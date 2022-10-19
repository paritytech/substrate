use clap::Parser;

use std::{
	collections::HashMap,
	fs::{self, File, OpenOptions},
	io::{Read, Write},
	path::{Path, PathBuf},
	process::Command,
};

use glob;

use fs_extra::dir::{self, CopyOptions};

use tempfile;

use git2;

use toml;

use tar;

use flate2::{write::GzEncoder, Compression};

const SUBSTRATE_GIT_URL: &str = "https://github.com/paritytech/substrate.git";

type CargoToml = HashMap<String, toml::Value>;

#[derive(Parser)]
struct Options {
	/// The path to the `node-template` source.
	#[arg()]
	node_template: PathBuf,
	/// The path where to output the generated `tar.gz` file.
	#[arg()]
	output: PathBuf,
}

/// Find all `Cargo.toml` files in the given path.
fn find_cargo_tomls(path: PathBuf) -> Vec<PathBuf> {
	let path = format!("{}/**/*.toml", path.display());

	let glob = glob::glob(&path).expect("Generates globbing pattern");

	let mut result = Vec::new();
	glob.into_iter().for_each(|file| match file {
		Ok(file) => result.push(file),
		Err(e) => println!("{:?}", e),
	});

	if result.is_empty() {
		panic!("Did not found any `Cargo.toml` files.");
	}

	result
}

/// Copy the `node-template` to the given path.
fn copy_node_template(node_template: &Path, dest_path: &Path) {
	let options = CopyOptions::new();
	dir::copy(node_template, dest_path, &options).expect("Copies node-template to tmp dir");
}

/// Gets the latest commit id of the repository given by `path`.
fn get_git_commit_id(path: &Path) -> String {
	let repo = git2::Repository::discover(path)
		.expect(&format!("Node template ({}) should be in a git repository.", path.display()));

	let commit_id = repo
		.head()
		.expect("Repository should have a head")
		.peel_to_commit()
		.expect("Head references a commit")
		.id();

	format!("{}", commit_id)
}

/// Parse the given `Cargo.toml` into a `HashMap`
fn parse_cargo_toml(file: &Path) -> CargoToml {
	let mut content = String::new();
	File::open(file)
		.expect("Cargo.toml exists")
		.read_to_string(&mut content)
		.expect("Reads file");
	toml::from_str(&content).expect("Cargo.toml is a valid toml file")
}

/// Replaces all substrate path dependencies with a git dependency.
fn replace_path_dependencies_with_git(
	cargo_toml_path: &Path,
	commit_id: &str,
	cargo_toml: &mut CargoToml,
) {
	let mut cargo_toml_path = cargo_toml_path.to_path_buf();
	// remove `Cargo.toml`
	cargo_toml_path.pop();

	for &table in &["dependencies", "build-dependencies", "dev-dependencies"] {
		let mut dependencies: toml::value::Table =
			match cargo_toml.remove(table).and_then(|v| v.try_into().ok()) {
				Some(deps) => deps,
				None => continue,
			};

		let deps_rewritten = dependencies
			.iter()
			.filter_map(|(k, v)| {
				v.clone().try_into::<toml::value::Table>().ok().map(move |v| (k, v))
			})
			.filter(|t| {
				t.1.contains_key("path") && {
					// if the path does not exists, we need to add this as git dependency
					t.1.get("path")
						.unwrap()
						.as_str()
						.map(|path| !cargo_toml_path.join(path).exists())
						.unwrap_or(false)
				}
			})
			.map(|(k, mut v)| {
				// remove `path` and add `git` and `rev`
				v.remove("path");
				v.insert("git".into(), SUBSTRATE_GIT_URL.into());
				v.insert("rev".into(), commit_id.into());

				(k.clone(), v.into())
			})
			.collect::<HashMap<_, _>>();

		dependencies.extend(deps_rewritten.into_iter());

		cargo_toml.insert(table.into(), dependencies.into());
	}
}

/// Update the top level (workspace) `Cargo.toml` file.
///
/// - Adds `profile.release` = `panic = unwind`
/// - Adds `workspace` definition
fn update_top_level_cargo_toml(
	cargo_toml: &mut CargoToml,
	workspace_members: Vec<&PathBuf>,
	node_template_path: &Path,
) {
	let mut panic_unwind = toml::value::Table::new();
	panic_unwind.insert("panic".into(), "unwind".into());

	let mut profile = toml::value::Table::new();
	profile.insert("release".into(), panic_unwind.into());

	cargo_toml.insert("profile".into(), profile.into());

	let members = workspace_members
		.iter()
		.map(|p| {
			p.strip_prefix(node_template_path)
				.expect("Workspace member is a child of the node template path!")
				.parent()
				// We get the `Cargo.toml` paths as workspace members, but for the `members` field
				// we just need the path.
				.expect("The given path ends with `Cargo.toml` as file name!")
				.display()
				.to_string()
		})
		.collect::<Vec<_>>();

	let mut members_section = toml::value::Table::new();
	members_section.insert("members".into(), members.into());

	cargo_toml.insert("workspace".into(), members_section.into());
}

fn write_cargo_toml(path: &Path, cargo_toml: CargoToml) {
	let content = toml::to_string_pretty(&cargo_toml).expect("Creates `Cargo.toml`");
	let mut file = File::create(path).expect(&format!("Creates `{}`.", path.display()));
	write!(file, "{}", content).expect("Writes `Cargo.toml`");
}

/// Build and test the generated node-template
fn build_and_test(path: &Path, cargo_tomls: &[PathBuf]) {
	// Build node
	assert!(Command::new("cargo")
		.args(&["build", "--all"])
		.current_dir(path)
		.status()
		.expect("Compiles node")
		.success());

	// Test node
	assert!(Command::new("cargo")
		.args(&["test", "--all"])
		.current_dir(path)
		.status()
		.expect("Tests node")
		.success());

	// Remove all `target` directories
	for toml in cargo_tomls {
		let mut target_path = toml.clone();
		target_path.pop();
		target_path = target_path.join("target");

		if target_path.exists() {
			fs::remove_dir_all(&target_path)
				.expect(&format!("Removes `{}`", target_path.display()));
		}
	}
}

fn main() {
	let options = Options::parse();

	let build_dir = tempfile::tempdir().expect("Creates temp build dir");

	let node_template_folder = options
		.node_template
		.canonicalize()
		.expect("Node template path exists")
		.file_name()
		.expect("Node template folder is last element of path")
		.to_owned();

	// The path to the node-template in the build dir.
	let node_template_path = build_dir.path().join(node_template_folder);

	copy_node_template(&options.node_template, build_dir.path());
	let mut cargo_tomls = find_cargo_tomls(build_dir.path().to_owned());

	let commit_id = get_git_commit_id(&options.node_template);
	let top_level_cargo_toml_path = node_template_path.join("Cargo.toml");

	// Check if top level Cargo.toml exists. If not, create one in the destination
	if !cargo_tomls.contains(&top_level_cargo_toml_path) {
		// create the top_level_cargo_toml
		OpenOptions::new()
			.create(true)
			.write(true)
			.open(top_level_cargo_toml_path.clone())
			.expect("Create root level `Cargo.toml` failed.");

		// push into our data structure
		cargo_tomls.push(PathBuf::from(top_level_cargo_toml_path.clone()));
	}

	cargo_tomls.iter().for_each(|t| {
		let mut cargo_toml = parse_cargo_toml(&t);
		replace_path_dependencies_with_git(&t, &commit_id, &mut cargo_toml);

		// Check if this is the top level `Cargo.toml`, as this requires some special treatments.
		if top_level_cargo_toml_path == *t {
			// All workspace member `Cargo.toml` file paths.
			let workspace_members =
				cargo_tomls.iter().filter(|p| **p != top_level_cargo_toml_path).collect();

			update_top_level_cargo_toml(&mut cargo_toml, workspace_members, &node_template_path);
		}

		write_cargo_toml(&t, cargo_toml);
	});

	// adding root rustfmt to node template build path
	let node_template_rustfmt_toml_path = node_template_path.join("rustfmt.toml");
	let root_rustfmt_toml = &options.node_template.join("../../rustfmt.toml");
	if root_rustfmt_toml.exists() {
		fs::copy(&root_rustfmt_toml, &node_template_rustfmt_toml_path)
			.expect("Copying rustfmt.toml.");
	}

	build_and_test(&node_template_path, &cargo_tomls);

	let output = GzEncoder::new(
		File::create(&options.output).expect("Creates output file"),
		Compression::default(),
	);
	let mut tar = tar::Builder::new(output);
	tar.append_dir_all("substrate-node-template", node_template_path)
		.expect("Writes substrate-node-template archive");
}
