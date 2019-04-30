use structopt::StructOpt;

use std::{
	path::{PathBuf, Path}, collections::HashMap, fs::{File, self}, io::{Read, Write},
	process::Command
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

#[derive(StructOpt)]
struct Options {
	/// The path to the `node-template` source.
	#[structopt(parse(from_os_str))]
	node_template: PathBuf,
	/// The path where to output the generated `tar.gz` file.
	#[structopt(parse(from_os_str))]
	output: PathBuf,
}

/// Find all `Cargo.toml` files in the given path.
fn find_cargo_tomls(path: PathBuf) -> Vec<PathBuf> {
	let path = format!("{}/**/*.toml", path.display());

	let glob = glob::glob(&path).expect("Generates globbing pattern");

	let mut result = Vec::new();
	glob.into_iter().for_each(|file| {
		match file {
			Ok(file) => result.push(file),
			Err(e) => println!("{:?}", e),
		}
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
	File::open(file).expect("Cargo.toml exists").read_to_string(&mut content).expect("Reads file");
	toml::from_str(&content).expect("Cargo.toml is a valid toml file")
}

/// Replaces all substrate path dependencies with a git dependency.
fn replace_path_dependencies_with_git(cargo_toml_path: &Path, commit_id: &str, cargo_toml: &mut CargoToml) {
	let mut cargo_toml_path = cargo_toml_path.to_path_buf();
	// remove `Cargo.toml`
	cargo_toml_path.pop();

	let mut dependencies: toml::value::Table = match cargo_toml
		.remove("dependencies")
		.and_then(|v| v.try_into().ok()) {
		Some(deps) => deps,
		None => return,
	};

	let deps_rewritten = dependencies
		.iter()
		.filter_map(|(k, v)| v.clone().try_into::<toml::value::Table>().ok().map(move |v| (k, v)))
		.filter(|t| t.1.contains_key("path"))
		.filter(|t| {
			// if the path does not exists, we need to add this as git dependency
			t.1.get("path").unwrap().as_str().map(|path| !cargo_toml_path.join(path).exists()).unwrap_or(false)
		})
		.map(|(k, mut v)| {
			// remove `path` and add `git` and `rev`
			v.remove("path");
			v.insert("git".into(), SUBSTRATE_GIT_URL.into());
			v.insert("rev".into(), commit_id.into());

			(k.clone(), v.into())
		}).collect::<HashMap<_, _>>();

	dependencies.extend(deps_rewritten.into_iter());

	cargo_toml.insert("dependencies".into(), dependencies.into());
}

/// Add `profile.release` = `panic = unwind` to the given `Cargo.toml`
fn cargo_toml_add_profile_release(cargo_toml: &mut CargoToml) {
	let mut panic_unwind = toml::value::Table::new();
	panic_unwind.insert("panic".into(), "unwind".into());

	let mut profile = toml::value::Table::new();
	profile.insert("release".into(), panic_unwind.into());

	cargo_toml.insert("profile".into(), profile.into());
}

fn write_cargo_toml(path: &Path, cargo_toml: CargoToml) {
	let content = toml::to_string_pretty(&cargo_toml).expect("Creates `Cargo.toml`");
	let mut file = File::create(path).expect(&format!("Creates `{}`.", path.display()));
	write!(file, "{}", content).expect("Writes `Cargo.toml`");
}

/// Build and test the generated node-template
fn build_and_test(path: &Path, cargo_tomls: &[PathBuf]) {
	// Build wasm
	assert!(Command::new(path.join("./scripts/build.sh")).current_dir(path).status().expect("Compiles wasm").success());

	// Build node
	assert!(Command::new("cargo").args(&["build", "--all"]).current_dir(path).status().expect("Compiles node").success());

	// Test node
	assert!(Command::new("cargo").args(&["test", "--all"]).current_dir(path).status().expect("Tests node").success());

	// Remove all `target` directories
	for toml in cargo_tomls {
		let mut target_path = toml.clone();
		target_path.pop();
		target_path = target_path.join("target");

		if target_path.exists() {
			fs::remove_dir_all(&target_path).expect(&format!("Removes `{}`", target_path.display()));
		}
	}
}

fn main() {
	let options = Options::from_args();

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
	let cargo_tomls = find_cargo_tomls(build_dir.path().to_owned());

	let commit_id = get_git_commit_id(&options.node_template);

	cargo_tomls.iter().for_each(|t| {
		let mut cargo_toml = parse_cargo_toml(&t);
		replace_path_dependencies_with_git(&t, &commit_id, &mut cargo_toml);

		// If this is the top-level `Cargo.toml`, add `profile.release`
		if &node_template_path.join("Cargo.toml") == t {
			cargo_toml_add_profile_release(&mut cargo_toml);
		}

		write_cargo_toml(&t, cargo_toml);
	});

	build_and_test(&node_template_path, &cargo_tomls);

	let output = GzEncoder::new(File::create(&options.output)
		.expect("Creates output file"), Compression::default());
	let mut tar = tar::Builder::new(output);
	tar.append_dir_all("substrate-node-template", node_template_path)
		.expect("Writes substrate-node-template archive");
}
