use std::{
	collections::HashMap,
	fs::{self, File, OpenOptions},
	path::{Path, PathBuf},
	process::Command,
};

use clap::Parser;
use flate2::{write::GzEncoder, Compression};
use fs_extra::dir::{self, CopyOptions};
use git2;
use glob;
use itertools::Itertools;
use tar;
use tempfile;
use toml_edit::{self, value, Array, Item, Table};

const SUBSTRATE_GIT_URL: &str = "https://github.com/paritytech/substrate.git";

type CargoToml = toml_edit::Document;

#[derive(Debug, PartialEq)]
struct Dependency {
	name: String,
	version: Option<String>,
	default_features: Option<bool>,
}

type Dependencies = HashMap<String, HashMap<String, Dependency>>;

#[derive(Parser)]
struct Options {
	/// The path to the `node-template` source.
	#[arg()]
	node_template: PathBuf,
	/// The path where to output the generated `tar.gz` file.
	#[arg()]
	output: PathBuf,
}

/// Copy the `node-template` to the given path.
fn copy_node_template(node_template: &Path, dest_path: &Path) {
	let options = CopyOptions::new();
	dir::copy(node_template, dest_path, &options).expect("Copies node-template to tmp dir");
}

/// Find all `Cargo.toml` files in the given path.
fn find_cargo_tomls(path: &PathBuf) -> Vec<PathBuf> {
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

/// Parse the given `Cargo.toml`.
fn parse_cargo_toml(file: &Path) -> CargoToml {
	fs::read_to_string(file)
		.unwrap_or_else(|e| panic!("Failed to read `{}`: {}", file.display(), e))
		.parse()
		.unwrap_or_else(|e| panic!("Failed to parse `{}`: {}", file.display(), e))
}

/// Write the given `Cargo.toml` to the given path.
fn write_cargo_toml(path: &Path, cargo_toml: CargoToml) {
	fs::write(path, cargo_toml.to_string())
		.unwrap_or_else(|e| panic!("Failed to write `{}`: {}", path.display(), e));
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

/// Rewrites git dependencies:
/// - inserts `workspace = true`;
/// - removes `path`;
/// - removes `version`;
/// - removes `default-features`
/// - and returns the dependencies that were rewritten.
fn update_git_dependencies<F: Copy + Fn(&str) -> bool>(
	cargo_toml: &mut CargoToml,
	path_filter: F,
) -> Dependencies {
	let process_dep = |dep: (toml_edit::KeyMut, &mut Item)| -> Option<Dependency> {
		let (key, value) = dep;
		value
			.as_table_like_mut()
			.filter(|dep| {
				dep.get("path").and_then(|path| path.as_str()).map(path_filter).unwrap_or(false)
			})
			.map(|dep| {
				dep.insert("workspace", toml_edit::value(true));
				dep.remove("path");

				Dependency {
					name: key.get().to_string(),
					version: dep
						.remove("version")
						.and_then(|version| version.as_str().map(|s| s.to_string())),
					default_features: dep.remove("default-features").and_then(|b| b.as_bool()),
				}
			})
	};

	["dependencies", "build-dependencies", "dev-dependencies"]
		.into_iter()
		.map(|table| -> (String, HashMap<String, Dependency>) {
			(
				table.to_string(),
				cargo_toml[table]
					.as_table_mut()
					.into_iter()
					.flat_map(|deps| deps.iter_mut().filter_map(process_dep))
					.map(|dep| (dep.name.clone(), dep))
					.collect(),
			)
		})
		.collect()
}

/// Processes all `Cargo.toml` files, aggregates dependencies and saves the changes.
fn process_cargo_tomls(cargo_tomls: &Vec<PathBuf>) -> Dependencies {
	/// Merge dependencies from one collection in another.
	fn merge_deps(into: &mut Dependencies, from: Dependencies) {
		from.into_iter().for_each(|(table, deps)| {
			into.entry(table).or_insert_with(HashMap::new).extend(deps);
		});
	}

	cargo_tomls.iter().fold(Dependencies::new(), |mut acc, path| {
		let mut cargo_toml = parse_cargo_toml(&path);

		let mut cargo_toml_path = path.clone();
		cargo_toml_path.pop(); // remove `Cargo.toml` from the path
		let deps = update_git_dependencies(&mut cargo_toml, |dep_path| {
			!cargo_toml_path.join(dep_path).exists()
		});

		write_cargo_toml(&path, cargo_toml);
		merge_deps(&mut acc, deps);
		acc
	})
}

/// Update the top level (workspace) `Cargo.toml` file.
///
/// - Adds `workspace` definition
/// - Adds dependencies
/// - Adds `profile.release` = `panic = unwind`
fn update_root_cargo_toml(
	cargo_toml: &mut CargoToml,
	members: &[String],
	deps: Dependencies,
	commit_id: &str,
) {
	let mut workspace = Table::new();
	workspace.insert("members", value(Array::from_iter(members.iter())));

	let mut workspace_dependencies = Table::new();
	deps.values()
		.flatten()
		.sorted_by_key(|(name, _)| *name)
		.for_each(|(name, dep)| {
			if let Some(version) = &dep.version {
				workspace_dependencies[name]["version"] = value(version);
			}
			if let Some(default_features) = dep.default_features {
				workspace_dependencies[name]["default-features"] = value(default_features);
			}
			workspace_dependencies[name]["git"] = value(SUBSTRATE_GIT_URL);
			workspace_dependencies[name]["rev"] = value(commit_id);
		});

	workspace.insert("dependencies", Item::Table(workspace_dependencies));
	cargo_toml.insert("workspace", Item::Table(workspace));

	let mut panic_unwind = Table::new();
	panic_unwind.insert("panic", value("unwind"));
	let mut profile = Table::new();
	profile.insert("release", Item::Table(panic_unwind));
	cargo_toml.insert("profile", Item::Table(profile.into()));
}

fn process_root_cargo_toml(
	root_cargo_toml_path: &Path,
	root_deps: Dependencies,
	cargo_tomls: &[PathBuf],
	node_template_path: &PathBuf,
	commit_id: &str,
) {
	let mut root_cargo_toml = parse_cargo_toml(root_cargo_toml_path);
	let workspace_members = cargo_tomls
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

	update_root_cargo_toml(&mut root_cargo_toml, &workspace_members, root_deps, commit_id);
	write_cargo_toml(&root_cargo_toml_path, root_cargo_toml);
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

	// Copy node-template to a temp build dir.
	let build_dir = tempfile::tempdir().expect("Creates temp build dir");
	let node_template_folder = options
		.node_template
		.canonicalize()
		.expect("Node template path exists")
		.file_name()
		.expect("Node template folder is last element of path")
		.to_owned();
	copy_node_template(&options.node_template, build_dir.path());

	// The path to the node-template in the build dir.
	let node_template_path = build_dir.path().join(node_template_folder);
	let root_cargo_toml_path = node_template_path.join("Cargo.toml");

	// Get all `Cargo.toml` files in the node-template
	let mut cargo_tomls = find_cargo_tomls(&node_template_path);

	// Check if top level Cargo.toml exists. If not, create one in the destination,
	// else remove it from the list, as this requires some special treatments.
	if let Some(index) = cargo_tomls.iter().position(|x| *x == root_cargo_toml_path) {
		cargo_tomls.remove(index);
	} else {
		OpenOptions::new()
			.create(true)
			.write(true)
			.open(root_cargo_toml_path.clone())
			.expect("Create root level `Cargo.toml` failed.");
	}

	// Process all `Cargo.toml` files.
	let root_deps = process_cargo_tomls(&cargo_tomls);
	process_root_cargo_toml(
		&root_cargo_toml_path,
		root_deps,
		&cargo_tomls,
		&node_template_path,
		&get_git_commit_id(&options.node_template),
	);

	// Add root rustfmt to node template build path.
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

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_update_git_dependencies() {
		let toml = r#"
[dev-dependencies]
scale-info = { version = "2.5.0", default-features = false, features = ["derive"] }

[dependencies]
scale-info = { version = "2.5.0", default-features = false, features = ["derive"] }
sp-io = { version = "7.0.0", path = "../../../../primitives/io" }
frame-system = { version = "4.0.0-dev", default-features = false, path = "../../../../frame/system" }
"#;
		let mut cargo_toml = toml.parse::<CargoToml>().expect("invalid doc");
		let actual_deps = update_git_dependencies(&mut cargo_toml, |_| true);

		assert_eq!(actual_deps.len(), 3);
		assert_eq!(actual_deps.get("dependencies").unwrap().len(), 2);
		assert_eq!(actual_deps.get("dev-dependencies").unwrap().len(), 0);
		assert_eq!(
			actual_deps.get("dependencies").unwrap().get("sp-io").unwrap(),
			&Dependency {
				name: "sp-io".into(),
				version: Some("7.0.0".into()),
				default_features: None
			}
		);
		assert_eq!(
			actual_deps.get("dependencies").unwrap().get("frame-system").unwrap(),
			&Dependency {
				name: "frame-system".into(),
				version: Some("4.0.0-dev".into()),
				default_features: Some(false),
			}
		);

		let expected_toml = r#"
[dev-dependencies]
scale-info = { version = "2.5.0", default-features = false, features = ["derive"] }

[dependencies]
scale-info = { version = "2.5.0", default-features = false, features = ["derive"] }
sp-io = { workspace = true }
frame-system = { workspace = true }
"#;
		assert_eq!(cargo_toml.to_string(), expected_toml);
	}

	#[test]
	fn test_update_root_cargo_toml() {
		let mut cargo_toml = CargoToml::new();
		update_root_cargo_toml(
			&mut cargo_toml,
			&vec!["node".into(), "pallets/template".into(), "runtime".into()],
			Dependencies::from([
				(
					"dependencies".into(),
					HashMap::from([
						(
							"sp-io".into(),
							Dependency {
								name: "sp-io".into(),
								version: Some("7.0.0".into()),
								default_features: None,
							},
						),
						(
							"frame-system".into(),
							Dependency {
								name: "frame-system".into(),
								version: Some("4.0.0-dev".into()),
								default_features: Some(true),
							},
						),
					]),
				),
				("dev-dependencies".into(), HashMap::new()),
				("build-dependencies".into(), HashMap::new()),
			]),
			"commit_id",
		);

		let expected_toml = r#"[workspace]
members = ["node", "pallets/template", "runtime"]

[workspace.dependencies]
frame-system = { version = "4.0.0-dev", default-features = true, git = "https://github.com/paritytech/substrate.git", rev = "commit_id" }
sp-io = { version = "7.0.0", git = "https://github.com/paritytech/substrate.git", rev = "commit_id" }

[profile]

[profile.release]
panic = "unwind"
"#;
		assert_eq!(cargo_toml.to_string(), expected_toml);
	}
}
