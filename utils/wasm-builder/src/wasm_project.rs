// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use crate::write_file_if_changed;

use std::{
	fs, path::{Path, PathBuf}, borrow::ToOwned, process, env, collections::HashSet,
	hash::{Hash, Hasher}, ops::Deref,
};

use toml::value::Table;

use build_helper::rerun_if_changed;

use cargo_metadata::MetadataCommand;

use walkdir::WalkDir;

use fs2::FileExt;

use itertools::Itertools;

/// Holds the path to the bloaty WASM binary.
pub struct WasmBinaryBloaty(PathBuf);

impl WasmBinaryBloaty {
	/// Returns the path to the bloaty wasm binary.
	pub fn wasm_binary_bloaty_path(&self) -> String {
		self.0.display().to_string().replace('\\', "/")
	}
}

/// Holds the path to the WASM binary.
pub struct WasmBinary(PathBuf);

impl WasmBinary {
	/// Returns the path to the wasm binary.
	pub fn wasm_binary_path(&self) -> String {
		self.0.display().to_string().replace('\\', "/")
	}
}

/// A lock for the WASM workspace.
struct WorkspaceLock(fs::File);

impl WorkspaceLock {
	/// Create a new lock
	fn new(wasm_workspace_root: &Path) -> Self {
		let lock = fs::OpenOptions::new()
			.read(true)
			.write(true)
			.create(true)
			.open(wasm_workspace_root.join("wasm_workspace.lock"))
			.expect("Opening the lock file does not fail");

		lock.lock_exclusive().expect("Locking `wasm_workspace.lock` failed");

		WorkspaceLock(lock)
	}
}

impl Drop for WorkspaceLock {
	fn drop(&mut self) {
		let _ = self.0.unlock();
	}
}

/// Creates the WASM project, compiles the WASM binary and compacts the WASM binary.
///
/// # Returns
/// The path to the compact WASM binary and the bloaty WASM binary.
pub fn create_and_compile(
	cargo_manifest: &Path,
	default_rustflags: &str,
) -> (WasmBinary, WasmBinaryBloaty) {
	let wasm_workspace_root = get_wasm_workspace_root();
	let wasm_workspace = wasm_workspace_root.join("wbuild");

	// Lock the workspace exclusively for us
	let _lock = WorkspaceLock::new(&wasm_workspace_root);

	let crate_metadata = MetadataCommand::new()
		.manifest_path(cargo_manifest)
		.exec()
		.expect("`cargo metadata` can not fail on project `Cargo.toml`; qed");

	let project = create_project(cargo_manifest, &wasm_workspace, &crate_metadata);
	create_wasm_workspace_project(&wasm_workspace, &crate_metadata.workspace_root);

	build_project(&project, default_rustflags);
	let (wasm_binary, bloaty) = compact_wasm_file(
		&project,
		cargo_manifest,
		&wasm_workspace,
	);

	copy_wasm_to_target_directory(cargo_manifest, &wasm_binary);

	generate_rerun_if_changed_instructions(cargo_manifest, &project, &wasm_workspace);

	(wasm_binary, bloaty)
}

/// Find the `Cargo.lock` relative to the `OUT_DIR` environment variable.
///
/// If the `Cargo.lock` cannot be found, we emit a warning and return `None`.
fn find_cargo_lock(cargo_manifest: &Path) -> Option<PathBuf> {
	fn find_impl(mut path: PathBuf) -> Option<PathBuf> {
		loop {
			if path.join("Cargo.lock").exists() {
				return Some(path.join("Cargo.lock"))
			}

			if !path.pop() {
				return None;
			}
		}
	}

	if let Some(path) = find_impl(build_helper::out_dir()) {
		return Some(path);
	}

	if let Some(path) = find_impl(cargo_manifest.to_path_buf()) {
		return Some(path);
	}

	build_helper::warning!(
		"Could not find `Cargo.lock` for `{}`, while searching from `{}`.",
		cargo_manifest.display(),
		build_helper::out_dir().display()
	);

	None
}

/// Extract the crate name from the given `Cargo.toml`.
fn get_crate_name(cargo_manifest: &Path) -> String {
	let cargo_toml: Table = toml::from_str(
		&fs::read_to_string(cargo_manifest).expect("File exists as checked before; qed")
	).expect("Cargo manifest is a valid toml file; qed");

	let package = cargo_toml
		.get("package")
		.and_then(|t| t.as_table())
		.expect("`package` key exists in valid `Cargo.toml`; qed");

	package.get("name").and_then(|p| p.as_str()).map(ToOwned::to_owned).expect("Package name exists; qed")
}

/// Returns the name for the wasm binary.
fn get_wasm_binary_name(cargo_manifest: &Path) -> String {
	get_crate_name(cargo_manifest).replace('-', "_")
}

/// Returns the root path of the wasm workspace.
fn get_wasm_workspace_root() -> PathBuf {
	let mut out_dir = build_helper::out_dir();

	loop {
		match out_dir.parent() {
			Some(parent) if out_dir.ends_with("build") => return parent.to_path_buf(),
			_ => if !out_dir.pop() {
				break;
			}
		}
	}

	panic!("Could not find target dir in: {}", build_helper::out_dir().display())
}

/// Find all workspace members.
///
/// Each folder in `wasm_workspace` is seen as a member of the workspace. Exceptions are
/// folders starting with "." and the "target" folder.
///
/// Every workspace member that is not valid anymore is deleted (the folder of it). A
/// member is not valid anymore when the `wasm-project` dependency points to an non-existing
/// folder or the package name is not valid.
fn find_and_clear_workspace_members(wasm_workspace: &Path) -> Vec<String> {
	let mut members = WalkDir::new(wasm_workspace)
		.min_depth(1)
		.max_depth(1)
		.into_iter()
		.filter_map(|p| p.ok())
		.map(|d| d.into_path())
		.filter(|p| p.is_dir())
		.filter_map(|p| p.file_name().map(|f| f.to_owned()).and_then(|s| s.into_string().ok()))
		.filter(|f| !f.starts_with(".") && f != "target")
		.collect::<Vec<_>>();

	let mut i = 0;
	while i != members.len() {
		let path = wasm_workspace.join(&members[i]).join("Cargo.toml");

		// Extract the `wasm-project` dependency.
		// If the path can be extracted and is valid and the package name matches,
		// the member is valid.
		if let Some(mut wasm_project) = fs::read_to_string(path)
			.ok()
			.and_then(|s| toml::from_str::<Table>(&s).ok())
			.and_then(|mut t| t.remove("dependencies"))
			.and_then(|p| p.try_into::<Table>().ok())
			.and_then(|mut t| t.remove("wasm_project"))
			.and_then(|p| p.try_into::<Table>().ok())
		{
			if let Some(path) = wasm_project.remove("path")
				.and_then(|p| p.try_into::<String>().ok())
			{
				if let Some(name) = wasm_project.remove("package")
					.and_then(|p| p.try_into::<String>().ok())
				{
					let path = PathBuf::from(path);
					if path.exists() {
						if name == get_crate_name(&path.join("Cargo.toml")) {
							i += 1;
							continue
						}
					}
				}
			}
		}

		fs::remove_dir_all(wasm_workspace.join(&members[i]))
			.expect("Removing invalid workspace member can not fail; qed");
		members.remove(i);
	}

	members
}

fn create_wasm_workspace_project(wasm_workspace: &Path, workspace_root_path: &Path) {
	let members = find_and_clear_workspace_members(wasm_workspace);

	let mut workspace_toml: Table = toml::from_str(
		&fs::read_to_string(
			workspace_root_path.join("Cargo.toml"),
		).expect("Workspace root `Cargo.toml` exists; qed")
	).expect("Workspace root `Cargo.toml` is a valid toml file; qed");

	let mut wasm_workspace_toml = Table::new();

	// Add `profile` with release and dev
	let mut release_profile = Table::new();
	release_profile.insert("panic".into(), "abort".into());
	release_profile.insert("lto".into(), true.into());

	let mut dev_profile = Table::new();
	dev_profile.insert("panic".into(), "abort".into());

	let mut profile = Table::new();
	profile.insert("release".into(), release_profile.into());
	profile.insert("dev".into(), dev_profile.into());

	wasm_workspace_toml.insert("profile".into(), profile.into());

	// Add `workspace` with members
	let mut workspace = Table::new();
	workspace.insert("members".into(), members.into());

	wasm_workspace_toml.insert("workspace".into(), workspace.into());

	// Add patch section from the project root `Cargo.toml`
	if let Some(mut patch) = workspace_toml.remove("patch").and_then(|p| p.try_into::<Table>().ok()) {
		// Iterate over all patches and make the patch path absolute from the workspace root path.
		patch.iter_mut()
			.filter_map(|p|
				p.1.as_table_mut().map(|t| t.iter_mut().filter_map(|t| t.1.as_table_mut()))
			)
			.flatten()
			.for_each(|p|
				p.iter_mut()
					.filter(|(k, _)| k == &"path")
					.for_each(|(_, v)| {
						if let Some(path) = v.as_str().map(PathBuf::from) {
							if path.is_relative() {
								*v = workspace_root_path.join(path).display().to_string().into();
							}
						}
					})
			);

		wasm_workspace_toml.insert("patch".into(), patch.into());
	}

	fs::write(
		wasm_workspace.join("Cargo.toml"),
		toml::to_string_pretty(&wasm_workspace_toml).expect("Wasm workspace toml is valid; qed"),
	).expect("WASM workspace `Cargo.toml` writing can not fail; qed");
}

/// Get a list of enabled features for the project.
fn project_enabled_features(
	cargo_manifest: &Path,
	crate_metadata: &cargo_metadata::Metadata,
) -> Vec<String> {
	let package = crate_metadata.packages
		.iter()
		.find(|p| p.manifest_path == cargo_manifest)
		.expect("Wasm project exists in its own metadata; qed");

	let mut enabled_features = package.features.keys()
		.filter(|f| {
			let mut feature_env = f.replace("-", "_");
			feature_env.make_ascii_uppercase();

			// We don't want to enable the `std`/`default` feature for the wasm build and
			// we need to check if the feature is enabled by checking the env variable.
			*f != "std"
				&& *f != "default"
				&& env::var(format!("CARGO_FEATURE_{}", feature_env))
					.map(|v| v == "1")
					.unwrap_or_default()
		})
		.cloned()
		.collect::<Vec<_>>();

	enabled_features.sort();
	enabled_features
}

/// Create the project used to build the wasm binary.
///
/// # Returns
/// The path to the created project.
fn create_project(
	cargo_manifest: &Path,
	wasm_workspace: &Path,
	crate_metadata: &cargo_metadata::Metadata,
) -> PathBuf {
	let crate_name = get_crate_name(cargo_manifest);
	let crate_path = cargo_manifest.parent().expect("Parent path exists; qed");
	let wasm_binary = get_wasm_binary_name(cargo_manifest);
	let project_folder = wasm_workspace.join(&crate_name);

	fs::create_dir_all(project_folder.join("src")).expect("Wasm project dir create can not fail; qed");

	let enabled_features = project_enabled_features(&cargo_manifest, &crate_metadata);

	write_file_if_changed(
		project_folder.join("Cargo.toml"),
		format!(
			r#"
				[package]
				name = "{crate_name}-wasm"
				version = "1.0.0"
				edition = "2018"

				[lib]
				name = "{wasm_binary}"
				crate-type = ["cdylib"]

				[dependencies]
				wasm_project = {{ package = "{crate_name}", path = "{crate_path}", default-features = false, features = [ {features} ] }}
			"#,
			crate_name = crate_name,
			crate_path = crate_path.display(),
			wasm_binary = wasm_binary,
			features = enabled_features.into_iter().map(|f| format!("\"{}\"", f)).join(","),
		)
	);

	write_file_if_changed(
		project_folder.join("src/lib.rs"),
		"#![no_std] pub use wasm_project::*;".into(),
	);

	if let Some(crate_lock_file) = find_cargo_lock(cargo_manifest) {
		// Use the `Cargo.lock` of the main project.
		fs::copy(crate_lock_file, wasm_workspace.join("Cargo.lock"))
			.expect("Copying the `Cargo.lock` can not fail; qed");
	}

	project_folder
}

/// Returns if the project should be built as a release.
fn is_release_build() -> bool {
	if let Ok(var) = env::var(crate::WASM_BUILD_TYPE_ENV) {
		match var.as_str() {
			"release" => true,
			"debug" => false,
			var => panic!(
				"Unexpected value for `{}` env variable: {}\nOne of the following are expected: `debug` or `release`.",
				crate::WASM_BUILD_TYPE_ENV,
				var,
			),
		}
	} else {
		true
	}
}

/// Build the project to create the WASM binary.
fn build_project(project: &Path, default_rustflags: &str) {
	let manifest_path = project.join("Cargo.toml");
	let mut build_cmd = crate::get_nightly_cargo().command();

	let rustflags = format!(
		"-C link-arg=--export-table {} {}",
		default_rustflags,
		env::var(crate::WASM_BUILD_RUSTFLAGS_ENV).unwrap_or_default(),
	);

	build_cmd.args(&["rustc", "--target=wasm32-unknown-unknown"])
		.arg(format!("--manifest-path={}", manifest_path.display()))
		.env("RUSTFLAGS", rustflags)
		// We don't want to call ourselves recursively
		.env(crate::SKIP_BUILD_ENV, "");

	if env::var(crate::WASM_BUILD_NO_COLOR).is_err() {
		build_cmd.arg("--color=always");
	}

	if is_release_build() {
		build_cmd.arg("--release");
	};

	println!("Executing build command: {:?}", build_cmd);

	match build_cmd.status().map(|s| s.success()) {
		Ok(true) => {},
		// Use `process.exit(1)` to have a clean error output.
		_ => process::exit(1),
	}
}

/// Compact the WASM binary using `wasm-gc`. Returns the path to the bloaty WASM binary.
fn compact_wasm_file(
	project: &Path,
	cargo_manifest: &Path,
	wasm_workspace: &Path,
) -> (WasmBinary, WasmBinaryBloaty) {
	let target = if is_release_build() { "release" } else { "debug" };
	let wasm_binary = get_wasm_binary_name(cargo_manifest);
	let wasm_file = wasm_workspace.join("target/wasm32-unknown-unknown")
		.join(target)
		.join(format!("{}.wasm", wasm_binary));
	let wasm_compact_file = project.join(format!("{}.compact.wasm", wasm_binary));

	wasm_gc::garbage_collect_file(&wasm_file, &wasm_compact_file)
		.expect("Failed to compact generated WASM binary.");

	(WasmBinary(wasm_compact_file), WasmBinaryBloaty(wasm_file))
}

/// Custom wrapper for a [`cargo_metadata::Package`] to store it in
/// a `HashSet`.
#[derive(Debug)]
struct DeduplicatePackage<'a> {
	package: &'a cargo_metadata::Package,
	identifier: String,
}

impl<'a> From<&'a cargo_metadata::Package> for DeduplicatePackage<'a> {
	fn from(package: &'a cargo_metadata::Package) -> Self {
		Self {
			package,
			identifier: format!("{}{}{:?}", package.name, package.version, package.source),
		}
	}
}

impl<'a> Hash for DeduplicatePackage<'a> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.identifier.hash(state);
	}
}

impl<'a> PartialEq for DeduplicatePackage<'a> {
	fn eq(&self, other: &Self) -> bool {
		self.identifier == other.identifier
	}
}

impl<'a> Eq for DeduplicatePackage<'a> {}

impl<'a> Deref for DeduplicatePackage<'a> {
	type Target = cargo_metadata::Package;

	fn deref(&self) -> &Self::Target {
		self.package
	}
}

/// Generate the `rerun-if-changed` instructions for cargo to make sure that the WASM binary is
/// rebuilt when needed.
fn generate_rerun_if_changed_instructions(
	cargo_manifest: &Path,
	project_folder: &Path,
	wasm_workspace: &Path,
) {
	// Rerun `build.rs` if the `Cargo.lock` changes
	if let Some(cargo_lock) = find_cargo_lock(cargo_manifest) {
		rerun_if_changed(cargo_lock);
	}

	let metadata = MetadataCommand::new()
		.manifest_path(project_folder.join("Cargo.toml"))
		.exec()
		.expect("`cargo metadata` can not fail!");

	// Start with the dependencies of the crate we want to compile for wasm.
	let mut dependencies = metadata.packages
		.iter()
		.find(|p| p.manifest_path == cargo_manifest)
		.expect("The crate package is contained in its own metadata; qed")
		.dependencies
		.iter()
		.collect::<Vec<_>>();

	// Collect all packages by follow the dependencies of all packages we find.
	let mut packages = HashSet::new();
	while let Some(dependency) = dependencies.pop() {
		let package = metadata.packages
			.iter()
			.filter(|p| !p.manifest_path.starts_with(wasm_workspace))
			.find(|p| dependency.req.matches(&p.version) && dependency.name == p.name);

		if let Some(package) = package {
			if packages.insert(DeduplicatePackage::from(package)) {
				dependencies.extend(package.dependencies.iter());
			}
		}
	}

	// Make sure that if any file/folder of a dependency change, we need to rerun the `build.rs`
	packages.into_iter()
		.filter(|p| !p.manifest_path.starts_with(wasm_workspace))
		.for_each(|package| {
			let mut manifest_path = package.manifest_path.clone();
			if manifest_path.ends_with("Cargo.toml") {
				manifest_path.pop();
			}

			rerun_if_changed(&manifest_path);

			WalkDir::new(manifest_path)
				.into_iter()
				.filter_map(|p| p.ok())
				.for_each(|p| rerun_if_changed(p.path()));
		});

	// Register our env variables
	println!("cargo:rerun-if-env-changed={}", crate::SKIP_BUILD_ENV);
	println!("cargo:rerun-if-env-changed={}", crate::WASM_BUILD_TYPE_ENV);
	println!("cargo:rerun-if-env-changed={}", crate::WASM_BUILD_RUSTFLAGS_ENV);
	println!("cargo:rerun-if-env-changed={}", crate::WASM_TARGET_DIRECTORY);
	println!("cargo:rerun-if-env-changed={}", crate::WASM_BUILD_TOOLCHAIN);
}

/// Copy the WASM binary to the target directory set in `WASM_TARGET_DIRECTORY` environment variable.
/// If the variable is not set, this is a no-op.
fn copy_wasm_to_target_directory(cargo_manifest: &Path, wasm_binary: &WasmBinary) {
	let target_dir = match env::var(crate::WASM_TARGET_DIRECTORY) {
		Ok(path) => PathBuf::from(path),
		Err(_) => return,
	};

	if !target_dir.is_absolute() {
		panic!(
			"Environment variable `{}` with `{}` is not an absolute path!",
			crate::WASM_TARGET_DIRECTORY,
			target_dir.display(),
		);
	}

	fs::create_dir_all(&target_dir).expect("Creates `WASM_TARGET_DIRECTORY`.");

	fs::copy(
		wasm_binary.wasm_binary_path(),
		target_dir.join(format!("{}.wasm", get_wasm_binary_name(cargo_manifest))),
	).expect("Copies WASM binary to `WASM_TARGET_DIRECTORY`.");
}
