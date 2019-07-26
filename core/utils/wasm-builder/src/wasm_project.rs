// Copyright 2019 Parity Technologies (UK) Ltd.
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

use std::{fs, path::{Path, PathBuf}, borrow::ToOwned, process::{Command, self}, env};

use toml::value::Table;

use build_helper::rerun_if_changed;

use cargo_metadata::MetadataCommand;

use walkdir::WalkDir;

use fs2::FileExt;

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
pub fn create_and_compile(cargo_manifest: &Path) -> (WasmBinary, WasmBinaryBloaty)  {
	let wasm_workspace_root = get_wasm_workspace_root();
	let wasm_workspace = wasm_workspace_root.join("wbuild");

	// Lock the workspace exclusively for us
	let _lock = WorkspaceLock::new(&wasm_workspace_root);

	let project = create_project(cargo_manifest, &wasm_workspace);
	create_wasm_workspace_project(&wasm_workspace);

	build_project(&project);
	let (wasm_binary, bloaty) = compact_wasm_file(&project, cargo_manifest, &wasm_workspace);

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

fn create_wasm_workspace_project(wasm_workspace: &Path) {
	let members = WalkDir::new(wasm_workspace)
		.min_depth(1)
		.max_depth(1)
		.into_iter()
		.filter_map(|p| p.ok())
		.map(|d| d.into_path())
		.filter(|p| p.is_dir() && !p.ends_with("target"))
		.filter_map(|p| p.file_name().map(|f| f.to_owned()).and_then(|s| s.into_string().ok()))
		.map(|s| format!("\"{}\", ", s))
		.collect::<String>();

	fs::write(
		wasm_workspace.join("Cargo.toml"),
		format!(
			r#"
				[profile.release]
				panic = "abort"
				lto = true

				[profile.dev]
				panic = "abort"

				[workspace]
				members = [ {members} ]
			"#,
			members = members,
		)
	).expect("WASM workspace `Cargo.toml` writing can not fail; qed");
}

/// Create the project used to build the wasm binary.
///
/// # Returns
/// The path to the created project.
fn create_project(cargo_manifest: &Path, wasm_workspace: &Path) -> PathBuf {
	let crate_name = get_crate_name(cargo_manifest);
	let crate_path = cargo_manifest.parent().expect("Parent path exists; qed");
	let wasm_binary = get_wasm_binary_name(cargo_manifest);
	let project_folder = wasm_workspace.join(&crate_name);

	fs::create_dir_all(project_folder.join("src")).expect("Wasm project dir create can not fail; qed");

	fs::write(
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
				wasm_project = {{ package = "{crate_name}", path = "{crate_path}", default-features = false, features = [ "no_std" ] }}
			"#,
			crate_name = crate_name,
			crate_path = crate_path.display(),
			wasm_binary = wasm_binary,
		)
	).expect("Project `Cargo.toml` writing can not fail; qed");

	fs::write(
		project_folder.join("src/lib.rs"),
		"#![no_std] pub use wasm_project::*;",
	).expect("Project `lib.rs` writing can not fail; qed");

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
		!build_helper::debug()
	}
}

/// Build the project to create the WASM binary.
fn build_project(project: &Path) {
	let manifest_path = project.join("Cargo.toml");
	let mut build_cmd = crate::get_nightly_cargo().command();

	let rustflags = format!(
		"-C link-arg=--export-table {}",
		env::var(crate::WASM_BUILD_RUSTFLAGS_ENV).unwrap_or_default(),
	);

	build_cmd.args(&["build", "--target=wasm32-unknown-unknown"])
		.arg(format!("--manifest-path={}", manifest_path.display()))
		.env("RUSTFLAGS", rustflags)
		// We don't want to call ourselves recursively
		.env(crate::SKIP_BUILD_ENV, "");

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

	let res = Command::new("wasm-gc")
		.arg(&wasm_file)
		.arg(&wasm_compact_file)
		.status()
		.map(|s| s.success());

	if !res.unwrap_or(false) {
		panic!("Failed to compact generated WASM binary.");
	}

	(WasmBinary(wasm_compact_file), WasmBinaryBloaty(wasm_file))
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

	// Make sure that if any file/folder of a depedency change, we need to rerun the `build.rs`
	metadata.packages.into_iter()
		.filter(|package| !package.manifest_path.starts_with(wasm_workspace))
		.for_each(|package| {
			let mut manifest_path = package.manifest_path;
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
}
