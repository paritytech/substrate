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

use std::{fs, path::{Path, PathBuf}, borrow::ToOwned, process::Command, env};

use toml::value::Table;

use build_helper::rerun_if_changed;

use cargo_metadata::MetadataCommand;

use walkdir::WalkDir;

/// The name for the wasm binary.
const WASM_BINARY: &str = "wasm_binary";

/// Holds the path to the bloaty WASM binary.
pub struct WasmBinaryBloaty(PathBuf);

impl WasmBinaryBloaty {
	/// Returns the path to the bloaty wasm binary.
	pub fn wasm_binary_bloaty_path(&self) -> &Path {
		&self.0
	}
}

/// Holds the path to the WASM binary.
pub struct WasmBinary(PathBuf);

impl WasmBinary {
	/// Returns the path to the wasm binary.
	pub fn wasm_binary_path(&self) -> &Path {
		&self.0
	}
}

/// Creates the WASM project, compiles the WASM binary and compacts the WASM binary.
///
/// # Returns
/// The path to the compact WASM binary and the bloaty WASM binary.
pub fn create_and_compile(cargo_manifest: &Path) -> (WasmBinary, WasmBinaryBloaty)  {
	let project = create_project(cargo_manifest);

	build_project(&project);
	let bloaty = WasmBinaryBloaty(compact_wasm_file(&project));
	let wasm_binary = WasmBinary(project.join(format!("{}.compact.wasm", WASM_BINARY)));

	generate_rerun_if_changed_instructions(cargo_manifest, &project);

	(wasm_binary, bloaty)
}

/// Find the `Cargo.lock` relative to the `OUT_DIR` environment variable.
///
/// If the `Cargo.lock` can not be found, we emit a warning and return `None`.
fn find_cargo_lock(cargo_manifest: &Path) -> Option<PathBuf> {
	let mut path = build_helper::out_dir();

	while path.pop() {
		if path.join("Cargo.lock").exists() {
			return Some(path.join("Cargo.lock"))
		}
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

/// Create the project used to build the wasm binary.
///
/// # Returns
/// The path to the created project.
fn create_project(cargo_manifest: &Path) -> PathBuf {
	let crate_name = get_crate_name(cargo_manifest);
	let crate_path = cargo_manifest.parent().expect("Parent path exists; qed");
	let project_folder = build_helper::out_dir().join(format!("{}_wasm_project", crate_name));

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

				[profile.release]
				panic = "abort"
				lto = true

				[profile.dev]
				panic = "abort"

				[workspace]
			"#,
			crate_name = crate_name,
			crate_path = crate_path.display(),
			wasm_binary = WASM_BINARY,
		)
	).expect("Project `Cargo.toml` writing can not fail; qed");

	fs::write(
		project_folder.join("src/lib.rs"),
		format!(
			r#"
				#![no_std]
				pub use wasm_project::*;
			"#
		)
	).expect("Project `lib.rs` writing can not fail; qed");

	if let Some(crate_lock_file) = find_cargo_lock(cargo_manifest) {
		// Use the `Cargo.lock` of the main project.
		fs::copy(crate_lock_file, project_folder.join("Cargo.lock"))
			.expect("Copying the `Cargo.lock` can not fail; qed");
	}

	project_folder
}

/// Returns if the project should be build a release.
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
	let mut build_cmd = crate::get_nightly_cargo();
	build_cmd.args(&["build", "--target=wasm32-unknown-unknown"])
		.arg(format!("--manifest-path={}", manifest_path.display()))
		.env("RUSTFLAGS", "-C link-arg=--export-table")
		// We don't want to call ourselves recursively
		.env(crate::SKIP_BUILD_ENV, "");

	if is_release_build() {
		build_cmd.arg("--release");
	};

	println!("Executing build command: {:?}", build_cmd);

	match build_cmd.status().map(|s| s.success()) {
		Ok(true) => {},
		_ => panic!("Failed to compile WASM binary"),
	}
}

/// Compact the WASM binary using `wasm-gc` and returns the path to the bloaty WASM binary.
fn compact_wasm_file(project: &Path) -> PathBuf {
	let target = if is_release_build() { "release" } else { "debug" };
	let wasm_file = project.join("target/wasm32-unknown-unknown")
		.join(target)
		.join(format!("{}.wasm", WASM_BINARY));

	let res = Command::new("wasm-gc").arg(&wasm_file)
		.arg(project.join(format!("{}.compact.wasm", WASM_BINARY)))
		.status()
		.map(|s| s.success());

	match res {
		Ok(true) => {},
		_ => panic!("Failed to compact generated WASM binary."),
	}

	wasm_file
}

/// Generate the `rerun-if-changed` instructions for cargo to make sure that the WASM binary is
/// rebuild when needed.
fn generate_rerun_if_changed_instructions(cargo_manifest: &Path, project_folder: &Path) {
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
		.filter(|package| !package.manifest_path.starts_with(project_folder))
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
}
