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

use std::{fs, path::{Path, PathBuf}, borrow::ToOwned, process::Command};

use toml::value::Table;

/// The name for the wasm binary.
const WASM_BINARY: &str = "wasm_binary";

/// Creates the WASM project, compiles the WASM binary and compacts the WASM binary.
///
/// # Returns
/// The path to the compact WASM binary.
pub fn create_and_compile(cargo_manifest: &Path) -> PathBuf {
	let project = create_project(cargo_manifest);

	build_project(&project);
	compact_wasm_file(&project);

	project.join(format!("{}.compact.wasm", WASM_BINARY))
}

/// Find the `Cargo.lock` relative to the `OUT_DIR`.
fn find_cargo_lock() -> PathBuf {
	let mut out_dir = build_helper::out_dir();

	while out_dir.pop() {
		if out_dir.join("Cargo.lock").exists() {
			return out_dir.join("Cargo.lock")
		}
	}

	panic!("Did not found `Cargo.lock` for out dir: {}", build_helper::out_dir().display())
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
	let crate_lock_file = find_cargo_lock();
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

	// Use the `Cargo.lock` of the main project.
	fs::copy(crate_lock_file, project_folder.join("Cargo.lock"))
		.expect("Copying the `Cargo.lock` can not fail; qed");

	project_folder
}

/// Build the project to create the WASM binary.
fn build_project(project: &Path) {
	let manifest_path = project.join("Cargo.toml");
	let mut build_cmd = Command::new(build_helper::bin::cargo());
	build_cmd.args(&["build", "--target=wasm32-unknown-unknown"])
		.arg(format!("--manifest-path={}", manifest_path.display()))
		.env("RUSTFLAGS", "-C link-arg=--export-table")
		// We don't want to calling us recursively
		.env(crate::SKIP_BUILD_ENV, "");

	if !build_helper::debug() {
		build_cmd.arg("--release");
	};

	println!("Executing build command: {:?}", build_cmd);

	match build_cmd.status().map(|s| s.success()) {
		Ok(true) => {},
		_ => panic!("Failed to compile WASM binary"),
	}
}

/// Compact the WASM binary using `wasm-gc`.
fn compact_wasm_file(project: &Path) {
	let target = if build_helper::debug() { "debug" } else { "release" };
	let wasm_file = project.join("target/wasm32-unknown-unknown")
		.join(target)
		.join(format!("{}.wasm", WASM_BINARY));

	let res = Command::new("wasm-gc").arg(wasm_file)
		.arg(project.join(format!("{}.compact.wasm", WASM_BINARY)))
		.status()
		.map(|s| s.success());

	match res {
		Ok(true) => {},
		_ => panic!("Failed to compact generated WASM binary."),
	}
}