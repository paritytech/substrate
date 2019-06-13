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

//! WASM builder runner
//!
//! As cargo just contains millions of bugs, when it comes to correct dependency and feature
//! resolution, we need this little tool. See https://github.com/rust-lang/cargo/issues/5730 for
//! more information.
//!
//! It will create a project that itself will call `wasm-builder` to not let any dependencies
//! from `wasm-builder` to influence the main project dependencies...

use std::{env, process::Command, fs, path::{PathBuf, Path}};

/// Environment variable that tells us to skip building the WASM binary.
const SKIP_BUILD_ENV: &str = "SKIP_WASM_BUILD";

/// Build the currently build project as WASM binary.
///
/// The current project is determined by using the `CARGO_MANIFEST_DIR` environment variable.
///
/// `file_name` - The name of the file being generated in the `OUT_DIR`. The file contains the
///               constant `WASM_BINARY` which contains the build wasm binary.
/// `wasm_builder_path` - Path to the wasm-builder project, relative to `CARGO_MANIFEST_DIR`.
pub fn build_current_project(file_name: &str, wasm_builder_path: &str) {
	if check_skip_build() {
		return;
	}

	let manifest_dir = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR").expect(
			"`CARGO_MANIFEST_DIR` is always set for `build.rs` files; qed"
		)
	);

	let wasm_builder_path = manifest_dir.join(wasm_builder_path);
	let manifest_dir = manifest_dir.join("Cargo.toml");
	let out_dir = PathBuf::from(env::var("OUT_DIR").expect("`OUT_DIR` is set by cargo!"));
	let file_path = out_dir.join(file_name);
	let project_folder = out_dir.join("wasm_build_runner");

	create_project(&project_folder, &file_path, &wasm_builder_path, &manifest_dir);
	run_project(&project_folder);
}

fn create_project(
	project_folder: &Path,
	file_path: &Path,
	wasm_builder_path: &Path,
	manifest_dir: &Path,
) {
	fs::create_dir_all(project_folder.join("src"))
		.expect("WASM build runner dir create can not fail; qed");

	fs::write(
		project_folder.join("Cargo.toml"),
		format!(
			r#"
				[package]
				name = "wasm-build-runner"
				version = "1.0.0"
				edition = "2018"

				[dependencies]
				wasm-builder = {{ path = "{crate_path}" }}

				[workspace]
			"#,
			crate_path = wasm_builder_path.display(),
		)
	).expect("WASM build runner `Cargo.toml` writing can not fail; qed");

	fs::write(
		project_folder.join("src/main.rs"),
		format!(
			r#"
				fn main() {{
					wasm_builder::build_project("{file_path}", "{manifest_dir}")
				}}
			"#,
			file_path = file_path.display(),
			manifest_dir = manifest_dir.display(),
		)
	).expect("WASM build runner `main.rs` writing can not fail; qed");
}

fn run_project(project_folder: &Path) {
	let mut cmd = Command::new("cargo");
	cmd.arg("run").arg(format!("--manifest-path={}", project_folder.join("Cargo.toml").display()));

	if env::var("DEBUG") != Ok(String::from("true")) {
		cmd.arg("--release");
	}

	match cmd.status().map(|s| s.success()) {
		Ok(true) => {},
		_ => panic!("Running WASM build runner failed!"),
	}
}

/// Checks if the build of the WASM binary should be skipped.
fn check_skip_build() -> bool {
	env::var(SKIP_BUILD_ENV).is_ok()
}