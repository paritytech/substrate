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

use std::{process::{Command, Stdio}, fs};

use tempfile::tempdir;

/// Checks that all prerequisites are installed.
///
/// # Returns
/// Returns `None` if everything was found and `Some(ERR_MSG)` if something could not be found.
pub fn check() -> Option<&'static str> {
	if !check_nightly_installed() {
		return Some("Rust nightly not installed, please install it!")
	}

	if Command::new("wasm-gc")
		.stdout(Stdio::null())
		.stderr(Stdio::null())
		.status()
		.map(|s| !s.success()).unwrap_or(true)
	{
		return Some("`wasm-gc` not installed, please install it!")
	}

	if !check_wasm_toolchain_installed() {
		return Some("Rust WASM toolchain not installed, please install it!")
	}

	None
}

fn check_nightly_installed() -> bool {
	let version = Command::new("cargo")
		.arg("--version")
		.output()
		.map_err(|_| ())
		.and_then(|o| String::from_utf8(o.stdout).map_err(|_| ()))
		.unwrap_or_default();

	let version2 = Command::new("rustup")
		.args(&["run", "nightly", "cargo", "--version"])
		.output()
		.map_err(|_| ())
		.and_then(|o| String::from_utf8(o.stdout).map_err(|_| ()))
		.unwrap_or_default();

	version.contains("-nightly") || version2.contains("-nightly")
}

fn check_wasm_toolchain_installed() -> bool {
	let temp = tempdir().expect("Creating temp dir does not fail; qed");
	fs::create_dir_all(temp.path().join("src")).expect("Creating src dir does not fail; qed");

	let test_file = temp.path().join("src/lib.rs");
	let manifest_path = temp.path().join("Cargo.toml");

	fs::write(&manifest_path,
		r#"
			[package]
			name = "wasm-test"
			version = "1.0.0"
			edition = "2018"

			[lib]
			name = "wasm_test"
			crate-type = ["cdylib"]

			[workspace]
		"#,
	).expect("Writing wasm-test manifest does not fail; qed");
	fs::write(&test_file, "pub fn test() {}")
		.expect("Writing to the test file does not fail; qed");

	let manifest_path = manifest_path.display().to_string();
	crate::get_nightly_cargo()
		.args(&["build", "--target=wasm32-unknown-unknown", "--manifest-path", &manifest_path])
		.stdout(Stdio::null())
		.stderr(Stdio::null())
		.status()
		.map(|s| s.success())
		.unwrap_or(false)
}