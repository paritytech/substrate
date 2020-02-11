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

use std::fs;

use tempfile::tempdir;

/// Checks that all prerequisites are installed.
///
/// # Returns
/// Returns `None` if everything was found and `Some(ERR_MSG)` if something could not be found.
pub fn check() -> Option<&'static str> {
	if !check_nightly_installed(){
		return Some("Rust nightly not installed, please install it!")
	}

	check_wasm_toolchain_installed()
}

fn check_nightly_installed() -> bool {
	crate::get_nightly_cargo().is_nightly()
}

fn check_wasm_toolchain_installed() -> Option<&'static str> {
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

	let err_msg = "Rust WASM toolchain not installed, please install it!";
	let manifest_path = manifest_path.display().to_string();
	crate::get_nightly_cargo()
		.command()
		.args(&["build", "--target=wasm32-unknown-unknown", "--manifest-path", &manifest_path])
		.output()
		.map_err(|_| err_msg)
		.and_then(|s|
			if s.status.success() {
				Ok(())
			} else {
				match String::from_utf8(s.stderr) {
					Ok(ref err) if err.contains("linker `rust-lld` not found") => {
						Err("`rust-lld` not found, please install it!")
					},
					_ => Err(err_msg)
				}
			}
		)
		.err()
}
