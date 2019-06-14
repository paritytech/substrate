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

	if Command::new("wasm-gc").stdout(Stdio::null()).status().map(|s| !s.success()).unwrap_or(true) {
		return Some("wasm-gc not installed, please install it!")
	}

	if !check_wasm_toolchain_installed() {
		return Some("Rurst WASM toolchain not installed, please install it!")
	}

	None
}

fn check_nightly_installed() -> bool {
	let cargo_bin = build_helper::bin::cargo();

	let version = String::from_utf8(
		Command::new(&cargo_bin)
			.arg("--version")
			.output()
			.expect("Cargo version never fails; qed")
			.stdout
	).unwrap_or_default();
	let version2 = String::from_utf8(
		Command::new(&cargo_bin)
			.args(&["+nightly", "--version"])
			.output()
			.expect("Cargo version never fails; qed")
			.stdout
	).unwrap_or_default();

	println!("VERSION: {}", version);
	println!("VERSION2: {}", version2);
	panic!();

	version.contains("-nightly") || version2.contains("-nightly")
}

fn check_wasm_toolchain_installed() -> bool {
	let temp = tempdir().expect("Creating temp dir does not fail; qed");
	let test_file = temp.path().join("main.rs");
	let out_file = temp.path().join("out.wasm").display().to_string();

	fs::write(&test_file, "fn main() {}").expect("Writing to the test file does not fail; qed");

	let test_file = test_file.display().to_string();
	Command::new(build_helper::bin::rustc())
		.args(&["--target=wasm32-unknown-unknown", &test_file, "-o", &out_file])
		.status()
		.map(|s| s.success())
		.unwrap_or(false)
}