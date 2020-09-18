// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::fs;

use tempfile::tempdir;
use ansi_term::Color;

/// Print an error message.
fn print_error_message(message: &str) -> String {
	if super::color_output_enabled() {
		Color::Red.bold().paint(message).to_string()
	} else {
		message.into()
	}
}

/// Checks that all prerequisites are installed.
///
/// # Returns
/// Returns `None` if everything was found and `Some(ERR_MSG)` if something could not be found.
pub fn check() -> Option<String> {
	if !check_nightly_installed(){
		return Some(print_error_message("Rust nightly not installed, please install it!"))
	}

	check_wasm_toolchain_installed()
}

fn check_nightly_installed() -> bool {
	crate::get_nightly_cargo().is_nightly()
}

fn check_wasm_toolchain_installed() -> Option<String> {
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

	let err_msg = print_error_message("Rust WASM toolchain not installed, please install it!");
	let manifest_path = manifest_path.display().to_string();

	let mut build_cmd = crate::get_nightly_cargo().command();

	build_cmd.args(&["build", "--target=wasm32-unknown-unknown", "--manifest-path", &manifest_path]);

	if super::color_output_enabled() {
		build_cmd.arg("--color=always");
	}

	build_cmd
		.output()
		.map_err(|_| err_msg.clone())
		.and_then(|s|
			if s.status.success() {
				Ok(())
			} else {
				match String::from_utf8(s.stderr) {
					Ok(ref err) if err.contains("linker `rust-lld` not found") => {
						Err(print_error_message("`rust-lld` not found, please install it!"))
					},
					Ok(ref err) => Err(
						format!(
							"{}\n\n{}\n{}\n{}{}\n",
							err_msg,
							Color::Yellow.bold().paint("Further error information:"),
							Color::Yellow.bold().paint("-".repeat(60)),
							err,
							Color::Yellow.bold().paint("-".repeat(60)),
						)
					),
					Err(_) => Err(err_msg),
				}
			}
		)
		.err()
}
