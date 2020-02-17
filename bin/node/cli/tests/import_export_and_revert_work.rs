// Copyright 2020 Parity Technologies (UK) Ltd.
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

#![cfg(unix)]

use assert_cmd::cargo::cargo_bin;
use std::{process::Command, fs};
use tempfile::tempdir;

mod common;

#[test]
fn import_export_and_revert_work() {
	let base_path = tempdir().unwrap();
	let exported_blocks = base_path.path().join("exported_blocks");

	common::run_command_for_a_while(&["-d", base_path.path().to_str().unwrap()]);

	let status = Command::new(cargo_bin("substrate"))
		.args(&[
			"export-blocks", "-d", base_path.path().to_str().unwrap(),
			exported_blocks.to_str().unwrap(),
		])
		.status()
		.unwrap();
	assert!(status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(base_path.path().join("db"));

	let status = Command::new(cargo_bin("substrate"))
		.args(&[
			"import-blocks", "-d", base_path.path().to_str().unwrap(),
			exported_blocks.to_str().unwrap(),
		])
		.status()
		.unwrap();
	assert!(status.success());

	let status = Command::new(cargo_bin("substrate"))
		.args(&["revert", "-d", base_path.path().to_str().unwrap()])
		.status()
		.unwrap();
	assert!(status.success());
}
