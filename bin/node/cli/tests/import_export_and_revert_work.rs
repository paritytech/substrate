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
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");

	common::run_dev_node_for_a_while(base_path.path());

	let status = Command::new(cargo_bin("substrate"))
		.args(&["export-blocks", "--dev", "--pruning", "archive", "-d"])
		.arg(base_path.path())
		.arg(&exported_blocks)
		.status()
		.unwrap();
	assert!(status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(base_path.path().join("db"));

	let status = Command::new(cargo_bin("substrate"))
		.args(&["import-blocks", "--dev", "--pruning", "archive", "-d"])
		.arg(base_path.path())
		.arg(&exported_blocks)
		.status()
		.unwrap();
	assert!(status.success());

	let status = Command::new(cargo_bin("substrate"))
		.args(&["revert", "--dev", "--pruning", "archive", "-d"])
		.arg(base_path.path())
		.status()
		.unwrap();
	assert!(status.success());
}
