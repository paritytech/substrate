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
use regex::Regex;
use lazy_static::lazy_static;

mod common;

fn contains_error(log: &str) -> bool {
    lazy_static! {
        static ref RE: Regex = Regex::new("Error").unwrap();
    }
    RE.is_match(log)
}

#[test]
fn export_binary_import_binary_works() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_dev_node_for_a_while(base_path.path());

	let output = Command::new(cargo_bin("substrate"))
		.args(&["export-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.unwrap();

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(&db_path);

	let output = Command::new(cargo_bin("substrate"))
		.args(&["import-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.expect("failed to execute process");

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());
}

#[test]
fn export_default_import_default_works() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_dev_node_for_a_while(base_path.path());

	let output = Command::new(cargo_bin("substrate"))
		.args(&["export-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.unwrap();

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(&db_path);

	let output = Command::new(cargo_bin("substrate"))
		.args(&["import-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.expect("failed to execute process");

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());
}

#[test]
fn export_binary_import_default_works() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_dev_node_for_a_while(base_path.path());

	let output = Command::new(cargo_bin("substrate"))
		.args(&["export-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.unwrap();

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(&db_path);

	let output = Command::new(cargo_bin("substrate"))
		.args(&["import-blocks", "--pruning", "archive", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.expect("failed to execute process");

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure we found an error.
	assert!(contains_error(&log_output));

	// Exit code should still be 0.
	assert!(output.status.success());
}

#[test]
fn export_default_import_binary_works() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_dev_node_for_a_while(base_path.path());

	let output = Command::new(cargo_bin("substrate"))
		.args(&["export-blocks", "--pruning", "archive", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.unwrap();

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure no error were logged.
	assert!(!contains_error(&log_output));

	assert!(output.status.success());

	let metadata = fs::metadata(&exported_blocks).unwrap();
	assert!(metadata.len() > 0, "file exported_blocks should not be empty");

	let _ = fs::remove_dir_all(&db_path);

	let output = Command::new(cargo_bin("substrate"))
		.args(&["import-blocks", "--pruning", "archive", "--binary", "--dev", "-d"])
		.arg(&base_path.path())
		.arg(&exported_blocks)
		.output()
		.expect("failed to execute process");

	let log_output = String::from_utf8_lossy(&output.stderr).to_owned();
	// Making sure we found an error.
	assert!(contains_error(&log_output));

	// Exit code should still be 0.
	assert!(output.status.success());
}