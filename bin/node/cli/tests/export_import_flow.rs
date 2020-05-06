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
use std::{process::Command, fs, path::PathBuf};
use tempfile::{tempdir, TempDir};
use regex::Regex;
use lazy_static::lazy_static;

mod common;

fn contains_error(stderr: &[u8]) -> bool {
	let log_output = String::from_utf8_lossy(stderr).to_owned();
    lazy_static! {
        static ref RE: Regex = Regex::new("Error").unwrap();
    }
    RE.is_match(&log_output)
}

/// Helper struct to execute the export/import/revert tests.
/// The fields are paths to a temporary directory
struct ExportImportRevertExecutor<'a> {
	base_path: &'a TempDir,
	exported_blocks: &'a PathBuf,
	db_path: &'a PathBuf,
}

/// Format options for export / import commands.
enum FormatOpt {
	Json,
	Binary,
}

impl<'a> ExportImportRevertExecutor<'a> {
	fn new(base_path: &'a TempDir, exported_blocks: &'a PathBuf, db_path: &'a PathBuf) -> Self {
		Self {
			base_path,
			exported_blocks,
			db_path,
		}
	}

	/// Helper method to run a command.
	fn run_block_command(&self, command: &str, format_opt: FormatOpt, expected_to_fail: bool) {
		let arguments = match format_opt {
			FormatOpt::Binary => vec![command, "--dev", "--pruning", "archive", "--binary", "-d"],
			FormatOpt::Json => vec![command, "--dev", "--pruning", "archive", "-d"],
		};
		let output = Command::new(cargo_bin("substrate"))
			.args(&arguments)
			.arg(&self.base_path.path())
			.arg(&self.exported_blocks)
			.output()
			.unwrap();

		if expected_to_fail {
			// Checking that we did indeed find an error.
			assert!(contains_error(&output.stderr), "expected to error but did not error!");
		} else {
			// Making sure no error were logged.
			assert!(!contains_error(&output.stderr), "expected not to error but error'd!");
		}

		// Command should never fail.
		assert!(output.status.success());
	}

	/// Runs the `export-blocks` command.
	fn run_export(&self, fmt_opt: FormatOpt) {
		self.run_block_command("export-blocks", fmt_opt, false);

		let metadata = fs::metadata(&self.exported_blocks).unwrap();
		assert!(metadata.len() > 0, "file exported_blocks should not be empty");

		let _ = fs::remove_dir_all(&self.db_path);
	}

	/// Runs the `import-blocks` command, asserting that an error was found or not depending on `expected_to_fail`.
	fn run_import(&self, fmt_opt: FormatOpt, expected_to_fail: bool) {
		self.run_block_command("import-blocks", fmt_opt, expected_to_fail)
	}

	/// Runs the `revert` command.
	fn run_revert(&self) {
		let output = Command::new(cargo_bin("substrate"))
			.args(&["revert", "--dev", "--pruning", "archive", "-d"])
			.arg(&self.base_path.path())
			.output()
			.unwrap();

		// Reverting should not log any error.
		assert!(!contains_error(&output.stderr));
		// Command should never fail.
		assert!(output.status.success());
	}

	/// Helper function that runs the whole export / import / revert flow and checks for errors.
	fn run(&self, export_fmt: FormatOpt, import_fmt: FormatOpt, expected_to_fail: bool) {
		self.run_export(export_fmt);
		self.run_import(import_fmt, expected_to_fail);
		self.run_revert();
	}
}

#[test]
fn export_import_revert() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_dev_node_for_a_while(base_path.path());

	let executor = ExportImportRevertExecutor::new(
		&base_path,
		&exported_blocks,
		&db_path,
	);

	// Binary and binary should work.
	executor.run(FormatOpt::Binary, FormatOpt::Binary, false);
	// Binary and JSON should fail.
	executor.run(FormatOpt::Binary, FormatOpt::Json, true);
	// JSON and JSON should work.
	executor.run(FormatOpt::Json, FormatOpt::Json, false);
	// JSON and binary should fail.
	executor.run(FormatOpt::Json, FormatOpt::Binary, true);
}
