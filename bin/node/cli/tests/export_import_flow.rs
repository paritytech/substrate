// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

#![cfg(unix)]

use assert_cmd::cargo::cargo_bin;
use regex::Regex;
use std::{fs, path::PathBuf, process::Command};
use tempfile::{tempdir, TempDir};

use substrate_cli_test_utils as common;

fn contains_error(logged_output: &str) -> bool {
	logged_output.contains("Error")
}

/// Helper struct to execute the export/import/revert tests.
/// The fields are paths to a temporary directory
struct ExportImportRevertExecutor<'a> {
	base_path: &'a TempDir,
	exported_blocks_file: &'a PathBuf,
	db_path: &'a PathBuf,
	num_exported_blocks: Option<u64>,
}

/// Format options for export / import commands.
enum FormatOpt {
	Json,
	Binary,
}

/// Command corresponding to the different commands we would like to run.
enum SubCommand {
	ExportBlocks,
	ImportBlocks,
}

impl ToString for SubCommand {
	fn to_string(&self) -> String {
		match self {
			SubCommand::ExportBlocks => String::from("export-blocks"),
			SubCommand::ImportBlocks => String::from("import-blocks"),
		}
	}
}

impl<'a> ExportImportRevertExecutor<'a> {
	fn new(
		base_path: &'a TempDir,
		exported_blocks_file: &'a PathBuf,
		db_path: &'a PathBuf,
	) -> Self {
		Self { base_path, exported_blocks_file, db_path, num_exported_blocks: None }
	}

	/// Helper method to run a command. Returns a string corresponding to what has been logged.
	fn run_block_command(
		&self,
		sub_command: SubCommand,
		format_opt: FormatOpt,
		expected_to_fail: bool,
	) -> String {
		let sub_command_str = sub_command.to_string();
		// Adding "--binary" if need be.
		let arguments: Vec<&str> = match format_opt {
			FormatOpt::Binary => {
				vec![&sub_command_str, "--dev", "--binary", "-d"]
			},
			FormatOpt::Json => vec![&sub_command_str, "--dev", "-d"],
		};

		let tmp: TempDir;
		// Setting base_path to be a temporary folder if we are importing blocks.
		// This allows us to make sure we are importing from scratch.
		let base_path = match sub_command {
			SubCommand::ExportBlocks => &self.base_path.path(),
			SubCommand::ImportBlocks => {
				tmp = tempdir().unwrap();
				tmp.path()
			},
		};

		// Running the command and capturing the output.
		let output = Command::new(cargo_bin("substrate-node"))
			.args(&arguments)
			.arg(&base_path)
			.arg(&self.exported_blocks_file)
			.output()
			.unwrap();

		let logged_output = String::from_utf8_lossy(&output.stderr).to_string();

		if expected_to_fail {
			// Checking that we did indeed find an error.
			assert!(contains_error(&logged_output), "expected to error but did not error!");
			assert!(!output.status.success());
		} else {
			// Making sure no error were logged.
			assert!(!contains_error(&logged_output), "expected not to error but error'd!");
			assert!(output.status.success());
		}

		logged_output
	}

	/// Runs the `export-blocks` command.
	fn run_export(&mut self, fmt_opt: FormatOpt) {
		let log = self.run_block_command(SubCommand::ExportBlocks, fmt_opt, false);

		// Using regex to find out how many block we exported.
		let re = Regex::new(r"Exporting blocks from #\d* to #(?P<exported_blocks>\d*)").unwrap();
		let caps = re.captures(&log).unwrap();
		// Saving the number of blocks we've exported for further use.
		self.num_exported_blocks = Some(caps["exported_blocks"].parse::<u64>().unwrap());

		let metadata = fs::metadata(&self.exported_blocks_file).unwrap();
		assert!(metadata.len() > 0, "file exported_blocks should not be empty");

		let _ = fs::remove_dir_all(&self.db_path);
	}

	/// Runs the `import-blocks` command, asserting that an error was found or
	/// not depending on `expected_to_fail`.
	fn run_import(&mut self, fmt_opt: FormatOpt, expected_to_fail: bool) {
		let log = self.run_block_command(SubCommand::ImportBlocks, fmt_opt, expected_to_fail);

		if !expected_to_fail {
			// Using regex to find out how much block we imported,
			// and what's the best current block.
			let re =
				Regex::new(r"Imported (?P<imported>\d*) blocks. Best: #(?P<best>\d*)").unwrap();
			let caps = re.captures(&log).expect("capture should have succeeded");
			let imported = caps["imported"].parse::<u64>().unwrap();
			let best = caps["best"].parse::<u64>().unwrap();

			assert_eq!(imported, best, "numbers of blocks imported and best number differs");
			assert_eq!(
				best,
				self.num_exported_blocks.expect("number of exported blocks cannot be None; qed"),
				"best block number and number of expected blocks should not differ"
			);
		}
		self.num_exported_blocks = None;
	}

	/// Runs the `revert` command.
	fn run_revert(&self) {
		let output = Command::new(cargo_bin("substrate-node"))
			.args(&["revert", "--dev", "-d"])
			.arg(&self.base_path.path())
			.output()
			.unwrap();

		let logged_output = String::from_utf8_lossy(&output.stderr).to_string();

		// Reverting should not log any error.
		assert!(!contains_error(&logged_output));
		// Command should never fail.
		assert!(output.status.success());
	}

	/// Helper function that runs the whole export / import / revert flow and checks for errors.
	fn run(&mut self, export_fmt: FormatOpt, import_fmt: FormatOpt, expected_to_fail: bool) {
		self.run_export(export_fmt);
		self.run_import(import_fmt, expected_to_fail);
		self.run_revert();
	}
}

#[tokio::test]
async fn export_import_revert() {
	let base_path = tempdir().expect("could not create a temp dir");
	let exported_blocks_file = base_path.path().join("exported_blocks");
	let db_path = base_path.path().join("db");

	common::run_node_for_a_while(base_path.path(), &["--dev", "--no-hardware-benchmarks"]).await;

	let mut executor = ExportImportRevertExecutor::new(&base_path, &exported_blocks_file, &db_path);

	// Binary and binary should work.
	executor.run(FormatOpt::Binary, FormatOpt::Binary, false);
	// Binary and JSON should fail.
	executor.run(FormatOpt::Binary, FormatOpt::Json, true);
	// JSON and JSON should work.
	executor.run(FormatOpt::Json, FormatOpt::Json, false);
	// JSON and binary should fail.
	executor.run(FormatOpt::Json, FormatOpt::Binary, true);
}
