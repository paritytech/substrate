// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
