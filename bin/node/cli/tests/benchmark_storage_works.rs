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

use assert_cmd::cargo::cargo_bin;
use std::{
	path::Path,
	process::{Command, ExitStatus},
};
use tempfile::tempdir;

/// Tests that the `benchmark storage` command works for the dev runtime.
#[test]
fn benchmark_storage_works() {
	let tmp_dir = tempdir().expect("could not create a temp dir");
	let base_path = tmp_dir.path();

	// Benchmarking the storage works and creates the correct weight file.
	assert!(benchmark_storage("rocksdb", base_path).success());
	assert!(base_path.join("rocksdb_weights.rs").exists());

	assert!(benchmark_storage("paritydb", base_path).success());
	assert!(base_path.join("paritydb_weights.rs").exists());
}

fn benchmark_storage(db: &str, base_path: &Path) -> ExitStatus {
	Command::new(cargo_bin("substrate"))
		.args(&["benchmark", "storage", "--dev"])
		.arg("--db")
		.arg(db)
		.arg("--weight-path")
		.arg(base_path)
		.args(["--state-version", "1"])
		.args(["--warmups", "0"])
		.args(["--add", "100", "--mul", "1.2", "--metric", "p75"])
		.arg("--include-child-trees")
		.status()
		.unwrap()
}
