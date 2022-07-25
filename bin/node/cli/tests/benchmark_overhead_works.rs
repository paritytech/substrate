// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use std::process::Command;
use tempfile::tempdir;

/// Tests that the `benchmark overhead` command works for the substrate dev runtime.
#[test]
fn benchmark_overhead_works() {
	let tmp_dir = tempdir().expect("could not create a temp dir");
	let base_path = tmp_dir.path();

	// Only put 10 extrinsics into the block otherwise it takes forever to build it
	// especially for a non-release build.
	let status = Command::new(cargo_bin("substrate"))
		.args(&["benchmark", "overhead", "--dev", "-d"])
		.arg(base_path)
		.arg("--weight-path")
		.arg(base_path)
		.args(["--warmup", "10", "--repeat", "10"])
		.args(["--add", "100", "--mul", "1.2", "--metric", "p75"])
		.args(["--max-ext-per-block", "10"])
		.status()
		.unwrap();
	assert!(status.success());

	// Weight files have been created.
	assert!(base_path.join("block_weights.rs").exists());
	assert!(base_path.join("extrinsic_weights.rs").exists());
}
