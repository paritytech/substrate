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

// Unix only since it uses signals from [`common::run_node_for_a_while`].
#![cfg(unix)]

use assert_cmd::cargo::cargo_bin;
use std::process::Command;
use tempfile::tempdir;

use substrate_cli_test_utils as common;

/// `benchmark block` works for the dev runtime using the wasm executor.
#[tokio::test]
async fn benchmark_block_works() {
	let base_dir = tempdir().expect("could not create a temp dir");

	common::run_node_for_a_while(base_dir.path(), &["--dev", "--no-hardware-benchmarks"]).await;

	// Invoke `benchmark block` with all options to make sure that they are valid.
	let status = Command::new(cargo_bin("substrate"))
		.args(["benchmark", "block", "--dev"])
		.arg("-d")
		.arg(base_dir.path())
		.args(["--from", "1", "--to", "1"])
		.args(["--repeat", "1"])
		.args(["--wasm-execution", "compiled"])
		.status()
		.unwrap();

	assert!(status.success())
}
