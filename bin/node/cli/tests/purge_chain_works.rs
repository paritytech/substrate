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
use std::process::Command;
use tempfile::tempdir;

use substrate_cli_test_utils as common;

#[tokio::test]
#[cfg(unix)]
async fn purge_chain_works() {
	let base_path = tempdir().expect("could not create a temp dir");

	common::run_node_for_a_while(base_path.path(), &["--dev", "--no-hardware-benchmarks"]).await;

	let status = Command::new(cargo_bin("substrate"))
		.args(&["purge-chain", "--dev", "-d"])
		.arg(base_path.path())
		.arg("-y")
		.status()
		.unwrap();
	assert!(status.success());

	// Make sure that the `dev` chain folder exists, but the `db` is deleted.
	assert!(base_path.path().join("chains/dev/").exists());
	assert!(!base_path.path().join("chains/dev/db/full").exists());
}
