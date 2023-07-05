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
use std::{
	process::{Command, Stdio},
	time::Duration,
};

use substrate_cli_test_utils as common;

#[allow(dead_code)]
// Apparently `#[ignore]` doesn't actually work to disable this one.
//#[tokio::test]
async fn temp_base_path_works() {
	common::run_with_timeout(Duration::from_secs(60 * 10), async move {
		let mut cmd = Command::new(cargo_bin("substrate"));
		let mut child = common::KillChildOnDrop(
			cmd.args(&["--dev", "--tmp", "--no-hardware-benchmarks"])
				.stdout(Stdio::piped())
				.stderr(Stdio::piped())
				.spawn()
				.unwrap(),
		);

		let mut stderr = child.stderr.take().unwrap();
		let node_info = common::extract_info_from_output(&mut stderr).0;

		// Let it produce some blocks.
		common::wait_n_finalized_blocks(3, &node_info.ws_url).await;

		// Ensure the db path exists while the node is running
		assert!(node_info.db_path.exists());

		child.assert_still_running();

		// Stop the process
		child.stop();

		if node_info.db_path.exists() {
			panic!("Database path `{}` wasn't deleted!", node_info.db_path.display());
		}
	})
	.await;
}
