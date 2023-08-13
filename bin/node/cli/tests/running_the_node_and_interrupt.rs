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
use nix::sys::signal::Signal::{self, SIGINT, SIGTERM};
use std::{
	process::{self, Command},
	time::Duration,
};
use tempfile::tempdir;

use substrate_cli_test_utils as common;

#[tokio::test]
async fn running_the_node_works_and_can_be_interrupted() {
	common::run_with_timeout(Duration::from_secs(60 * 10), async move {
		async fn run_command_and_kill(signal: Signal) {
			let base_path = tempdir().expect("could not create a temp dir");
			let mut cmd = common::KillChildOnDrop(
				Command::new(cargo_bin("substrate-node"))
					.stdout(process::Stdio::piped())
					.stderr(process::Stdio::piped())
					.args(&["--dev", "-d"])
					.arg(base_path.path())
					.arg("--db=paritydb")
					.arg("--no-hardware-benchmarks")
					.spawn()
					.unwrap(),
			);

			let stderr = cmd.stderr.take().unwrap();

			let ws_url = common::extract_info_from_output(stderr).0.ws_url;

			common::wait_n_finalized_blocks(3, &ws_url).await;

			cmd.assert_still_running();

			cmd.stop_with_signal(signal);

			// Check if the database was closed gracefully. If it was not,
			// there may exist a ref cycle that prevents the Client from being dropped properly.
			//
			// parity-db only writes the stats file on clean shutdown.
			let stats_file = base_path.path().join("chains/dev/paritydb/full/stats.txt");
			assert!(std::path::Path::exists(&stats_file));
		}

		run_command_and_kill(SIGINT).await;
		run_command_and_kill(SIGTERM).await;
	})
	.await;
}

#[tokio::test]
async fn running_two_nodes_with_the_same_ws_port_should_work() {
	common::run_with_timeout(Duration::from_secs(60 * 10), async move {
		let mut first_node = common::KillChildOnDrop(common::start_node());
		let mut second_node = common::KillChildOnDrop(common::start_node());

		let stderr = first_node.stderr.take().unwrap();
		let ws_url = common::extract_info_from_output(stderr).0.ws_url;

		common::wait_n_finalized_blocks(3, &ws_url).await;

		first_node.assert_still_running();
		second_node.assert_still_running();

		first_node.stop();
		second_node.stop();
	})
	.await;
}
