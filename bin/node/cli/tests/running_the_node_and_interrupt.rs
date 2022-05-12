// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
use nix::{
	sys::signal::{
		kill,
		Signal::{self, SIGINT, SIGTERM},
	},
	unistd::Pid,
};
use std::process::{self, Child, Command};
use tempfile::tempdir;

pub mod common;

#[tokio::test]
async fn running_the_node_works_and_can_be_interrupted() {
	async fn run_command_and_kill(signal: Signal) {
		let base_path = tempdir().expect("could not create a temp dir");
		let mut cmd = common::KillChildOnDrop(
			Command::new(cargo_bin("substrate"))
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

		let (ws_url, _) = common::find_ws_url_from_output(stderr);

		common::wait_n_finalized_blocks(3, 30, &ws_url)
			.await
			.expect("Blocks are produced in time");
		assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");
		kill(Pid::from_raw(cmd.id().try_into().unwrap()), signal).unwrap();
		assert_eq!(
			common::wait_for(&mut cmd, 30).map(|x| x.success()),
			Ok(true),
			"the process must exit gracefully after signal {}",
			signal,
		);
		// Check if the database was closed gracefully. If it was not,
		// there may exist a ref cycle that prevents the Client from being dropped properly.
		//
		// parity-db only writes the stats file on clean shutdown.
		let stats_file = base_path.path().join("chains/dev/paritydb/full/stats.txt");
		assert!(std::path::Path::exists(&stats_file));
	}

	run_command_and_kill(SIGINT).await;
	run_command_and_kill(SIGTERM).await;
}

#[tokio::test]
async fn running_two_nodes_with_the_same_ws_port_should_work() {
	fn start_node() -> Child {
		Command::new(cargo_bin("substrate"))
			.stdout(process::Stdio::piped())
			.stderr(process::Stdio::piped())
			.args(&["--dev", "--tmp", "--ws-port=45789", "--no-hardware-benchmarks"])
			.spawn()
			.unwrap()
	}

	let mut first_node = common::KillChildOnDrop(start_node());
	let mut second_node = common::KillChildOnDrop(start_node());

	let stderr = first_node.stderr.take().unwrap();
	let (ws_url, _) = common::find_ws_url_from_output(stderr);

	common::wait_n_finalized_blocks(3, 30, &ws_url).await.unwrap();

	assert!(first_node.try_wait().unwrap().is_none(), "The first node should still be running");
	assert!(second_node.try_wait().unwrap().is_none(), "The second node should still be running");

	kill(Pid::from_raw(first_node.id().try_into().unwrap()), SIGINT).unwrap();
	kill(Pid::from_raw(second_node.id().try_into().unwrap()), SIGINT).unwrap();

	assert_eq!(
		common::wait_for(&mut first_node, 30).map(|x| x.success()),
		Ok(true),
		"The first node must exit gracefully",
	);
	assert_eq!(
		common::wait_for(&mut second_node, 30).map(|x| x.success()),
		Ok(true),
		"The second node must exit gracefully",
	);
}
