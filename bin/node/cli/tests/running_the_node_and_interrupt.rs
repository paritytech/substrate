// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use sc_service::Deref;
use std::{
	convert::TryInto,
	ops::DerefMut,
	process::{Child, Command},
	thread,
	time::Duration,
};
use tempfile::tempdir;

pub mod common;

#[test]
fn running_the_node_works_and_can_be_interrupted() {
	fn run_command_and_kill(signal: Signal) {
		let base_path = tempdir().expect("could not create a temp dir");
		let mut cmd = Command::new(cargo_bin("substrate"))
			.args(&["--dev", "-d"])
			.arg(base_path.path())
			.spawn()
			.unwrap();

		thread::sleep(Duration::from_secs(20));
		assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");
		kill(Pid::from_raw(cmd.id().try_into().unwrap()), signal).unwrap();
		assert_eq!(
			common::wait_for(&mut cmd, 30).map(|x| x.success()),
			Some(true),
			"the process must exit gracefully after signal {}",
			signal,
		);
	}

	run_command_and_kill(SIGINT);
	run_command_and_kill(SIGTERM);
}

struct KillChildOnDrop(Child);

impl Drop for KillChildOnDrop {
	fn drop(&mut self) {
		let _ = self.0.kill();
	}
}

impl Deref for KillChildOnDrop {
	type Target = Child;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl DerefMut for KillChildOnDrop {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

#[test]
fn running_two_nodes_with_the_same_ws_port_should_work() {
	fn start_node() -> Child {
		Command::new(cargo_bin("substrate"))
			.args(&["--dev", "--tmp", "--ws-port=45789"])
			.spawn()
			.unwrap()
	}

	let mut first_node = KillChildOnDrop(start_node());
	let mut second_node = KillChildOnDrop(start_node());

	thread::sleep(Duration::from_secs(30));

	assert!(first_node.try_wait().unwrap().is_none(), "The first node should still be running");
	assert!(second_node.try_wait().unwrap().is_none(), "The second node should still be running");

	kill(Pid::from_raw(first_node.id().try_into().unwrap()), SIGINT).unwrap();
	kill(Pid::from_raw(second_node.id().try_into().unwrap()), SIGINT).unwrap();

	assert_eq!(
		common::wait_for(&mut first_node, 30).map(|x| x.success()),
		Some(true),
		"The first node must exit gracefully",
	);
	assert_eq!(
		common::wait_for(&mut second_node, 30).map(|x| x.success()),
		Some(true),
		"The second node must exit gracefully",
	);
}
