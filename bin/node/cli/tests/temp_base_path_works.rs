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
use nix::{
	sys::signal::{kill, Signal::SIGINT},
	unistd::Pid,
};
use regex::Regex;
use std::{
	io::Read,
	path::PathBuf,
	process::{Command, Stdio},
};

pub mod common;

#[tokio::test]
async fn temp_base_path_works() {
	let mut cmd = Command::new(cargo_bin("substrate"));
	let mut child = common::KillChildOnDrop(
		cmd.args(&["--dev", "--tmp", "--no-hardware-benchmarks"])
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.spawn()
			.unwrap(),
	);

	let mut stderr = child.stderr.take().unwrap();
	let (ws_url, mut data) = common::find_ws_url_from_output(&mut stderr);

	// Let it produce some blocks.
	common::wait_n_finalized_blocks(3, 30, &ws_url).await.unwrap();
	assert!(child.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(child.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(common::wait_for(&mut child, 40).map(|x| x.success()).unwrap_or_default());

	// Ensure the database has been deleted
	stderr.read_to_string(&mut data).unwrap();
	let re = Regex::new(r"Database: .+ at (\S+)").unwrap();
	let db_path = PathBuf::from(re.captures(data.as_str()).unwrap().get(1).unwrap().as_str());

	assert!(!db_path.exists());
}
