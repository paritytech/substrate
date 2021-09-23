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
	sys::signal::{kill, Signal::SIGINT},
	unistd::Pid,
};
use regex::Regex;
use std::{
	convert::TryInto,
	io::Read,
	path::PathBuf,
	process::{Command, Stdio},
};

pub mod common;

#[tokio::test]
async fn temp_base_path_works() {
	// Test depends on log output so set RUST_LOG:
	let mut cmd = Command::new(cargo_bin("substrate"));
	let mut cmd = cmd
		.args(&["--dev", "--tmp"])
		.env("RUST_LOG", "info")
		.stdout(Stdio::piped())
		.stderr(Stdio::piped())
		.spawn()
		.unwrap();

	// Let it produce some blocks.
	common::wait_n_blocks(3, 30).await.unwrap();
	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(cmd.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(common::wait_for(&mut cmd, 40).map(|x| x.success()).unwrap_or_default());

	// Ensure the database has been deleted
	let mut stderr = String::new();
	cmd.stderr.unwrap().read_to_string(&mut stderr).unwrap();
	let re = Regex::new(r"Database: .+ at (\S+)").unwrap();
	let db_path = PathBuf::from(re.captures(stderr.as_str()).unwrap().get(1).unwrap().as_str());

	assert!(!db_path.exists());
}
