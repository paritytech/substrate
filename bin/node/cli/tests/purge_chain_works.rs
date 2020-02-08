// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use assert_cmd::cargo::cargo_bin;
use std::{convert::TryInto, process::Command, thread, time::Duration, fs, path::PathBuf};

mod common;

#[test]
#[cfg(unix)]
fn purge_chain_works() {
	use nix::sys::signal::{kill, Signal::SIGINT};
	use nix::unistd::Pid;

	let base_path = "purge_chain_test";

	let _ = fs::remove_dir_all(base_path);
	let mut cmd = Command::new(cargo_bin("substrate"))
		.args(&["--dev", "-d", base_path])
		.spawn()
		.unwrap();

	// Let it produce some blocks.
	thread::sleep(Duration::from_secs(30));
	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(cmd.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(common::wait_for(&mut cmd, 30).map(|x| x.success()).unwrap_or_default());

	let status = Command::new(cargo_bin("substrate"))
		.args(&["purge-chain", "--dev", "-d", base_path, "-y"])
		.status()
		.unwrap();
	assert!(status.success());

	// Make sure that the `dev` chain folder exists, but the `db` is deleted.
	assert!(PathBuf::from(base_path).join("chains/dev/").exists());
	assert!(!PathBuf::from(base_path).join("chains/dev/db").exists());
}
