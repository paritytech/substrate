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

#![cfg(unix)]
#![allow(dead_code)]

use std::{env, process::{Child, ExitStatus}, thread, time::Duration, path::{Path, PathBuf}};
use std::{convert::TryInto, process::Command};
use nix::sys::signal::{kill, Signal::SIGINT};
use nix::unistd::Pid;

/// Wait for the given `child` the given number of `secs`.
///
/// Returns the `Some(exit status)` or `None` if the process did not finish in the given time.
pub fn wait_for(child: &mut Child, secs: usize) -> Option<ExitStatus> {
	for i in 0..secs {
		match child.try_wait().unwrap() {
			Some(status) => {
				if i > 5 {
					eprintln!("Child process took {} seconds to exit gracefully", i);
				}
				return Some(status)
			},
			None => thread::sleep(Duration::from_secs(1)),
		}
	}
	eprintln!("Took too long to exit (> {} seconds). Killing...", secs);
	let _ = child.kill();
	child.wait().unwrap();

	None
}

/// Run the node for a while (30 seconds)
pub fn run_dev_node_for_a_while(base_path: &Path) {
	let mut cmd = Command::new(cargo_bin("substrate"));

	let mut cmd = cmd
		.args(&["--dev"])
		.arg("-d")
		.arg(base_path)
		.spawn()
		.unwrap();

	// Let it produce some blocks.
	thread::sleep(Duration::from_secs(30));
	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(cmd.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(wait_for(&mut cmd, 40).map(|x| x.success()).unwrap_or_default());
}

// Code taken directly from https://github.com/assert-rs/assert_cmd/blob/d9fcca1ac40496afbcdaea719082e5d7f105f4d9/src/cargo.rs
// Adapted from
// https://github.com/rust-lang/cargo/blob/485670b3983b52289a2f353d589c57fae2f60f82/tests/testsuite/support/mod.rs#L507
fn target_dir() -> PathBuf {
	env::current_exe()
		.ok()
		.map(|mut path| {
			path.pop();
			if path.ends_with("deps") {
				path.pop();
			}
			path
		})
		.unwrap()
}

/// Look up the path to a cargo-built binary within an integration test.
pub fn cargo_bin<S: AsRef<str>>(name: S) -> PathBuf {
	cargo_bin_str(name.as_ref())
}

fn cargo_bin_str(name: &str) -> PathBuf {
	target_dir().join(format!("{}{}", name, env::consts::EXE_SUFFIX))
}
