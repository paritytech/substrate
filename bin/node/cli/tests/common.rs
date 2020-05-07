// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg(unix)]
#![allow(dead_code)]

use std::{process::{Child, ExitStatus}, thread, time::Duration, path::Path};
use assert_cmd::cargo::cargo_bin;
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
