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
use std::convert::TryInto;
use std::process::{Child, Command, ExitStatus};
use std::thread::sleep;
use std::time::Duration;

#[test]
#[cfg(unix)]
fn running_the_node_works_and_can_be_interrupted() {
	use nix::sys::signal::{kill, Signal::{self, SIGINT, SIGTERM}};
	use nix::unistd::Pid;

	fn wait_for(child: &mut Child, secs: usize) -> Option<ExitStatus> {
		for _ in 0..secs {
			match child.try_wait().unwrap() {
				Some(status) => return Some(status),
				None => sleep(Duration::from_secs(1)),
			}
		}
		eprintln!("Took to long to exit. Killing...");
		let _ = child.kill();
		child.wait().unwrap();

		None
	}

	fn run_command_and_kill(signal: Signal) {
		let mut cmd = Command::new(cargo_bin("substrate")).spawn().unwrap();
		sleep(Duration::from_secs(30));
		assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");
		kill(Pid::from_raw(cmd.id().try_into().unwrap()), signal).unwrap();
		assert_eq!(
			wait_for(&mut cmd, 30).map(|x| x.success()),
			Some(true),
			"the pocess must exit gracefully after signal {}",
			signal,
		);
	}

	run_command_and_kill(SIGINT);
	run_command_and_kill(SIGTERM);
}
