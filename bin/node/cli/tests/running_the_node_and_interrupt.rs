// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

pub mod common;

#[tokio::test]
#[cfg(unix)]
async fn running_the_node_works_and_can_be_interrupted() {
	use nix::sys::signal::Signal::{self, SIGINT, SIGTERM};

	async fn run_command_and_kill(signal: Signal) {
		let mut client = common::start_local_dev_node();
		client.run_for(20u64).await.unwrap();
		client.signal(signal).unwrap();
		client.wait_to_die(30u32).await.unwrap();
		assert_eq!(
			client.exit_status().map(|x| x.success()),
			Some(true),
			"the process must exit gracefully after signal {}",
			signal,
		);
	}

	run_command_and_kill(SIGINT).await;
	run_command_and_kill(SIGTERM).await;
}
