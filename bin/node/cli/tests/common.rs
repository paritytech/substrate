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
	sys::signal::{kill, Signal::SIGINT},
	unistd::Pid,
};
use node_primitives::Block;
use remote_externalities::rpc_api;
use std::{
	ops::{Deref, DerefMut},
	path::Path,
	process::{Child, Command, ExitStatus},
	time::Duration,
};
use tokio::time::timeout;

static LOCALHOST_WS: &str = "ws://127.0.0.1:9944/";

/// Wait for the given `child` the given number of `secs`.
///
/// Returns the `Some(exit status)` or `None` if the process did not finish in the given time.
pub fn wait_for(child: &mut Child, secs: u64) -> Result<ExitStatus, ()> {
	let result = wait_timeout::ChildExt::wait_timeout(child, Duration::from_secs(5.min(secs)))
		.map_err(|_| ())?;
	if let Some(exit_status) = result {
		Ok(exit_status)
	} else {
		if secs > 5 {
			eprintln!("Child process taking over 5 seconds to exit gracefully");
			let result = wait_timeout::ChildExt::wait_timeout(child, Duration::from_secs(secs - 5))
				.map_err(|_| ())?;
			if let Some(exit_status) = result {
				return Ok(exit_status)
			}
		}
		eprintln!("Took too long to exit (> {} seconds). Killing...", secs);
		let _ = child.kill();
		child.wait().unwrap();
		Err(())
	}
}

/// Wait for at least n blocks to be finalized within a specified time.
pub async fn wait_n_finalized_blocks(
	n: usize,
	timeout_secs: u64,
) -> Result<(), tokio::time::error::Elapsed> {
	timeout(Duration::from_secs(timeout_secs), wait_n_finalized_blocks_from(n, LOCALHOST_WS)).await
}

/// Wait for at least n blocks to be finalized from a specified node
pub async fn wait_n_finalized_blocks_from(n: usize, url: &str) {
	let mut built_blocks = std::collections::HashSet::new();
	let mut interval = tokio::time::interval(Duration::from_secs(2));

	loop {
		if let Ok(block) = rpc_api::get_finalized_head::<Block, _>(url.to_string()).await {
			built_blocks.insert(block);
			if built_blocks.len() > n {
				break
			}
		};
		interval.tick().await;
	}
}

/// Run the node for a while (3 blocks)
pub async fn run_node_for_a_while(base_path: &Path, args: &[&str]) {
	let mut cmd = Command::new(cargo_bin("substrate"));

	let mut child = KillChildOnDrop(cmd.args(args).arg("-d").arg(base_path).spawn().unwrap());

	// Let it produce some blocks.
	let _ = wait_n_finalized_blocks(3, 30).await;

	assert!(child.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(child.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(wait_for(&mut child, 40).map(|x| x.success()).unwrap());
}

/// Run the node asserting that it fails with an error
pub fn run_node_assert_fail(base_path: &Path, args: &[&str]) {
	let mut cmd = Command::new(cargo_bin("substrate"));

	let mut child = KillChildOnDrop(cmd.args(args).arg("-d").arg(base_path).spawn().unwrap());

	// Let it produce some blocks, but it should die within 10 seconds.
	assert_ne!(
		wait_timeout::ChildExt::wait_timeout(&mut *child, Duration::from_secs(10)).unwrap(),
		None,
		"the process should not be running anymore"
	);
}

pub struct KillChildOnDrop(pub Child);

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
