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
use std::{
	convert::TryInto,
	path::Path,
	process::{Child, Command, ExitStatus},
	thread,
	time::Duration,
};
use tokio::time::timeout;

static LOCALHOST_WS: &str = "ws://127.0.0.1:9944/";

/// Wait for the given `child` the given number of `secs`.
///
/// Returns the `Some(exit status)` or `None` if the process did not finish in the given time.
pub fn wait_for(child: &mut Child, secs: u64) -> Result<ExitStatus, ()> {
	assert!(secs > 5);

	let result =
		wait_timeout::ChildExt::wait_timeout(child, Duration::from_secs(5)).map_err(|_| ())?;
	if let Some(exit_status) = result {
		Ok(exit_status)
	} else {
		eprintln!("Child process taking over 5 seconds to exit gracefully");
		let result = wait_timeout::ChildExt::wait_timeout(child, Duration::from_secs(secs - 5))
			.map_err(|_| ())?;
		if let Some(exit_status) = result {
			Ok(exit_status)
		} else {
			eprintln!("Took too long to exit (> {} seconds). Killing...", secs);
			let _ = child.kill();
			child.wait().unwrap();
			Err(())
		}
	}
}

pub async fn wait_n_blocks(n: usize, timeout_secs: u64) -> Result<(), tokio::time::error::Elapsed> {
	timeout(Duration::from_secs(timeout_secs), wait_n_blocks_from(n, LOCALHOST_WS)).await
}

/// Wait for at least n blocks to be produced
///
/// Eg. to wait for 3 blocks or a timeout of 30 seconds:
/// ```
/// timeout(Duration::from_secs(30), wait_n_blocks("ws://127.0.0.1:9944/", 3)).await;
/// ```
pub async fn wait_n_blocks_from(n: usize, url: &str) {
	let mut built_blocks = std::collections::HashSet::new();
	let mut interval = tokio::time::interval(Duration::from_secs(2));

	loop {
		// We could call remote-externalities like this:
		// = remote_externalities::rpc_api::get_finalized_head::<String,
		// String>("ws://127.0.0.1:9944/".to_string()).await;
		// but then we'd need to gen the types to get the BlockT type.
		// https://github.com/paritytech/substrate-subxt/blob/aj-metadata-vnext/proc-macro/src/generate_types.rs

		if let Ok(ws_client) = jsonrpsee_ws_client::WsClientBuilder::default().build(url).await {
			let block_result: Result<String, _> =
				<jsonrpsee_ws_client::WsClient as jsonrpsee_ws_client::types::traits::Client>::request(
					&ws_client,
					"chain_getFinalizedHead",
					jsonrpsee_ws_client::types::v2::params::JsonRpcParams::NoParams,
				)
				.await;
			if let Ok(block) = block_result {
				built_blocks.insert(block);
				if built_blocks.len() > n {
					break
				}
			}
		}
		interval.tick().await;
	}
}

/// Run the node for a while (3 blocks)
pub fn run_node_for_a_while(base_path: &Path, args: &[&str]) {
	let mut cmd = Command::new(cargo_bin("substrate"));

	let mut cmd = cmd.args(args).arg("-d").arg(base_path).spawn().unwrap();

	// Let it produce some blocks.
	tokio_test::block_on(wait_n_blocks(3, 30)).unwrap();

	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");

	// Stop the process
	kill(Pid::from_raw(cmd.id().try_into().unwrap()), SIGINT).unwrap();
	assert!(wait_for(&mut cmd, 40).map(|x| x.success()).unwrap());
}

/// Run the node asserting that it fails with an error
pub fn run_node_assert_fail(base_path: &Path, args: &[&str]) {
	let mut cmd = Command::new(cargo_bin("substrate"));

	let mut cmd = cmd.args(args).arg("-d").arg(base_path).spawn().unwrap();

	// Let it produce some blocks.
	thread::sleep(Duration::from_secs(10));
	assert!(cmd.try_wait().unwrap().is_some(), "the process should not be running anymore");
}
