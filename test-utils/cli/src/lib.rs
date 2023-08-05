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
	sys::signal::{kill, Signal, Signal::SIGINT},
	unistd::Pid,
};
use node_primitives::{Hash, Header};
use regex::Regex;
use sp_rpc::{list::ListOrValue, number::NumberOrHex};
use std::{
	io::{BufRead, BufReader, Read},
	ops::{Deref, DerefMut},
	path::{Path, PathBuf},
	process::{self, Child, Command},
	time::Duration,
};
use tokio::io::{AsyncBufReadExt, AsyncRead};

/// Starts a new Substrate node in development mode with a temporary chain.
///
/// This function creates a new Substrate node using the `substrate` binary.
/// It configures the node to run in development mode (`--dev`) with a temporary chain (`--tmp`),
/// sets the WebSocket port to 45789 (`--ws-port=45789`).
///
/// # Returns
///
/// A [`Child`] process representing the spawned Substrate node.
///
/// # Panics
///
/// This function will panic if the `substrate` binary is not found or if the node fails to start.
///
/// # Examples
///
/// ```ignore
/// use my_crate::start_node;
///
/// let child = start_node();
/// // Interact with the Substrate node using the WebSocket port 45789.
/// // When done, the node will be killed when the `child` is dropped.
/// ```
///
/// [`Child`]: std::process::Child
pub fn start_node() -> Child {
	Command::new(cargo_bin("substrate-node"))
		.stdout(process::Stdio::piped())
		.stderr(process::Stdio::piped())
		.args(&["--dev", "--tmp", "--rpc-port=45789", "--no-hardware-benchmarks"])
		.spawn()
		.unwrap()
}

/// Builds the Substrate project using the provided arguments.
///
/// This function reads the CARGO_MANIFEST_DIR environment variable to find the root workspace
/// directory. It then runs the `cargo b` command in the root directory with the specified
/// arguments.
///
/// This can be useful for building the Substrate binary with a desired set of features prior
/// to using the binary in a CLI test.
///
/// # Arguments
///
/// * `args: &[&str]` - A slice of string references representing the arguments to pass to the
///   `cargo b` command.
///
/// # Panics
///
/// This function will panic if:
///
/// * The CARGO_MANIFEST_DIR environment variable is not set.
/// * The root workspace directory cannot be determined.
/// * The 'cargo b' command fails to execute.
/// * The 'cargo b' command returns a non-successful status.
///
/// # Examples
///
/// ```ignore
/// build_substrate(&["--features=try-runtime"]);
/// ```
pub fn build_substrate(args: &[&str]) {
	let is_release_build = !cfg!(build_type = "debug");

	// Get the root workspace directory from the CARGO_MANIFEST_DIR environment variable
	let mut cmd = Command::new("cargo");

	cmd.arg("build").arg("-p=node-cli");

	if is_release_build {
		cmd.arg("--release");
	}

	let output = cmd
		.args(args)
		.output()
		.expect(format!("Failed to execute 'cargo b' with args {:?}'", args).as_str());

	if !output.status.success() {
		panic!(
			"Failed to execute 'cargo b' with args {:?}': \n{}",
			args,
			String::from_utf8_lossy(&output.stderr)
		);
	}
}

/// Takes a readable tokio stream (e.g. from a child process `ChildStderr` or `ChildStdout`) and
/// a `Regex` pattern, and checks each line against the given pattern as it is produced.
/// The function returns OK(()) as soon as a line matching the pattern is found, or an Err if
/// the stream ends without any lines matching the pattern.
///
/// # Arguments
///
/// * `child_stream` - An async tokio stream, e.g. from a child process `ChildStderr` or
///   `ChildStdout`.
/// * `re` - A `Regex` pattern to search for in the stream.
///
/// # Returns
///
/// * `Ok(())` if a line matching the pattern is found.
/// * `Err(String)` if the stream ends without any lines matching the pattern.
///
/// # Examples
///
/// ```ignore
/// use regex::Regex;
/// use tokio::process::Command;
/// use tokio::io::AsyncRead;
///
/// # async fn run() {
/// let child = Command::new("some-command").stderr(std::process::Stdio::piped()).spawn().unwrap();
/// let stderr = child.stderr.unwrap();
/// let re = Regex::new("error:").unwrap();
///
/// match wait_for_pattern_match_in_stream(stderr, re).await {
///     Ok(()) => println!("Error found in stderr"),
///     Err(e) => println!("Error: {}", e),
/// }
/// # }
/// ```
pub async fn wait_for_stream_pattern_match<R>(stream: R, re: Regex) -> Result<(), String>
where
	R: AsyncRead + Unpin,
{
	let mut stdio_reader = tokio::io::BufReader::new(stream).lines();
	while let Ok(Some(line)) = stdio_reader.next_line().await {
		match re.find(line.as_str()) {
			Some(_) => return Ok(()),
			None => (),
		}
	}
	Err(String::from("Stream closed without any lines matching the regex."))
}

/// Run the given `future` and panic if the `timeout` is hit.
pub async fn run_with_timeout(timeout: Duration, future: impl futures::Future<Output = ()>) {
	tokio::time::timeout(timeout, future).await.expect("Hit timeout");
}

/// Wait for at least n blocks to be finalized from a specified node
pub async fn wait_n_finalized_blocks(n: usize, url: &str) {
	use substrate_rpc_client::{ws_client, ChainApi};

	let mut built_blocks = std::collections::HashSet::new();
	let block_duration = Duration::from_secs(2);
	let mut interval = tokio::time::interval(block_duration);
	let rpc = ws_client(url).await.unwrap();

	loop {
		if let Ok(block) = ChainApi::<(), Hash, Header, ()>::finalized_head(&rpc).await {
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
	run_with_timeout(Duration::from_secs(60 * 10), async move {
		let mut cmd = Command::new(cargo_bin("substrate-node"))
			.stdout(process::Stdio::piped())
			.stderr(process::Stdio::piped())
			.args(args)
			.arg("-d")
			.arg(base_path)
			.spawn()
			.unwrap();

		let stderr = cmd.stderr.take().unwrap();

		let mut child = KillChildOnDrop(cmd);

		let ws_url = extract_info_from_output(stderr).0.ws_url;

		// Let it produce some blocks.
		wait_n_finalized_blocks(3, &ws_url).await;

		child.assert_still_running();

		// Stop the process
		child.stop();
	})
	.await
}

pub async fn block_hash(block_number: u64, url: &str) -> Result<Hash, String> {
	use substrate_rpc_client::{ws_client, ChainApi};

	let rpc = ws_client(url).await.unwrap();

	let result = ChainApi::<(), Hash, Header, ()>::block_hash(
		&rpc,
		Some(ListOrValue::Value(NumberOrHex::Number(block_number))),
	)
	.await
	.map_err(|_| "Couldn't get block hash".to_string())?;

	match result {
		ListOrValue::Value(maybe_block_hash) if maybe_block_hash.is_some() =>
			Ok(maybe_block_hash.unwrap()),
		_ => Err("Couldn't get block hash".to_string()),
	}
}

pub struct KillChildOnDrop(pub Child);

impl KillChildOnDrop {
	/// Stop the child and wait until it is finished.
	///
	/// Asserts if the exit status isn't success.
	pub fn stop(&mut self) {
		self.stop_with_signal(SIGINT);
	}

	/// Same as [`Self::stop`] but takes the `signal` that is sent to stop the child.
	pub fn stop_with_signal(&mut self, signal: Signal) {
		kill(Pid::from_raw(self.id().try_into().unwrap()), signal).unwrap();
		assert!(self.wait().unwrap().success());
	}

	/// Asserts that the child is still running.
	pub fn assert_still_running(&mut self) {
		assert!(self.try_wait().unwrap().is_none(), "the process should still be running");
	}
}

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

/// Information extracted from a running node.
pub struct NodeInfo {
	pub ws_url: String,
	pub db_path: PathBuf,
}

/// Extract [`NodeInfo`] from a running node by parsing its output.
///
/// Returns the [`NodeInfo`] and all the read data.
pub fn extract_info_from_output(read: impl Read + Send) -> (NodeInfo, String) {
	let mut data = String::new();

	let ws_url = BufReader::new(read)
		.lines()
		.find_map(|line| {
			let line = line.expect("failed to obtain next line while extracting node info");
			data.push_str(&line);
			data.push_str("\n");

			// does the line contain our port (we expect this specific output from substrate).
			let sock_addr = match line.split_once("Running JSON-RPC server: addr=") {
				None => return None,
				Some((_, after)) => after.split_once(",").unwrap().0,
			};

			Some(format!("ws://{}", sock_addr))
		})
		.unwrap_or_else(|| {
			eprintln!("Observed node output:\n{}", data);
			panic!("We should get a WebSocket address")
		});

	// Database path is printed before the ws url!
	let re = Regex::new(r"Database: .+ at (\S+)").unwrap();
	let db_path = PathBuf::from(re.captures(data.as_str()).unwrap().get(1).unwrap().as_str());

	(NodeInfo { ws_url, db_path }, data)
}
