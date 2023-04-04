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
use regex::Regex;
use std::{
	process::{self, Child, Command},
	time::Duration,
};
use tokio::io::{AsyncBufReadExt, AsyncRead};

pub mod common;

#[tokio::test]
async fn follow_chain_works() {
	common::run_with_timeout(Duration::from_secs(60), async move {
		/// Asynchronously reads lines from an async tokio stream and waits for
		/// a pattern match.
		///
		/// This function takes a readable tokio stream (e.g. from a child process `ChildStderr` or
		/// `ChildStdout`) and a `Regex` pattern. It reads lines from the provided stream and checks
		/// each line against the given pattern. The function returns as soon as a line matching the
		/// pattern is found.
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
		/// * `Err(String)` if the stream ends without any lines matching the pattern, or if an
		///   error occurs while reading the stream.
		///
		/// # Example
		///
		/// ```
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
		async fn wait_for_stream_pattern_match<R>(stream: R, re: Regex) -> Result<(), String>
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
			Err(String::from("Stderr stream ended without any lines matching the regex."))
		}

		fn start_node() -> Child {
			Command::new(cargo_bin("substrate"))
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.args(&["--dev", "--tmp", "--ws-port=45789", "--no-hardware-benchmarks"])
				.spawn()
				.unwrap()
		}

		fn start_follow(ws_url: &str) -> tokio::process::Child {
			tokio::process::Command::new(cargo_bin("substrate"))
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.args(&["try-runtime", "--runtime=existing"])
				.args(&["follow-chain", format!("--uri={}", ws_url).as_str()])
				.spawn()
				.unwrap()
		}

		// Start a node and wait for it to begin finalizing blocks
		let mut node = start_node();
		let ws_url = common::extract_info_from_output(node.stderr.take().unwrap()).0.ws_url;
		common::wait_n_finalized_blocks(1, &ws_url).await;

		// Kick off the follow-chain process and wait for it to process at least 3 blocks.
		let mut follow = start_follow(&ws_url);
		let re = Regex::new(r#".*executed block ([3-9]|[1-9]\d+).*"#).unwrap();
		let matched = wait_for_stream_pattern_match(follow.stderr.take().unwrap(), re).await;

		// Assert that the follow-chain process has followed at least 5 blocks.
		assert!(matches!(matched, Ok(_)));

		// Sanity check: node is still running
		assert!(node.try_wait().unwrap().is_none());
	})
	.await;
}
