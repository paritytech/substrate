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
#![cfg(feature = "try-runtime")]

use assert_cmd::cargo::cargo_bin;
use regex::Regex;
use std::{
	process::{self},
	time::Duration,
};
use substrate_cli_test_utils as common;
use tokio::process::{Child, Command};

#[tokio::test]
async fn follow_chain_works() {
	// Build substrate so binaries used in the test use the latest code.
	common::build_substrate(&["--features=try-runtime"]);

	common::run_with_timeout(Duration::from_secs(60), async move {
		fn start_follow(ws_url: &str) -> Child {
			Command::new(cargo_bin("substrate-node"))
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.args(&["try-runtime", "--runtime=existing"])
				.args(&["follow-chain", format!("--uri={}", ws_url).as_str()])
				.kill_on_drop(true)
				.spawn()
				.unwrap()
		}

		// Start a node and wait for it to begin finalizing blocks
		let mut node = common::KillChildOnDrop(common::start_node());
		let ws_url = common::extract_info_from_output(node.stderr.take().unwrap()).0.ws_url;
		common::wait_n_finalized_blocks(1, &ws_url).await;

		// Kick off the follow-chain process and wait for it to process at least 3 blocks.
		let mut follow = start_follow(&ws_url);
		let re = Regex::new(r#".*executed block ([3-9]|[1-9]\d+).*"#).unwrap();
		let matched =
			common::wait_for_stream_pattern_match(follow.stderr.take().unwrap(), re).await;

		// Assert that the follow-chain process has followed at least 3 blocks.
		assert!(matched.is_ok());
	})
	.await;
}
