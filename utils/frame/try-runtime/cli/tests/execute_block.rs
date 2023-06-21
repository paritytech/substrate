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
use node_primitives::Hash;
use regex::Regex;
use std::{process, time::Duration};
use substrate_cli_test_utils as common;
use tokio::process::{Child, Command};

#[tokio::test]
async fn block_execution_works() {
	// Build substrate so binaries used in the test use the latest code.
	common::build_substrate(&["--features=try-runtime"]);

	common::run_with_timeout(Duration::from_secs(60), async move {
		fn execute_block(ws_url: &str, at: Hash) -> Child {
			Command::new(cargo_bin("substrate"))
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.args(&["try-runtime", "--runtime=existing"])
				.args(&["execute-block"])
				.args(&["live", format!("--uri={}", ws_url).as_str()])
				.args(&["--at", format!("{:?}", at).as_str()])
				.kill_on_drop(true)
				.spawn()
				.unwrap()
		}

		// Start a node and wait for it to begin finalizing blocks
		let mut node = common::KillChildOnDrop(common::start_node());
		let ws_url = common::extract_info_from_output(node.stderr.take().unwrap()).0.ws_url;
		common::wait_n_finalized_blocks(3, &ws_url).await;

		let block_number = 1;
		let block_hash = common::block_hash(block_number, &ws_url).await.unwrap();

		// Try to execute the block.
		let mut block_execution = execute_block(&ws_url, block_hash);

		// The execute-block command is actually executing the next block.
		let expected_output =
			format!(r#".*Block #{} successfully executed"#, block_number.saturating_add(1));
		let re = Regex::new(expected_output.as_str()).unwrap();
		let matched =
			common::wait_for_stream_pattern_match(block_execution.stderr.take().unwrap(), re).await;

		// Assert that the block-execution process has executed a block.
		assert!(matched.is_ok());
	})
	.await;
}
