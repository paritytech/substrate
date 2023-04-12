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

#[cfg(feature = "try-runtime")]
mod tests {
	use assert_cmd::cargo::cargo_bin;
	use regex::Regex;
	use std::{
		process,
		str::from_utf8,
		time::Duration,
	};
	use substrate_cli_test_utils as common;
	use tokio::process::Command;

	#[tokio::test]
	async fn follow_chain_works() {
		// Build substrate so binaries used in the test use the latest code.
		common::build_substrate(&["--features=try-runtime"]);

		let n_blocks = 10;
		common::run_with_timeout(Duration::from_secs(10 * 60), async move {
			let run_fast_forward = |ws_url: String| async move {
				Command::new(cargo_bin("substrate"))
					.stdout(process::Stdio::piped())
					.stderr(process::Stdio::piped())
					.args(&["try-runtime", "--runtime=existing"])
					.args(&[
						"fast-forward",
						format!("--n-blocks={}", n_blocks).as_str(),
						"live",
						format!("--uri={}", ws_url).as_str(),
					])
					.kill_on_drop(true)
					.output()
					.await
					.unwrap()
			};

			// Start a node and wait for it to begin finalizing blocks
			let mut node = common::KillChildOnDrop(common::start_node());
			let ws_url = common::extract_info_from_output(node.stderr.take().unwrap()).0.ws_url;
			common::wait_n_finalized_blocks(1, &ws_url).await;

			// Make sure fast_forward logged "Executed the new block" the expected number of times
			// and exited successfully
			let fast_forward = run_fast_forward(ws_url).await;
			let re = Regex::new(
				format!(r#"(?:(?s).*Executed the new block.*\s*){}"#, n_blocks).as_str(),
			)
			.unwrap();
			assert!(re.is_match(from_utf8(&fast_forward.stderr).unwrap()));
			assert!(fast_forward.status.success());
		})
		.await;
	}
}
