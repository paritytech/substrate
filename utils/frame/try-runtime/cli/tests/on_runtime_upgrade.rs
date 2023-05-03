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
	use std::{process, time::Duration, str::from_utf8};
	use substrate_cli_test_utils as common;
	use tokio::process::Command;

	#[tokio::test]
	async fn on_runtime_upgrade_works() {
		// Build substrate so binaries used in the test use the latest code.
		common::build_substrate(&["--features=try-runtime"]);

		common::run_with_timeout(Duration::from_secs(10*60), async move {
			let run_on_runtime_upgrade = |ws_url: String| async move {
				Command::new(cargo_bin("substrate"))
					.stdout(process::Stdio::piped())
					.stderr(process::Stdio::piped())
					.args(&["try-runtime", "--runtime=existing"])
                    .args(&["on-runtime-upgrade", "--checks=pre-and-post"])
					.args(&["live", format!("--uri={}", ws_url).as_str()])
					.kill_on_drop(true)
                    .output()
					.await
					.unwrap()
			};

			// Start a node and wait for it to begin finalizing blocks
            let (_child, ws_url) = common::start_node();
			common::wait_n_finalized_blocks(1, &ws_url).await.unwrap();

			// Kick off the on-runtime-upgrade process and wait for the on-runtime-upgrade to succeed.
			let on_runtime_upgrade = run_on_runtime_upgrade(ws_url).await;
            let re = Regex::new(r"TryRuntime_on_runtime_upgrade executed without errors").unwrap();
            let error_re = Regex::new(r"(?i)error").unwrap();
            let stderr_str = from_utf8(&on_runtime_upgrade.stderr).unwrap();
            
            if error_re.is_match(stderr_str) {
                // Output the line where the error matched in the stderr.
                let stderr_str_lines: Vec<&str> = stderr_str.lines().collect();
                for (_, line) in stderr_str_lines.iter().enumerate() {
                    if error_re.is_match(line) {
                        println!("{}", line);
                        break;
                    }
                }
                panic!("Error found in stderr");
            }
            
            assert!(re.is_match(stderr_str));
            assert!(on_runtime_upgrade.status.success());
        })
		.await;
	}
}
