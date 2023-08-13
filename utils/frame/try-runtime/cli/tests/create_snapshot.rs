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
use remote_externalities::{Builder, Mode, OfflineConfig, SnapshotConfig};
use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper};
use std::{
	path::{Path, PathBuf},
	process,
	time::Duration,
};
use substrate_cli_test_utils as common;
use tokio::process::{Child, Command};

type Block = RawBlock<ExtrinsicWrapper<Hash>>;

#[tokio::test]
async fn create_snapshot_works() {
	// Build substrate so binaries used in the test use the latest code.
	common::build_substrate(&["--features=try-runtime"]);

	let temp_dir = tempfile::Builder::new()
		.prefix("try-runtime-cli-test-dir")
		.tempdir()
		.expect("Failed to create a tempdir");
	let snap_file_path = temp_dir.path().join("snapshot.snap");

	common::run_with_timeout(Duration::from_secs(60), async move {
		fn create_snapshot(ws_url: &str, snap_file: &PathBuf, at: Hash) -> Child {
			Command::new(cargo_bin("substrate-node"))
				.stdout(process::Stdio::piped())
				.stderr(process::Stdio::piped())
				.args(&["try-runtime", "--runtime=existing"])
				.args(&["create-snapshot", format!("--uri={}", ws_url).as_str()])
				.arg(snap_file)
				.args(&["--at", format!("{:?}", at).as_str()])
				.kill_on_drop(true)
				.spawn()
				.unwrap()
		}

		// Start a node and wait for it to begin finalizing blocks
		let mut node = common::KillChildOnDrop(common::start_node());
		let ws_url = common::extract_info_from_output(node.stderr.take().unwrap()).0.ws_url;
		common::wait_n_finalized_blocks(3, &ws_url).await;

		let block_number = 2;
		let block_hash = common::block_hash(block_number, &ws_url).await.unwrap();

		// Try to create a snapshot.
		let mut snapshot_creation = create_snapshot(&ws_url, &snap_file_path, block_hash);

		let re = Regex::new(r#".*writing snapshot of (\d+) bytes to .*"#).unwrap();
		let matched =
			common::wait_for_stream_pattern_match(snapshot_creation.stderr.take().unwrap(), re)
				.await;

		// Assert that the snapshot creation succeded.
		assert!(matched.is_ok(), "Failed to create snapshot");

		let snapshot_is_on_disk = Path::new(&snap_file_path).exists();
		assert!(snapshot_is_on_disk, "Snapshot was not written to disk");

		// Try and load the snapshot we have created by running `create-snapshot`.
		let snapshot_loading_result = Builder::<Block>::new()
			.mode(Mode::Offline(OfflineConfig {
				state_snapshot: SnapshotConfig { path: snap_file_path },
			}))
			.build()
			.await;

		assert!(snapshot_loading_result.is_ok(), "Snapshot couldn't be loaded");
	})
	.await;
}
