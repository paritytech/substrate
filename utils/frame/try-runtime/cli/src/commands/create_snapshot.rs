// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{hash_of, LiveState, LOG_TARGET};
use remote_externalities::{Builder, Mode, OnlineConfig, SnapshotConfig};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, StateApi};

/// Configurations of the [`Command::CreateSnapshot`].
#[derive(Debug, Clone, clap::Parser)]
pub struct CreateSnapshotCmd {
	/// The source of the snapshot. Must be a remote node.
	#[clap(flatten)]
	from: LiveState,

	/// The snapshot path to write to.
	///
	/// If not provided `<spec-name>-<spec-version>@<block-hash>.snap` will be used.
	snapshot_path: Option<String>,
}

/// inner command for `Command::CreateSnapshot`.
pub(crate) async fn create_snapshot<Block>(command: CreateSnapshotCmd) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr + serde::de::DeserializeOwned,
	Block::Header: serde::de::DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
{
	let snapshot_path = command.snapshot_path;
	let command = command.from;

	let at = match command.at {
		Some(ref at_str) => Some(hash_of::<Block>(at_str)?),
		None => None,
	};

	let path = match snapshot_path {
		Some(path) => path,
		None => {
			let rpc = ws_client(&command.uri).await.unwrap();
			let remote_spec = StateApi::<Block::Hash>::runtime_version(&rpc, None).await.unwrap();
			let path_str = format!(
				"{}-{}@{}.snap",
				remote_spec.spec_name.to_lowercase(),
				remote_spec.spec_version,
				command.at.clone().unwrap_or("latest".to_owned())
			);
			log::info!(target: LOG_TARGET, "snapshot path not provided (-s), using '{}'", path_str);
			path_str.into()
		},
	};

	let _ = Builder::<Block>::new()
		.mode(Mode::Online(OnlineConfig {
			at,
			state_snapshot: Some(SnapshotConfig::new(path)),
			pallets: command.pallet,
			transport: command.uri.into(),
			child_trie: command.child_tree,
			hashed_prefixes: vec![],
			hashed_keys: vec![],
			threads: command.threads,
		}))
		.build()
		.await?;

	Ok(())
}
