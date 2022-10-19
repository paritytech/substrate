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

use crate::{
	build_executor, ensure_matching_spec, extract_code, full_extensions, local_spec, parse,
	state_machine_call_with_proof, LiveState, SharedParams, State, LOG_TARGET, hash_of,
};
use jsonrpsee::{
	core::{
		async_trait,
		client::{Client, Subscription, SubscriptionClientT},
	},
	ws_client::WsClientBuilder,
};
use parity_scale_codec::{Decode, Encode};
use remote_externalities::{
	rpc_api::{self, RpcService},
	Builder, Mode, OnlineConfig, SnapshotConfig,
};
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use serde::de::DeserializeOwned;
use sp_core::H256;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_weights::Weight;
use std::{collections::VecDeque, fmt::Debug, str::FromStr};

/// Configurations of the [`Command::CreateSnapshot`].
#[derive(Debug, Clone, clap::Parser)]
pub struct CreateSnapshotCmd {
	/// The source of the snapshot. Must be a remove node.
	#[clap(flatten)]
	from: LiveState,
}

pub(crate) async fn create_snapshot<Block>(
	shared: SharedParams,
	command: CreateSnapshotCmd,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
{
	assert!(command.from.snapshot_path.is_some(), "snapshot path must be provided.");

	let at = match command.from.at {
		Some(at_str) => Some(hash_of::<Block>(&at_str)?),
		None => None,
	};

	let _ = Builder::<Block>::new()
		.mode(Mode::Online(OnlineConfig {
			at,
			state_snapshot: command.from.snapshot_path.as_ref().map(SnapshotConfig::new),
			pallets: command.from.pallet,
			transport: command.from.uri.into(),
			child_trie: command.from.child_tree,
			hashed_prefixes: vec![],
			hashed_keys: vec![],
			threads: 8,
		}))
		.state_version(shared.state_version)
		.build()
		.await?;

	Ok(())
}
