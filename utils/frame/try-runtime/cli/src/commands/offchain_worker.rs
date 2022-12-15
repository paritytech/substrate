// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
	build_executor, commands::execute_block::next_hash_of, full_extensions, parse, rpc_err_handler,
	state_machine_call, LiveState, SharedParams, State, LOG_TARGET,
};
use parity_scale_codec::Encode;
use sc_executor::sp_wasm_interface::HostFunctions;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi};

/// Configurations of the [`crate::Command::OffchainWorker`].
#[derive(Debug, Clone, clap::Parser)]
pub struct OffchainWorkerCmd {
	/// The ws uri from which to fetch the header.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[arg(
		long,
		value_parser = parse::url
	)]
	pub header_ws_uri: Option<String>,

	/// The state type to use.
	#[command(subcommand)]
	pub state: State,
}

impl OffchainWorkerCmd {
	fn header_ws_uri<Block: BlockT>(&self) -> String
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.header_ws_uri, &self.state) {
			(Some(header_ws_uri), State::Snap { .. }) => header_ws_uri.to_owned(),
			(Some(header_ws_uri), State::Live { .. }) => {
				log::error!(target: LOG_TARGET, "--header-uri is provided while state type is live, this will most likely lead to a nonsensical result.");
				header_ws_uri.to_owned()
			},
			(None, State::Live(LiveState { uri, .. })) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--header-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub(crate) async fn offchain_worker<Block, HostFns>(
	shared: SharedParams,
	command: OffchainWorkerCmd,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Header: serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	HostFns: HostFunctions,
{
	let executor = build_executor(&shared);
	// we first build the externalities with the remote code.
	let ext = command.state.into_ext::<Block, HostFns>(&shared, &executor, None).await?;

	let header_ws_uri = command.header_ws_uri::<Block>();

	let rpc = ws_client(&header_ws_uri).await?;
	let next_hash = next_hash_of::<Block>(&rpc, ext.block_hash).await?;
	log::info!(target: LOG_TARGET, "fetching next header: {:?} ", next_hash);

	let header = ChainApi::<(), Block::Hash, Block::Header, ()>::header(&rpc, Some(next_hash))
		.await
		.map_err(rpc_err_handler)
		.map(|maybe_header| maybe_header.ok_or("Header does not exist"))??;
	let payload = header.encode();

	let _ = state_machine_call::<Block, HostFns>(
		&ext,
		&executor,
		"OffchainWorkerApi_offchain_worker",
		&payload,
		full_extensions(),
	)?;

	Ok(())
}
