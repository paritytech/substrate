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
	build_executor, full_extensions, rpc_err_handler, state_machine_call_with_proof, LiveState,
	SharedParams, State, LOG_TARGET,
};
use parity_scale_codec::Encode;
use sc_executor::sp_wasm_interface::HostFunctions;
use sp_rpc::{list::ListOrValue, number::NumberOrHex};
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi};

/// Configurations of the [`crate::Command::ExecuteBlock`].
///
/// This will always call into `TryRuntime_execute_block`, which can optionally skip the state-root
/// check (useful for trying a unreleased runtime), and can execute runtime sanity checks as well.
#[derive(Debug, Clone, clap::Parser)]
pub struct ExecuteBlockCmd {
	/// Which try-state targets to execute when running this command.
	///
	/// Expected values:
	/// - `all`
	/// - `none`
	/// - A comma separated list of pallets, as per pallet names in `construct_runtime!()` (e.g.
	///   `Staking, System`).
	/// - `rr-[x]` where `[x]` is a number. Then, the given number of pallets are checked in a
	///   round-robin fashion.
	#[arg(long, default_value = "all")]
	pub try_state: frame_try_runtime::TryStateSelect,

	/// The ws uri from which to fetch the block.
	///
	/// This will always fetch the next block of whatever `state` is referring to, because this is
	/// the only sensible combination. In other words, if you have the state of block `n`, you
	/// should execute block `n+1` on top of it.
	///
	/// If `state` is `Live`, this can be ignored and the same uri is used for both.
	#[arg(
		long,
		value_parser = crate::parse::url
	)]
	pub block_ws_uri: Option<String>,

	/// The state type to use.
	#[command(subcommand)]
	pub state: State,
}

impl ExecuteBlockCmd {
	fn block_ws_uri<Block: BlockT>(&self) -> String
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.block_ws_uri, &self.state) {
			(Some(block_ws_uri), State::Snap { .. }) => block_ws_uri.to_owned(),
			(Some(block_ws_uri), State::Live { .. }) => {
				log::error!(target: LOG_TARGET, "--block-uri is provided while state type is live, Are you sure you know what you are doing?");
				block_ws_uri.to_owned()
			},
			(None, State::Live(LiveState { uri, .. })) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--block-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub(crate) async fn execute_block<Block, HostFns>(
	shared: SharedParams,
	command: ExecuteBlockCmd,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
	Block::Hash: serde::de::DeserializeOwned,
	Block::Header: serde::de::DeserializeOwned,
	<NumberFor<Block> as TryInto<u64>>::Error: Debug,
	HostFns: HostFunctions,
{
	let executor = build_executor::<HostFns>(&shared);
	let ext = command.state.into_ext::<Block, HostFns>(&shared, &executor, None).await?;

	// get the block number associated with this block.
	let block_ws_uri = command.block_ws_uri::<Block>();
	let rpc = ws_client(&block_ws_uri).await?;
	let next_hash = next_hash_of::<Block>(&rpc, ext.block_hash).await?;

	log::info!(target: LOG_TARGET, "fetching next block: {:?} ", next_hash);

	let block = ChainApi::<(), Block::Hash, Block::Header, SignedBlock<Block>>::block(
		&rpc,
		Some(next_hash),
	)
	.await
	.map_err(rpc_err_handler)?
	.expect("header exists, block should also exist; qed")
	.block;

	// A digest item gets added when the runtime is processing the block, so we need to pop
	// the last one to be consistent with what a gossiped block would contain.
	let (mut header, extrinsics) = block.deconstruct();
	header.digest_mut().pop();
	let block = Block::new(header, extrinsics);

	// for now, hardcoded for the sake of simplicity. We might customize them one day.
	let state_root_check = false;
	let signature_check = false;
	let payload = (block.clone(), state_root_check, signature_check, command.try_state).encode();

	let _ = state_machine_call_with_proof::<Block, HostFns>(
		&ext,
		&executor,
		"TryRuntime_execute_block",
		&payload,
		full_extensions(),
		shared.export_proof,
	)?;

	Ok(())
}

pub(crate) async fn next_hash_of<Block: BlockT>(
	rpc: &substrate_rpc_client::WsClient,
	hash: Block::Hash,
) -> sc_cli::Result<Block::Hash>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Header: serde::de::DeserializeOwned,
{
	let number = ChainApi::<(), Block::Hash, Block::Header, ()>::header(rpc, Some(hash))
		.await
		.map_err(rpc_err_handler)
		.and_then(|maybe_header| maybe_header.ok_or("header_not_found").map(|h| *h.number()))?;

	let next = number + sp_runtime::traits::One::one();

	let next_hash = match ChainApi::<(), Block::Hash, Block::Header, ()>::block_hash(
		rpc,
		Some(ListOrValue::Value(NumberOrHex::Number(
			next.try_into().map_err(|_| "failed to convert number to block number")?,
		))),
	)
	.await
	.map_err(rpc_err_handler)?
	{
		ListOrValue::Value(t) => t.expect("value passed in; value comes out; qed"),
		_ => unreachable!(),
	};

	Ok(next_hash)
}
