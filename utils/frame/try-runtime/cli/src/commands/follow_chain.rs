// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	build_executor, full_extensions, parse, rpc_err_handler, state_machine_call_with_proof,
	LiveState, SharedParams, State, LOG_TARGET,
};
use parity_scale_codec::{Decode, Encode};
use sc_executor::sp_wasm_interface::HostFunctions;
use serde::{de::DeserializeOwned, Serialize};
use sp_core::H256;
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi, FinalizedHeaders, Subscription, WsClient};

const SUB: &str = "chain_subscribeFinalizedHeads";
const UN_SUB: &str = "chain_unsubscribeFinalizedHeads";

/// Configurations of the [`crate::Command::FollowChain`].
#[derive(Debug, Clone, clap::Parser)]
pub struct FollowChainCmd {
	/// The url to connect to.
	#[arg(short, long, value_parser = parse::url)]
	pub uri: String,

	/// If set, then the state root check is enabled.
	#[arg(long)]
	pub state_root_check: bool,

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

	/// If present, a single connection to a node will be kept and reused for fetching blocks.
	#[arg(long)]
	pub keep_connection: bool,
}

/// Start listening for with `SUB` at `url`.
///
/// Returns a pair `(client, subscription)` - `subscription` alone will be useless, because it
/// relies on the related alive `client`.
async fn start_subscribing<Header: DeserializeOwned + Serialize + Send + Sync + 'static>(
	url: &str,
) -> sc_cli::Result<(WsClient, Subscription<Header>)> {
	let client = ws_client(url).await.map_err(|e| sc_cli::Error::Application(e.into()))?;

	log::info!(target: LOG_TARGET, "subscribing to {:?} / {:?}", SUB, UN_SUB);

	let sub = ChainApi::<(), (), Header, ()>::subscribe_finalized_heads(&client)
		.await
		.map_err(|e| sc_cli::Error::Application(e.into()))?;
	Ok((client, sub))
}

pub(crate) async fn follow_chain<Block, HostFns>(
	shared: SharedParams,
	command: FollowChainCmd,
) -> sc_cli::Result<()>
where
	Block: BlockT<Hash = H256> + DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	HostFns: HostFunctions,
{
	let (rpc, subscription) = start_subscribing::<Block::Header>(&command.uri).await?;
	let mut finalized_headers: FinalizedHeaders<Block, _, _> =
		FinalizedHeaders::new(&rpc, subscription);

	let mut maybe_state_ext = None;
	let executor = build_executor::<HostFns>(&shared);

	while let Some(header) = finalized_headers.next().await {
		let hash = header.hash();
		let number = header.number();

		let block =
			ChainApi::<(), Block::Hash, Block::Header, SignedBlock<Block>>::block(&rpc, Some(hash))
				.await
				.or_else(|e| {
					if matches!(e, substrate_rpc_client::Error::ParseError(_)) {
						log::error!(
							"failed to parse the block format of remote against the local \
						codebase. The block format has changed, and follow-chain cannot run in \
						this case. Try running this command in a branch of your codebase that has \
						the same block format as the remote chain. For now, we replace the block with an empty one"
						);
					}
					Err(rpc_err_handler(e))
				})?
				.expect("if header exists, block should also exist.")
				.block;

		log::debug!(
			target: LOG_TARGET,
			"new block event: {:?} => {:?}, extrinsics: {}",
			hash,
			number,
			block.extrinsics().len()
		);

		// create an ext at the state of this block, whatever is the first subscription event.
		if maybe_state_ext.is_none() {
			let state = State::Live(LiveState {
				uri: command.uri.clone(),
				// a bit dodgy, we have to un-parse the has to a string again and re-parse it
				// inside.
				at: Some(hex::encode(header.parent_hash().encode())),
				pallet: vec![],
				child_tree: true,
			});
			let ext = state.into_ext::<Block, HostFns>(&shared, &executor, None, true).await?;
			maybe_state_ext = Some(ext);
		}

		let state_ext =
			maybe_state_ext.as_mut().expect("state_ext either existed or was just created");

		let result = state_machine_call_with_proof::<Block, HostFns>(
			state_ext,
			&executor,
			"TryRuntime_execute_block",
			(block, command.state_root_check, command.try_state.clone()).encode().as_ref(),
			full_extensions(),
			shared
				.export_proof
				.as_ref()
				.map(|path| path.as_path().join(&format!("{}.json", number))),
		);

		if let Err(why) = result {
			log::error!(
				target: LOG_TARGET,
				"failed to execute block {:?} due to {:?}",
				number,
				why
			);
			continue
		}

		let (mut changes, encoded_result) = result.expect("checked to be Ok; qed");

		let consumed_weight = <sp_weights::Weight as Decode>::decode(&mut &*encoded_result)
			.map_err(|e| format!("failed to decode weight: {:?}", e))?;

		let storage_changes = changes
			.drain_storage_changes(
				&state_ext.backend,
				&mut Default::default(),
				// Note that in case a block contains a runtime upgrade, state version could
				// potentially be incorrect here, this is very niche and would only result in
				// unaligned roots, so this use case is ignored for now.
				state_ext.state_version,
			)
			.unwrap();

		state_ext.backend.apply_transaction(
			storage_changes.transaction_storage_root,
			storage_changes.transaction,
		);

		log::info!(
			target: LOG_TARGET,
			"executed block {}, consumed weight {}, new storage root {:?}",
			number,
			consumed_weight,
			state_ext.as_backend().root(),
		);
	}

	log::error!(target: LOG_TARGET, "ws subscription must have terminated.");
	Ok(())
}
