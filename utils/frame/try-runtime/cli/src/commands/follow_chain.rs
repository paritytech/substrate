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
	build_executor, ensure_matching_spec, extract_code, full_extensions, local_spec, parse,
	state_machine_call_with_proof, SharedParams, LOG_TARGET,
};
use parity_scale_codec::{Decode, Encode};
use remote_externalities::{Builder, Mode, OnlineConfig};
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use serde::{de::DeserializeOwned, Serialize};
use sp_core::H256;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi, FinalizedHeaders, Subscription, WsClient};

const SUB: &str = "chain_subscribeFinalizedHeads";
const UN_SUB: &str = "chain_unsubscribeFinalizedHeads";

/// Configurations of the [`Command::FollowChain`].
#[derive(Debug, Clone, clap::Parser)]
pub struct FollowChainCmd {
	/// The url to connect to.
	#[arg(short, long, value_parser = parse::url)]
	uri: String,

	/// If set, then the state root check is enabled.
	#[arg(long)]
	state_root_check: bool,

	/// Which try-state targets to execute when running this command.
	///
	/// Expected values:
	/// - `all`
	/// - `none`
	/// - A comma separated list of pallets, as per pallet names in `construct_runtime!()` (e.g.
	///   `Staking, System`).
	/// - `rr-[x]` where `[x]` is a number. Then, the given number of pallets are checked in a
	///   round-robin fashion.
	#[arg(long, default_value = "none")]
	try_state: frame_try_runtime::TryStateSelect,

	/// If present, a single connection to a node will be kept and reused for fetching blocks.
	#[arg(long)]
	keep_connection: bool,
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

pub(crate) async fn follow_chain<Block, ExecDispatch>(
	shared: SharedParams,
	command: FollowChainCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT<Hash = H256> + DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let mut maybe_state_ext = None;
	let (rpc, subscription) = start_subscribing::<Block::Header>(&command.uri).await?;

	let (code_key, code) = extract_code(&config.chain_spec)?;
	let executor = build_executor::<ExecDispatch>(&shared, &config);
	let execution = shared.execution;

	let mut finalized_headers: FinalizedHeaders<Block, _, _> =
		FinalizedHeaders::new(&rpc, subscription);

	while let Some(header) = finalized_headers.next().await {
		let hash = header.hash();
		let number = header.number();

		let block: Block = ChainApi::<(), Block::Hash, Block::Header, _>::block(&rpc, Some(hash))
			.await
			.unwrap()
			.unwrap();

		log::debug!(
			target: LOG_TARGET,
			"new block event: {:?} => {:?}, extrinsics: {}",
			hash,
			number,
			block.extrinsics().len()
		);

		// create an ext at the state of this block, whatever is the first subscription event.
		if maybe_state_ext.is_none() {
			let builder = Builder::<Block>::new()
				.mode(Mode::Online(OnlineConfig {
					transport: command.uri.clone().into(),
					at: Some(*header.parent_hash()),
					..Default::default()
				}))
				.state_version(shared.state_version);

			let new_ext = builder
				.inject_hashed_key_value(&[(code_key.clone(), code.clone())])
				.build()
				.await?;
			log::info!(
				target: LOG_TARGET,
				"initialized state externalities at {:?}, storage root {:?}",
				number,
				new_ext.as_backend().root()
			);

			let (expected_spec_name, expected_spec_version, spec_state_version) =
				local_spec::<Block, ExecDispatch>(&new_ext, &executor);
			ensure_matching_spec::<Block>(
				command.uri.clone(),
				expected_spec_name,
				expected_spec_version,
				shared.no_spec_check_panic,
			)
			.await;

			maybe_state_ext = Some((new_ext, spec_state_version));
		}

		let (state_ext, spec_state_version) =
			maybe_state_ext.as_mut().expect("state_ext either existed or was just created");

		let (mut changes, encoded_result) = state_machine_call_with_proof::<Block, ExecDispatch>(
			state_ext,
			&executor,
			execution,
			"TryRuntime_execute_block",
			(block, command.state_root_check, command.try_state.clone()).encode().as_ref(),
			full_extensions(),
		)?;

		let consumed_weight = <sp_weights::Weight as Decode>::decode(&mut &*encoded_result)
			.map_err(|e| format!("failed to decode weight: {:?}", e))?;

		let storage_changes = changes
			.drain_storage_changes(
				&state_ext.backend,
				&mut Default::default(),
				// Note that in case a block contains a runtime upgrade,
				// state version could potentially be incorrect here,
				// this is very niche and would only result in unaligned
				// roots, so this use case is ignored for now.
				*spec_state_version,
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
