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
	block_building_info::BlockBuildingInfoProvider, build_executor, full_extensions,
	rpc_err_handler, state_machine_call, BlockT, LiveState, SharedParams, State,
};
use parity_scale_codec::{Decode, Encode};
use sc_cli::Result;
use sc_executor::{sp_wasm_interface::HostFunctions, WasmExecutor};
use serde::de::DeserializeOwned;
use sp_core::H256;
use sp_inherents::{InherentData, InherentDataProvider};
use sp_runtime::{
	traits::{HashingFor, Header, NumberFor, One},
	Digest,
};
use sp_state_machine::TestExternalities;
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi};

/// Configurations of the [`crate::Command::FastForward`].
#[derive(Debug, Clone, clap::Parser)]
pub struct FastForwardCmd {
	/// How many blocks should be processed. If `None`, then blocks will be produced and processed
	/// in a loop.
	#[arg(long)]
	n_blocks: Option<u64>,

	/// The state type to use.
	#[command(subcommand)]
	state: State,

	/// The ws uri from which to fetch the block.
	///
	/// If `state` is `Live`, this is ignored. Otherwise, it must not be empty.
	#[arg(long, value_parser = crate::parse::url)]
	block_ws_uri: Option<String>,

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
	try_state: frame_try_runtime::TryStateSelect,
}

impl FastForwardCmd {
	fn block_ws_uri(&self) -> &str {
		match self.state {
			State::Live(LiveState { ref uri, .. }) => &uri,
			_ => self
				.block_ws_uri
				.as_ref()
				.expect("Either `--block-uri` must be provided, or state must be `live`"),
		}
	}
}

/// Read the block number corresponding to `hash` with an RPC call to `ws_uri`.
async fn get_block_number<Block: BlockT>(
	hash: Block::Hash,
	ws_uri: &str,
) -> Result<NumberFor<Block>>
where
	Block::Header: DeserializeOwned,
{
	let rpc = ws_client(ws_uri).await?;
	Ok(ChainApi::<(), Block::Hash, Block::Header, ()>::header(&rpc, Some(hash))
		.await
		.map_err(rpc_err_handler)
		.and_then(|maybe_header| maybe_header.ok_or("header_not_found").map(|h| *h.number()))?)
}

/// Call `method` with `data` and return the result. `externalities` will not change.
fn dry_run<T: Decode, Block: BlockT, HostFns: HostFunctions>(
	externalities: &TestExternalities<HashingFor<Block>>,
	executor: &WasmExecutor<HostFns>,
	method: &'static str,
	data: &[u8],
) -> Result<T> {
	let (_, result) = state_machine_call::<Block, HostFns>(
		externalities,
		executor,
		method,
		data,
		full_extensions(executor.clone()),
	)?;

	Ok(<T>::decode(&mut &*result)?)
}

/// Call `method` with `data` and actually save storage changes to `externalities`.
async fn run<Block: BlockT, HostFns: HostFunctions>(
	externalities: &mut TestExternalities<HashingFor<Block>>,
	executor: &WasmExecutor<HostFns>,
	method: &'static str,
	data: &[u8],
) -> Result<()> {
	let (mut changes, _) = state_machine_call::<Block, HostFns>(
		externalities,
		executor,
		method,
		data,
		full_extensions(executor.clone()),
	)?;

	let storage_changes =
		changes.drain_storage_changes(&externalities.backend, externalities.state_version)?;

	externalities
		.backend
		.apply_transaction(storage_changes.transaction_storage_root, storage_changes.transaction);

	Ok(())
}

/// Produce next empty block.
async fn next_empty_block<
	Block: BlockT,
	HostFns: HostFunctions,
	BBIP: BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>>,
>(
	externalities: &mut TestExternalities<HashingFor<Block>>,
	executor: &WasmExecutor<HostFns>,
	parent_height: NumberFor<Block>,
	parent_hash: Block::Hash,
	block_building_info_provider: &Option<BBIP>,
	previous_block_building_info: Option<(InherentData, Digest)>,
) -> Result<(Block, Option<(InherentData, Digest)>)> {
	let (maybe_inherent_data, pre_digest) = match &block_building_info_provider {
		None => (None, Default::default()),
		Some(bbip) => {
			let (inherent_data_provider, pre_digest) = bbip
				.get_inherent_providers_and_pre_digest(parent_hash, previous_block_building_info)
				.await?;
			let inherent_data = inherent_data_provider
				.create_inherent_data()
				.await
				.map_err(|e| sc_cli::Error::Input(format!("I don't know how to convert {e:?}")))?;

			(Some(inherent_data), Digest { logs: pre_digest })
		},
	};

	let header = Block::Header::new(
		parent_height + One::one(),
		Default::default(),
		Default::default(),
		parent_hash,
		pre_digest.clone(),
	);
	let mut extrinsics = <Vec<Block::Extrinsic>>::new();

	run::<Block, _>(externalities, executor, "Core_initialize_block", &header.encode()).await?;

	if let Some(ref inherent_data) = maybe_inherent_data {
		extrinsics = dry_run::<Vec<Block::Extrinsic>, Block, _>(
			externalities,
			executor,
			"BlockBuilder_inherent_extrinsics",
			&inherent_data.encode(),
		)?;
	}

	for xt in &extrinsics {
		run::<Block, _>(externalities, executor, "BlockBuilder_apply_extrinsic", &xt.encode())
			.await?;
	}

	let header = dry_run::<Block::Header, Block, _>(
		externalities,
		executor,
		"BlockBuilder_finalize_block",
		&[0u8; 0],
	)?;

	run::<Block, _>(externalities, executor, "BlockBuilder_finalize_block", &[0u8; 0]).await?;

	Ok((Block::new(header, extrinsics), (maybe_inherent_data.map(|id| (id, pre_digest)))))
}

pub(crate) async fn fast_forward<Block, HostFns, BBIP>(
	shared: SharedParams,
	command: FastForwardCmd,
	block_building_info_provider: Option<BBIP>,
) -> Result<()>
where
	Block: BlockT<Hash = H256> + DeserializeOwned,
	Block::Header: DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	HostFns: HostFunctions,
	BBIP: BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>>,
{
	let executor = build_executor::<HostFns>(&shared);
	let ext = command.state.into_ext::<Block, HostFns>(&shared, &executor, None, true).await?;

	let mut last_block_hash = ext.block_hash;
	let mut last_block_number =
		get_block_number::<Block>(last_block_hash, command.block_ws_uri()).await?;
	let mut prev_block_building_info = None;

	let mut ext = ext.inner_ext;

	for _ in 1..=command.n_blocks.unwrap_or(u64::MAX) {
		// We are saving state before we overwrite it while producing new block.
		let backend = ext.as_backend();

		log::info!("Producing new empty block at height {:?}", last_block_number + One::one());

		let (next_block, new_block_building_info) = next_empty_block::<Block, HostFns, BBIP>(
			&mut ext,
			&executor,
			last_block_number,
			last_block_hash,
			&block_building_info_provider,
			prev_block_building_info,
		)
		.await?;

		log::info!("Produced a new block: {:?}", next_block.header());

		// And now we restore previous state.
		ext.backend = backend;

		let state_root_check = true;
		let signature_check = true;
		let payload =
			(next_block.clone(), state_root_check, signature_check, command.try_state.clone())
				.encode();
		run::<Block, _>(&mut ext, &executor, "TryRuntime_execute_block", &payload).await?;

		log::info!("Executed the new block");

		prev_block_building_info = new_block_building_info;
		last_block_hash = next_block.hash();
		last_block_number += One::one();
	}

	Ok(())
}
