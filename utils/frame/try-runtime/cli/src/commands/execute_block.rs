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
	build_executor, ensure_matching_spec, extract_code, full_extensions, hash_of, local_spec,
	state_machine_call_with_proof, SharedParams, State, LOG_TARGET,
};
use remote_externalities::rpc_api;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::storage::well_known_keys;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use std::{fmt::Debug, str::FromStr};

/// Configurations of the [`Command::ExecuteBlock`].
#[derive(Debug, Clone, structopt::StructOpt)]
pub struct ExecuteBlockCmd {
	/// Overwrite the wasm code in state or not.
	#[structopt(long)]
	overwrite_wasm_code: bool,

	/// If set, then the state root check is disabled by the virtue of calling into
	/// `TryRuntime_execute_block_no_check` instead of
	/// `Core_execute_block`.
	#[structopt(long)]
	no_check: bool,

	/// The block hash at which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::at` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = crate::parse::hash)
	)]
	block_at: Option<String>,

	/// The ws uri from which to fetch the block.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[structopt(
		long,
		multiple = false,
		parse(try_from_str = crate::parse::url)
	)]
	block_ws_uri: Option<String>,

	/// The state type to use.
	///
	/// For this command only, if the `live` is used, then state of the parent block is fetched.
	///
	/// If `block_at` is provided, then the [`State::Live::at`] is being ignored.
	#[structopt(subcommand)]
	state: State,
}

impl ExecuteBlockCmd {
	fn block_at<Block: BlockT>(&self) -> sc_cli::Result<Block::Hash>
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.block_at, &self.state) {
			(Some(block_at), State::Snap { .. }) => hash_of::<Block>(&block_at),
			(Some(block_at), State::Live { .. }) => {
				log::warn!(target: LOG_TARGET, "--block-at is provided while state type is live. the `Live::at` will be ignored");
				hash_of::<Block>(&block_at)
			},
			(None, State::Live { at: Some(at), .. }) => hash_of::<Block>(&at),
			_ => {
				panic!("either `--block-at` must be provided, or state must be `live with a proper `--at``");
			},
		}
	}

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
			(None, State::Live { uri, .. }) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--block-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub(crate) async fn execute_block<Block, ExecDispatch>(
	shared: SharedParams,
	command: ExecuteBlockCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let executor = build_executor::<ExecDispatch>(&shared, &config);
	let execution = shared.execution;

	let block_at = command.block_at::<Block>()?;
	let block_ws_uri = command.block_ws_uri::<Block>();
	let block: Block = rpc_api::get_block::<Block, _>(block_ws_uri.clone(), block_at).await?;
	let parent_hash = block.header().parent_hash();
	log::info!(
		target: LOG_TARGET,
		"fetched block from {:?}, parent_hash to fetch the state {:?}",
		block_ws_uri,
		parent_hash
	);

	let ext = {
		let builder = command
			.state
			.builder::<Block>()?
			// make sure the state is being build with the parent hash, if it is online.
			.overwrite_online_at(parent_hash.to_owned());

		let builder = if command.overwrite_wasm_code {
			let (code_key, code) = extract_code(&config.chain_spec)?;
			builder.inject_hashed_key_value(&[(code_key, code)])
		} else {
			builder.inject_hashed_key(well_known_keys::CODE)
		};

		builder.build().await?
	};

	// A digest item gets added when the runtime is processing the block, so we need to pop
	// the last one to be consistent with what a gossiped block would contain.
	let (mut header, extrinsics) = block.deconstruct();
	header.digest_mut().pop();
	let block = Block::new(header, extrinsics);

	let (expected_spec_name, expected_spec_version, _) =
		local_spec::<Block, ExecDispatch>(&ext, &executor);
	ensure_matching_spec::<Block>(
		block_ws_uri.clone(),
		expected_spec_name,
		expected_spec_version,
		shared.no_spec_name_check,
	)
	.await;

	let _ = state_machine_call_with_proof::<Block, ExecDispatch>(
		&ext,
		&executor,
		execution,
		if command.no_check { "TryRuntime_execute_block_no_check" } else { "Core_execute_block" },
		block.encode().as_ref(),
		full_extensions(),
	)?;

	log::info!(target: LOG_TARGET, "Core_execute_block executed without errors.");

	Ok(())
}
