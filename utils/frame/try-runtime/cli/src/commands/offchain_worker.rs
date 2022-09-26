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
	parse, state_machine_call, SharedParams, State, LOG_TARGET,
};
use parity_scale_codec::Encode;
use remote_externalities::rpc_api;
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use sp_core::storage::well_known_keys;
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{fmt::Debug, str::FromStr};

/// Configurations of the [`Command::OffchainWorker`].
#[derive(Debug, Clone, clap::Parser)]
pub struct OffchainWorkerCmd {
	/// Overwrite the wasm code in state or not.
	#[clap(long)]
	overwrite_wasm_code: bool,

	/// The block hash at which to fetch the header.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::at` is. Only use this (with care) when combined with a snapshot.
	#[clap(
		long,
		multiple_values = false,
		parse(try_from_str = parse::hash)
	)]
	header_at: Option<String>,

	/// The ws uri from which to fetch the header.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[clap(
		long,
		multiple_values = false,
		parse(try_from_str = parse::url)
	)]
	header_ws_uri: Option<String>,

	/// The state type to use.
	#[clap(subcommand)]
	pub state: State,
}

impl OffchainWorkerCmd {
	fn header_at<Block: BlockT>(&self) -> sc_cli::Result<Block::Hash>
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		match (&self.header_at, &self.state) {
			(Some(header_at), State::Snap { .. }) => hash_of::<Block>(header_at),
			(Some(header_at), State::Live { .. }) => {
				log::error!(target: LOG_TARGET, "--header-at is provided while state type is live, this will most likely lead to a nonsensical result.");
				hash_of::<Block>(header_at)
			},
			(None, State::Live { at: Some(at), .. }) => hash_of::<Block>(at),
			_ => {
				panic!("either `--header-at` must be provided, or state must be `live` with a proper `--at`");
			},
		}
	}

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
			(None, State::Live { uri, .. }) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--header-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub(crate) async fn offchain_worker<Block, ExecDispatch>(
	shared: SharedParams,
	command: OffchainWorkerCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: serde::de::DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let executor = build_executor(&shared, &config);
	let execution = shared.execution;

	let header_at = command.header_at::<Block>()?;
	let header_ws_uri = command.header_ws_uri::<Block>();

	let rpc_service = rpc_api::RpcService::new(header_ws_uri.clone(), false).await?;
	let header = rpc_service.get_header::<Block>(header_at).await?;
	log::info!(
		target: LOG_TARGET,
		"fetched header from {:?}, block number: {:?}",
		header_ws_uri,
		header.number()
	);

	let ext = {
		let builder = command.state.builder::<Block>()?.state_version(shared.state_version);

		let builder = if command.overwrite_wasm_code {
			log::info!(
				target: LOG_TARGET,
				"replacing the in-storage :code: with the local code from {}'s chain_spec (your local repo)",
				config.chain_spec.name(),
			);
			let (code_key, code) = extract_code(&config.chain_spec)?;
			builder.inject_hashed_key_value(&[(code_key, code)])
		} else {
			builder.inject_hashed_key(well_known_keys::CODE)
		};

		builder.build().await?
	};

	let (expected_spec_name, expected_spec_version, _) =
		local_spec::<Block, ExecDispatch>(&ext, &executor);
	ensure_matching_spec::<Block>(
		header_ws_uri,
		expected_spec_name,
		expected_spec_version,
		shared.no_spec_check_panic,
	)
	.await;

	let _ = state_machine_call::<Block, ExecDispatch>(
		&ext,
		&executor,
		execution,
		"OffchainWorkerApi_offchain_worker",
		header.encode().as_ref(),
		full_extensions(),
	)?;

	log::info!(target: LOG_TARGET, "OffchainWorkerApi_offchain_worker executed without errors.");

	Ok(())
}
