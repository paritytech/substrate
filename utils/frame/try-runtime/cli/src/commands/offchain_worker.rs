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
	build_executor, build_wasm_executor, extract_code, full_extensions,
	hash_of, local_spec, parse, state_machine_call, LiveState, Runtime, SharedParams, State,
	LOG_TARGET,
};
use parity_scale_codec::Encode;
use sc_cli::RuntimeVersion;
use sc_executor::{
	sp_wasm_interface::{HostFunctionRegistry, HostFunctions},
	NativeExecutionDispatch, RuntimeVersionOf,
};
use sc_service::Configuration;
use sp_core::{
	storage::{well_known_keys, StorageKey},
	traits::ReadRuntimeVersion,
};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{fmt::Debug, str::FromStr};
use substrate_rpc_client::{ws_client, ChainApi};

/// Configurations of the [`Command::OffchainWorker`].
#[derive(Debug, Clone, clap::Parser)]
pub struct OffchainWorkerCmd {
	/// The block hash at which to fetch the header.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::at` is. Only use this (with care) when combined with a snapshot.
	#[arg(
		long,
		value_parser = parse::hash
	)]
	header_at: Option<String>,

	/// The ws uri from which to fetch the header.
	///
	/// If the `live` state type is being used, then this can be omitted, and is equal to whatever
	/// the `state::uri` is. Only use this (with care) when combined with a snapshot.
	#[arg(
		long,
		value_parser = parse::url
	)]
	header_ws_uri: Option<String>,

	/// The state type to use.
	#[command(subcommand)]
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
			(None, State::Live(LiveState { at: Some(at), .. })) => hash_of::<Block>(at),
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
			(None, State::Live(LiveState { uri, .. })) => uri.clone(),
			(None, State::Snap { .. }) => {
				panic!("either `--header-uri` must be provided, or state must be `live`");
			},
		}
	}
}

pub(crate) async fn offchain_worker<Block, H: HostFunctions>(
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
{
	let executor = build_wasm_executor(&shared, &config);
	let header_at = command.header_at::<Block>()?;
	let header_ws_uri = command.header_ws_uri::<Block>();

	let rpc = ws_client(&header_ws_uri).await?;
	let header = ChainApi::<(), Block::Hash, Block::Header, ()>::header(&rpc, Some(header_at))
		.await
		.unwrap()
		.unwrap();
	log::info!(
		target: LOG_TARGET,
		"fetched header from {:?}, block number: {:?}",
		header_ws_uri,
		header.number()
	);

	// we first build the externalities with the remote code.
	let mut ext = command
		.state
		.into_ext::<Block>()?
		.state_version(shared.state_version)
		.build()
		.await?;

	let _ = state_machine_call::<Block, H>(
		&ext,
		&executor,
		"OffchainWorkerApi_offchain_worker",
		header.encode().as_ref(),
		full_extensions(),
	)?;

	log::info!(target: LOG_TARGET, "OffchainWorkerApi_offchain_worker executed without errors.");

	Ok(())
}

fn ensure_matching_runtime_version(spec1: &RuntimeVersion, spec2: &RuntimeVersion, no_panic: bool) {
	let log_or_panic = |err| {
		if no_panic {
			log::error!("{}", err);
		} else {
			panic!("{}", err);
		}
	};

	if spec1.spec_name != spec2.spec_name {
		let err = format!("incompatible spec-name: {:?} {:?}", spec1.spec_name, spec2.spec_name);
		log_or_panic(err);
	}

	if spec1.spec_version != spec2.spec_version {
		let err = format!("incompatible spec-version: {:?} {:?}", spec1.spec_version, spec2.spec_version);
		log_or_panic(err);
	}
}
