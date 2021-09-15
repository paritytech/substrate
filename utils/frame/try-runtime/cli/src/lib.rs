// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! `Structopt`-ready structs for `try-runtime`.

use remote_externalities::{Builder, Mode, OfflineConfig, OnlineConfig, SnapshotConfig};
use sc_chain_spec::ChainSpec;
use sc_cli::{CliConfiguration, ExecutionStrategy, WasmExecutionMethod};
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::{
	storage::{well_known_keys, StorageData, StorageKey},
	H256,
};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{fmt::Debug, path::PathBuf, str::FromStr};

mod commands;
pub(crate) mod parse;
pub(crate) const LOG_TARGET: &'static str = "try-runtime::cli";

/// Possible subcommands of `try-runtime`.
#[derive(Debug, Clone, structopt::StructOpt)]
pub enum Command {
	/// Execute "TryRuntime_on_runtime_upgrade" against the given runtime state.
	OnRuntimeUpgrade(commands::on_runtime_upgrade::OnRuntimeUpgradeCmd),

	/// Execute "OffchainWorkerApi_offchain_worker" against the given runtime state.
	OffchainWorker(commands::offchain_worker::OffchainWorkerCmd),

	/// Execute "Core_execute_block" using the given block and the runtime state of the parent
	/// block.
	ExecuteBlock(commands::execute_block::ExecuteBlockCmd),

	/// Follow the given chain's finalized blocks and apply all of its extrinsics.
	///
	/// The initial state is the state of the first finalized block received.
	FollowChain(commands::follow_chain::FollowChainCmd),
}

#[derive(Debug, Clone, structopt::StructOpt)]
pub struct SharedParams {
	/// The shared parameters
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The execution strategy that should be used for benchmarks
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "Wasm",
	)]
	pub execution: ExecutionStrategy,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::variants(),
		case_insensitive = true,
		default_value = "Compiled"
	)]
	pub wasm_method: WasmExecutionMethod,

	/// The number of 64KB pages to allocate for Wasm execution. Defaults to
	/// sc_service::Configuration.default_heap_pages.
	#[structopt(long)]
	pub heap_pages: Option<u64>,
}

/// Various commands to try out against runtime state at a specific block.
#[derive(Debug, Clone, structopt::StructOpt)]
pub struct TryRuntimeCmd {
	#[structopt(flatten)]
	pub shared: SharedParams,

	#[structopt(subcommand)]
	pub command: Command,
}

/// The source of runtime state to try operations against.
#[derive(Debug, Clone, structopt::StructOpt)]
pub enum State {
	/// Use a state snapshot as the source of runtime state. NOTE: for the offchain-worker and
	/// execute-block command this is only partially supported and requires a archive node url.
	Snap {
		#[structopt(short, long)]
		snapshot_path: PathBuf,
	},

	/// Use a live chain as the source of runtime state.
	Live {
		/// The url to connect to
		#[structopt(
			short,
			long,
			parse(try_from_str = parse::url),
		)]
		uri: String,

		/// The block hash at which to fetch the state.
		#[structopt(
			short,
			long,
			multiple = false,
			parse(try_from_str = parse::hash),
		)]
		at: String,

		/// An optional state snapshot file to WRITE to. Not written if set to `None`.
		#[structopt(short, long)]
		snapshot_path: Option<PathBuf>,

		/// The modules to scrape. If empty, entire chain state will be scraped.
		#[structopt(short, long, require_delimiter = true)]
		modules: Option<Vec<String>>,
	},
}

impl State {
	pub(crate) fn builder<Block: BlockT>(&self) -> sc_cli::Result<Builder<Block>>
	where
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
	{
		Ok(match self {
			State::Snap { snapshot_path } =>
				Builder::<Block>::new().mode(Mode::Offline(OfflineConfig {
					state_snapshot: SnapshotConfig::new(snapshot_path),
				})),
			State::Live { snapshot_path, modules, uri, at } =>
				Builder::<Block>::new().mode(Mode::Online(OnlineConfig {
					transport: uri.to_owned().into(),
					state_snapshot: snapshot_path.as_ref().map(SnapshotConfig::new),
					modules: modules.to_owned().unwrap_or_default(),
					at: Some(hash_of::<Block>(at)?),
					..Default::default()
				})),
		})
	}

	pub(crate) fn live_uri(&self) -> Option<String> {
		match self {
			State::Live { uri, .. } => Some(uri.clone()),
			_ => None,
		}
	}
}

impl TryRuntimeCmd {
	pub async fn run<Block, ExecDispatch>(&self, config: Configuration) -> sc_cli::Result<()>
	where
		Block: BlockT<Hash = H256> + serde::de::DeserializeOwned,
		Block::Header: serde::de::DeserializeOwned,
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
		NumberFor<Block>: FromStr,
		<NumberFor<Block> as FromStr>::Err: Debug,
		ExecDispatch: NativeExecutionDispatch + 'static,
	{
		match &self.command {
			Command::OnRuntimeUpgrade(ref cmd) =>
				commands::on_runtime_upgrade::on_runtime_upgrade::<Block, ExecDispatch>(
					self.shared.clone(),
					cmd.clone(),
					config,
				)
				.await,
			Command::OffchainWorker(cmd) =>
				commands::offchain_worker::offchain_worker::<Block, ExecDispatch>(
					self.shared.clone(),
					cmd.clone(),
					config,
				)
				.await,
			Command::ExecuteBlock(cmd) =>
				commands::execute_block::execute_block::<Block, ExecDispatch>(
					self.shared.clone(),
					cmd.clone(),
					config,
				)
				.await,
			Command::FollowChain(cmd) =>
				commands::follow_chain::follow_chain::<Block, ExecDispatch>(
					self.shared.clone(),
					cmd.clone(),
					config,
				)
				.await,
		}
	}
}

impl CliConfiguration for TryRuntimeCmd {
	fn shared_params(&self) -> &sc_cli::SharedParams {
		&self.shared.shared_params
	}

	fn chain_id(&self, _is_dev: bool) -> sc_cli::Result<String> {
		Ok(match self.shared.shared_params.chain {
			Some(ref chain) => chain.clone(),
			None => "dev".into(),
		})
	}
}

/// Extract `:code` from the given chain spec and return as `StorageData` along with the
/// corresponding `StorageKey`.
pub(crate) fn extract_code(spec: Box<dyn ChainSpec>) -> sc_cli::Result<(StorageKey, StorageData)> {
	let genesis_storage = spec.build_storage()?;
	let code = StorageData(
		genesis_storage
			.top
			.get(well_known_keys::CODE)
			.expect("code key must exist in genesis storage; qed")
			.to_vec(),
	);
	let code_key = StorageKey(well_known_keys::CODE.to_vec());

	Ok((code_key, code))
}

pub(crate) fn hash_of<Block: BlockT>(hash_str: &str) -> sc_cli::Result<Block::Hash>
where
	Block::Hash: FromStr,
	<Block::Hash as FromStr>::Err: Debug,
{
	hash_str
		.parse::<<Block as BlockT>::Hash>()
		.map_err(|e| format!("Could not parse block hash: {:?}", e).into())
}

/// Check the spec_name of an `ext`
///
/// If the version does not exist, or if it does not match with the given, it emits a warning.
pub(crate) async fn check_spec_name<Block: BlockT + serde::de::DeserializeOwned>(
	uri: String,
	expected_spec_name: String,
) {
	let expected_spec_name = expected_spec_name.to_lowercase();
	match remote_externalities::rpc_api::get_runtime_version::<Block, _>(uri.clone(), None)
		.await
		.map(|version| String::from(version.spec_name.clone()))
		.map(|spec_name| spec_name.to_lowercase())
	{
		Ok(spec) if spec == expected_spec_name => {
			log::debug!(target: LOG_TARGET, "found matching spec name: {:?}", spec);
		},
		Ok(spec) => {
			log::warn!(
				target: LOG_TARGET,
				"version mismatch: remote spec name: '{}', expected (local chain spec, aka. `--chain`): '{}'",
				spec,
				expected_spec_name,
			);
		},
		Err(why) => {
			log::error!(
				target: LOG_TARGET,
				"failed to fetch runtime version from {}: {:?}",
				uri,
				why
			);
		},
	}
}
