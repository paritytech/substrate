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

//! # Try-runtime
//!
//! Substrate's ultimate testing framework for the power users.
//!
//! > As the name suggests, `try-runtime` is a detailed testing framework that gives you a lot of
//! control over what is being executed in which environment. It is recommended that user's first
//! familiarize themselves with substrate in depth, particularly the execution model. It is critical
//! to deeply understand how the wasm/native interactions, and the runtime apis work in the
//! substrate runtime.
//!
//! #### Resources
//!
//! Some resources about the above:
//!
//! 1. https://substrate.dev/docs/en/knowledgebase/integrate/try-runtime
//! 2. https://www.crowdcast.io/e/substrate-seminar/41
//! 3. https://substrate.dev/docs/en/knowledgebase/advanced/executor
//!
//! ---
//!
//! ## Overview
//!
//! The basis of all try-runtime commands is the same: connect to a live node, scrape its *state*
//! and put it inside a `TestExternalities`, then call into a *specific runtime-api* using the given
//! state and some *runtime*.
//!
//! All of the variables in the above statement are made *italic*. Let's look at each of them:
//!
//! 1. **State** is the key-value pairs of data that consist the important information that any
//! blockchain is keeping. A state can be full (all key-value pairs), or be partial (only pairs
//! related to some pallets). Moreover, some keys are special and live outside of pallets, known as
//! [`well_known_keys`] in substrate. The most important of these is the `:CODE:` key, which
//! contains the code used for execution, when `--execution Wasm` is used.
//! 2. *A runtime-api* is a call into the function defined in the runtime, *on top of a given
//! state*. Each subcommand of `try-runtime` utilizes a specific one of these.
//! 3. Finally, the **runtime** is the actual code that is used to execute the aforementioned
//! runtime-api. All substrate based chains always have two runtimes: native and wasm. The decision
//! of which one is chosen is slightly non-trivial. First, let's look at the options:
//!
//! 1. Native: this means that the runtime that is **in your codebase**, aka whatever you see in
//! your editor is being used. This runtime is easier for diagnostics. In the rest of the
//! documentation, by "local runtime", we mean the na 2. Wasm: this means that whatever is stored in
//! the `:CODE:` key of the state that your scrape is being used. In plain sight, since the entire
//! state (including `:CODE:`) is scraped from a remote chain, you could conclude that the wasm
//! runtime, if used, is always equal to the canonical runtime. That's factually true, but then the
//! testing would be quite lame. Typically, with try-runtime, you don't want to execute whatever
//! code is already on the live chain. Instead, you want your local runtime (which typically
//! includes a non-released feature) to be used. This is why try-runtime overwrites the wasm runtime
//! (at `:CODE:`) with the local runtime as well. That being said, this behavior can be controlled
//! in certain subcommands with a special flag.
//!
//! The decision of which runtime is eventually used is based on two facts:
//!
//! 1. `--execution` flag. If you specify `wasm`, then it is *always* wasm. If it is `native`, then
//! if and ONLY IF the spec versions match, then the native runtime is used. Else, wasm runtime is
//! used again.
//! 2. `--chain` flag (if present in your cli), which determines *which native runtime*, if needed,
//! might be used.
//!
//! All in all, if the term "local runtime" is used in the rest of this crate's documentation, it
//! means either the native runtime, or the wasm runtime when overwritten inside `:CODE:`. In other
//! words, it means your... well, "local runtime", regardless of wasm or native.
//!
//! To make sure there are no errors regarding this, always run any try-runtime command with
//! `executor=trace` logging targets, which will specify which runtime is being used per api call.
//!
//! Furthermore, other relevant log targets are: `try-runtime::cli`, `remote-ext`, and `runtime`.
//!
//! ## Commands
//!
//! See [`Command`] for more info.
//! 
//! ## Examples
//! 
//! TODO

use parity_scale_codec::Decode;
use remote_externalities::{
	Builder, Mode, OfflineConfig, OnlineConfig, SnapshotConfig, TestExternalities,
};
use sc_chain_spec::ChainSpec;
use sc_cli::{CliConfiguration, ExecutionStrategy, WasmExecutionMethod};
use sc_executor::NativeElseWasmExecutor;
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_core::{
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	storage::{well_known_keys, StorageData, StorageKey},
	testing::TaskExecutor,
	traits::TaskExecutorExt,
	twox_128, H256,
};
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_state_machine::{OverlayedChanges, StateMachine};
use std::{fmt::Debug, path::PathBuf, str::FromStr};

mod commands;
pub(crate) mod parse;
pub(crate) const LOG_TARGET: &'static str = "try-runtime::cli";

/// Possible commands of `try-runtime`.
#[derive(Debug, Clone, structopt::StructOpt)]
pub enum Command {
	/// Execute the migrations of the "local runtime".
	///
	/// This uses a custom runtime api call, namely "TryRuntime_on_runtime_upgrade".
	///
	/// This always overwrites the wasm code with the local runtime, to ensure the new migrations
	/// are being executed. Re-executing already existing migrations is evidently not very
	/// exciting.
	OnRuntimeUpgrade(commands::on_runtime_upgrade::OnRuntimeUpgradeCmd),

	/// Executes the given block against some state.
	///
	/// Unlike [`Command:::OnRuntimeUpgrade`], this command needs two inputs: the state, and the
	/// block data. Since the state could be cached (see [`State::Snap`]), different flags are
	/// provided for both. `--block-at` and `--block-uri`, if provided, are only used for fetching
	/// the block. For convenience, these flags can be both emitted, if the [`State::Live`] is
	/// being used.
	///
	/// Note that by default, this command does not overwrite the code, so in wasm execution, the
	/// live chain's code is used. This can be disabled if desired, see
	/// [`ExecuteBlockCmd::overwrite_wasm_code`]. Note that if you do overwrite the wasm code, or
	/// generally use the local runtime for this, you might
	///   - not be able to decode the block, if the block format has changed.
	///   - almost certainly get a state root mismatch.
	///
	/// To make testing slightly more dynamic, you can disable the state root check by enabling
	/// [`ExecuteBlockCmd::no_state_root_check`].
	///
	/// A subtle detail of execute block is that if you want to execute block 100 of a live chain
	/// again, you need to scrape the state of block 99. This is already done automatically if you
	/// use [`State::Live`], and the parent has of the target block is used to scrape the state. If
	/// [`State::Snap`] is being used, then this needs to manually taken into consideration.
	///
	/// This executes the same runtime api as normal block import, namely `Core_execute_block`. If
	/// [`ExecuteBlockCmd::no_state_root_check`] is set, it uses a custom, try-runtime-only runtime
	/// api called `TryRuntime_execute_block_no_state_root_check`.
	ExecuteBlock(commands::execute_block::ExecuteBlockCmd),

	/// Executes *the offchain worker hooks* of a given block against some state.
	///
	/// Similar to [`Command:::ExecuteBlock`], this command needs two inputs: the state, and the
	/// header data. Likewise, `--header-at` and `--header-uri` can be filled, or omitted if
	/// [`State::Live`] is used.
	///
	/// Similar to [`Command:::ExecuteBlock`], this command does not overwrite the code, so in wasm
	/// execution, the live chain's code is used. This can be disabled if desired, see
	/// [`OffchainWorkerCmd::overwrite_wasm_code`].
	///
	/// This executes the same runtime api as normal block import, namely
	/// `OffchainWorkerApi_offchain_worker`.
	OffchainWorker(commands::offchain_worker::OffchainWorkerCmd),

	/// Follow the given chain's finalized blocks and apply all of its extrinsics.
	///
	/// This is essentially repeated calls to [`Command::ExecuteBlock`], whilst the local runtime
	/// is always at use, the state root check is disabled, and the state is persisted between
	/// executions.
	///
	/// This allows the behavior of a new runtime to be inspected over a long period of time, with
	/// realistic transactions coming as input.
	///
	/// This does not support snapshot states, and can only work with a remote chain. Upon first
	/// connections, starts listening for finalized block events. Upon first notification, it
	/// initializes the state from the remote node, and starts applying that block, and all the
	/// ones that follows, to the same growing state.
	FollowChain(commands::follow_chain::FollowChainCmd),
}

/// Shared parameters of the `try-runtime` commands
#[derive(Debug, Clone, structopt::StructOpt)]
pub struct SharedParams {
	/// Shared parameters of substrate cli.
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: sc_cli::SharedParams,

	/// The execution strategy that should be used.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "Wasm",
	)]
	pub execution: ExecutionStrategy,

	/// Type of wasm execution used.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::variants(),
		case_insensitive = true,
		default_value = "Compiled"
	)]
	pub wasm_method: WasmExecutionMethod,

	/// The number of 64KB pages to allocate for Wasm execution. Defaults to
	/// [`sc_service::Configuration.default_heap_pages`].
	#[structopt(long)]
	pub heap_pages: Option<u64>,
}

/// Our `try-runtime` command.
///
/// See [`Command`] for more info.
#[derive(Debug, Clone, structopt::StructOpt)]
pub struct TryRuntimeCmd {
	#[structopt(flatten)]
	pub shared: SharedParams,

	#[structopt(subcommand)]
	pub command: Command,
}

/// The source of runtime *state* to use.
#[derive(Debug, Clone, structopt::StructOpt)]
pub enum State {
	/// Use a state snapshot as the source of runtime state.
	///
	/// This can be crated by passing a value to [`State::Live::snapshot_path`].
	Snap {
		#[structopt(short, long)]
		snapshot_path: PathBuf,
	},

	/// Use a live chain as the source of runtime state.
	Live {
		/// The url to connect to.
		#[structopt(
			short,
			long,
			parse(try_from_str = parse::url),
		)]
		uri: String,

		/// The block hash at which to fetch the state.
		///
		/// If non provided, then the latest finalized head is used. This is particularly useful
		/// for [`Command::OnRuntimeUpgrade`].
		#[structopt(
			short,
			long,
			multiple = false,
			parse(try_from_str = parse::hash),
		)]
		at: Option<String>,

		/// An optional state snapshot file to WRITE to. Not written if set to `None`.
		#[structopt(short, long)]
		snapshot_path: Option<PathBuf>,

		/// The pallets to scrape. If empty, entire chain state will be scraped.
		#[structopt(short, long, require_delimiter = true)]
		pallets: Option<Vec<String>>,
	},
}

impl State {
	/// Create the [`remote_externalities::Builder`] from self.
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
			State::Live { snapshot_path, pallets, uri, at } => {
				let at = match at {
					Some(at_str) => Some(hash_of::<Block>(at_str)?),
					None => None,
				};
				Builder::<Block>::new()
					.mode(Mode::Online(OnlineConfig {
						transport: uri.to_owned().into(),
						state_snapshot: snapshot_path.as_ref().map(SnapshotConfig::new),
						pallets: pallets.to_owned().unwrap_or_default(),
						at,
					}))
					.inject_hashed_key(
						&[twox_128(b"System"), twox_128(b"LastRuntimeUpgrade")].concat(),
					)
			},
		})
	}

	/// Get the uri, if self is `Live`.
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
pub(crate) fn extract_code(spec: &Box<dyn ChainSpec>) -> sc_cli::Result<(StorageKey, StorageData)> {
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

/// Get the hash type of the generic `Block` from a `hash_str`.
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
pub(crate) async fn ensure_matching_spec_name<Block: BlockT + serde::de::DeserializeOwned>(
	uri: String,
	expected_spec_name: String,
) {
	match remote_externalities::rpc_api::get_runtime_version::<Block, _>(uri.clone(), None)
		.await
		.map(|version| String::from(version.spec_name.clone()))
		.map(|spec_name| spec_name.to_lowercase())
	{
		Ok(spec) if spec == expected_spec_name => {
			log::debug!(target: LOG_TARGET, "found matching spec name: {:?}", spec);
		},
		Ok(spec) => {
			panic!(
				"version mismatch: remote spec name: '{}', expected (local chain spec, aka. `--chain`): '{}'",
				spec,
				expected_spec_name,
			);
		},
		Err(why) => {
			log::error!(
				target: LOG_TARGET,
				"failed to fetch runtime version from {}: {:?}. Skipping the check",
				uri,
				why
			);
		},
	}
}

/// Build all extensions that we typically use.
pub(crate) fn full_extensions() -> Extensions {
	let mut extensions = Extensions::default();
	extensions.register(TaskExecutorExt::new(TaskExecutor::new()));
	let (offchain, _offchain_state) = TestOffchainExt::new();
	let (pool, _pool_state) = TestTransactionPoolExt::new();
	extensions.register(OffchainDbExt::new(offchain.clone()));
	extensions.register(OffchainWorkerExt::new(offchain));
	extensions.register(KeystoreExt(std::sync::Arc::new(KeyStore::new())));
	extensions.register(TransactionPoolExt::new(pool));

	extensions
}

/// Build a default execution that we typically use.
pub(crate) fn build_executor<D: NativeExecutionDispatch + 'static>(
	shared: &SharedParams,
	config: &sc_service::Configuration,
) -> NativeElseWasmExecutor<D> {
	let wasm_method = shared.wasm_method;
	let heap_pages = shared.heap_pages.or(config.default_heap_pages);
	let max_runtime_instances = config.max_runtime_instances;

	NativeElseWasmExecutor::<D>::new(wasm_method.into(), heap_pages, max_runtime_instances)
}

/// Execute the given `method` and `data` on top of `ext`, returning the results (encoded) and the
/// state `changes`.
pub(crate) fn state_machine_call<Block: BlockT, D: NativeExecutionDispatch + 'static>(
	ext: &TestExternalities,
	executor: &NativeElseWasmExecutor<D>,
	execution: sc_cli::ExecutionStrategy,
	method: &'static str,
	data: &[u8],
	extensions: Extensions,
) -> sc_cli::Result<(OverlayedChanges, Vec<u8>)> {
	let mut changes = Default::default();
	let encoded_results = StateMachine::<_, _, NumberFor<Block>, _>::new(
		&ext.backend,
		None,
		&mut changes,
		executor,
		method,
		data,
		extensions,
		&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend).runtime_code()?,
		sp_core::testing::TaskExecutor::new(),
	)
	.execute(execution.into())
	.map_err(|e| format!("failed to execute 'TryRuntime_on_runtime_upgrade': {:?}", e))
	.map_err::<sc_cli::Error, _>(Into::into)?;

	Ok((changes, encoded_results))
}

/// Get the spec name from the local runtime.
pub(crate) fn local_spec_name<Block: BlockT, D: NativeExecutionDispatch + 'static>(
	ext: &TestExternalities,
	executor: &NativeElseWasmExecutor<D>,
) -> String {
	let (_, encoded) = state_machine_call::<Block, D>(
		&ext,
		&executor,
		sc_cli::ExecutionStrategy::NativeElseWasm,
		"Core_version",
		&[],
		Default::default(),
	)
	.expect("all runtimes should have version; qed");
	<sp_version::RuntimeVersion as Decode>::decode(&mut &*encoded)
		.map_err(|e| format!("failed to decode output: {:?}", e))
		.map(|v| v.spec_name)
		.expect("all runtimes should have version; qed")
		.into()
}
