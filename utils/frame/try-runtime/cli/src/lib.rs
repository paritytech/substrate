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

//! # Try-runtime
//!
//! Substrate's ultimate testing framework for the power users.
//!
//! > As the name suggests, `try-runtime` is a detailed testing framework that gives you a lot of
//! control over what is being executed in which environment. It is recommended that user's first
//! familiarize themselves with substrate in depth, particularly the execution model. It is critical
//! to deeply understand how the wasm/client/runtime interactions, and the runtime apis work in the
//! substrate runtime, before commencing to working with `try-runtime`.
//!
//! #### Resources
//!
//! Some resources about the above:
//!
//! 1. <https://docs.substrate.io/v3/tools/try-runtime>
//! 2. <https://www.crowdcast.io/e/substrate-seminar/41>
//! 3. <https://docs.substrate.io/v3/advanced/executor>
//!
//! ---
//!
//! ## Background Knowledge
//!
//! The basis of all try-runtime commands is the same: connect to a live node, scrape its *state*
//! and put it inside a `TestExternalities`, then call into a *specific runtime-api* using the given
//! state and some *runtime*.
//!
//! Alternatively, the state could come from a snapshot file.
//!
//! All of the variables in the above statement are made *italic*. Let's look at each of them:
//!
//! 1. **State** is the key-value pairs of data that comprise the canonical information that any
//!    blockchain is keeping. A state can be full (all key-value pairs), or be partial (only pairs
//!    related to some pallets/prefixes). Moreover, some keys are especial and are not related to
//!    specific pallets, known as [`well_known_keys`] in substrate. The most important of these is
//!    the `:CODE:` key, which contains the code used for execution, when wasm execution is chosen.
//!
//! 2. *A runtime-api* call is a call into a function defined in the runtime, *on top of a given
//!    state*. Each subcommand of `try-runtime` utilizes a specific *runtime-api*.
//!
//! 3. Finally, the **runtime** is the actual code that is used to execute the aforementioned
//!    runtime-api. Everything in this crate assumes wasm execution, which means the runtime that
//!    you use is the one stored onchain, namely under the `:CODE:` key.
//!
//! To recap, a typical try-runtime command does the following:
//!
//! 1. Download the state of a live chain, and write to an `externalities`.
//! 2. Overwrite the `:CODE:` with a given wasm blob
//! 3. Test some functionality via calling a runtime-api.
//!
//! ## Usage
//!
//! To use any of the provided commands, [`SharedParams`] must be provided. The most important of
//! which being [`SharedParams::runtime`], which specifies which runtime to use. Furthermore,
//! [`SharedParams::overwrite_state_version`] can be used to alter the state-version (see
//! https://forum.polkadot.network/t/state-trie-migration/852 for more info).
//!
//! Then, the specific command has to be specified. See [`Command`] for more information about each
//! command's specific customization flags, and assumptions regarding the runtime being used.
//!
//! Said briefly, this CLI is capable of executing:
//!
//! * [`Command::OnRuntimeUpgrade`]: execute all the `on_runtime_upgrade` hooks.
//! * [`Command::ExecuteBlock`]: re-execute the given block.
//! * [`Command::OffchainWorker`]: re-execute the given block's offchain worker code path.
//! * [`Command::FollowChain`]: continuously execute the blocks of a remote chain on top of a given
//!       runtime.
//! * [`Command::CreateSnapshot`]: Create a snapshot file from a remote node.
//!
//! Finally, To make sure there are no errors regarding this, always run any `try-runtime` command
//! with `executor=trace` logging targets, which will specify which runtime is being used per api
//! call. Moreover, `remote-ext`, `try-runtime` and `runtime` logs targets will also be useful.
//!
//! ## Spec name check
//!
//! A common pitfall is that you might be running some test on top of the state of chain `x`, with
//! the runtime of chain `y`. To avoid this all commands do a spec-name check before executing
//! anything by default. This will check the, if any alterations are being made to the `:CODE:`,
//! then the spec names match. The spec versions are warned, but are not mandated to match.
//!
//! > If anything, in most cases, we expect spec-versions to NOT match, because try-runtime is all
//! > about testing unreleased runtimes.
//!
//! ## Note on nodes that respond to `try-runtime` requests.
//!
//! There are a number of flags that need to be preferably set on a running node in order to work
//! well with try-runtime's expensive RPC queries:
//!
//! - set `--rpc-max-response-size 1000` and
//! - `--rpc-max-request-size 1000` to ensure connections are not dropped in case the state is
//!   large.
//! - set `--rpc-cors all` to ensure ws connections can come through.
//!
//! Note that *none* of the try-runtime operations need unsafe RPCs.
//!
//! ## Best Practices
//!
//! Try-runtime is all about battle-testing unreleased runtime. The following list of suggestions
//! help developers maximize the testing coverage and make base use of `try-runtime`.
//!
//! #### Adding pre/post hooks
//!
//! One of the gems that come only in the `try-runtime` feature flag is the `pre_upgrade` and
//! `post_upgrade` hooks for `OnRuntimeUpgrade`. This trait is implemented either inside the pallet,
//! or manually in a runtime, to define a migration. In both cases, these functions can be added,
//! given the right flag:
//!
//! ```ignore
//!
//! #[cfg(feature = try-runtime)]
//! fn pre_upgrade() -> Result<Vec<u8>, &'static str> {}
//!
//! #[cfg(feature = try-runtime)]
//! fn post_upgrade(state: Vec<u8>) -> Result<(), &'static str> {}
//! ```
//!
//! (The pallet macro syntax will support this simply as a part of `#[pallet::hooks]`).
//!
//! These hooks allow you to execute some code, only within the `on-runtime-upgrade` command, before
//! and after the migration. Moreover, `pre_upgrade` can return a `Vec<u8>` that contains arbitrary
//! encoded data (usually some pre-upgrade state) which will be passed to `post_upgrade` after
//! upgrading and used for post checking.
//!
//! ## State Consistency
//!
//! Similar to
//!
//! #### Logging
//!
//! It is super helpful to make sure your migration code uses logging (always with a `runtime` log
//! target prefix, e.g. `runtime::balance`) and state exactly at which stage it is, and what it is
//! doing.
//!
//! #### Guarding migrations
//!
//! Always make sure that any migration code is guarded either by `StorageVersion`, or by some
//! custom storage item, so that it is NEVER executed twice, even if the code lives in two
//! consecutive runtimes.
//!
//! ## Examples
//!
//! Run the migrations of a given runtime on top of live Polkadot state.
//!
//! ```sh
//! ```
//!
//! Same as the previous one, but run it at specific block number's state. This means that this
//! block hash's state shall not yet have been pruned in `rpc.polkadot.io`.
//!
//! ```sh
//! ```
//! Same as the previous one, but use a snapshot file.
//!
//! ```sh
//! ```
//!
//! Execute a given past block with the given runtime.
//!
//! ```sh
//! ```
//!
//! Execute the given past block with the given runtime, while the snapshot is stored on a file.
//!
//! ```sh
//! ```
//!
//! Follow Polkadot's blocks using `follow-chain`, with the given runtime.
#![cfg(feature = "try-runtime")]

use parity_scale_codec::Decode;
use remote_externalities::{
	Builder, Mode, OfflineConfig, OnlineConfig, RemoteExternalities, SnapshotConfig,
	TestExternalities,
};
use sc_cli::{
	CliConfiguration, RuntimeVersion, WasmExecutionMethod, WasmtimeInstantiationStrategy,
	DEFAULT_WASMTIME_INSTANTIATION_STRATEGY, DEFAULT_WASM_EXECUTION_METHOD,
};
use sc_executor::{sp_wasm_interface::HostFunctions, WasmExecutor};
use sp_core::{
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	storage::well_known_keys,
	testing::TaskExecutor,
	traits::{ReadRuntimeVersion, TaskExecutorExt},
	twox_128, H256,
};
use sp_externalities::Extensions;
use sp_keystore::{testing::KeyStore, KeystoreExt};
use sp_runtime::{
	traits::{Block as BlockT, NumberFor},
	DeserializeOwned,
};
use sp_state_machine::{CompactProof, OverlayedChanges, StateMachine, TrieBackendBuilder};
use sp_version::StateVersion;
use std::{fmt::Debug, path::PathBuf, str::FromStr};

mod commands;
pub(crate) mod parse;
pub(crate) const LOG_TARGET: &str = "try-runtime::cli";

/// Possible commands of `try-runtime`.
#[derive(Debug, Clone, clap::Subcommand)]
pub enum Command {
	/// Execute the migrations of the "local runtime".
	///
	/// This uses a custom runtime api call, namely "TryRuntime_on_runtime_upgrade".
	///
	/// This always overwrites the wasm code with the local runtime (specified by `--chain`), to
	/// ensure the new migrations are being executed. Re-executing already existing migrations is
	/// evidently not very exciting.
	OnRuntimeUpgrade(commands::on_runtime_upgrade::OnRuntimeUpgradeCmd),

	/// Executes the given block against some state.
	///
	/// Unlike [`Command::OnRuntimeUpgrade`], this command needs two inputs: the state, and the
	/// block data. Since the state could be cached (see [`State::Snap`]), different flags are
	/// provided for both. `--block-at` and `--block-uri`, if provided, are only used for fetching
	/// the block. For convenience, these flags can be both emitted, if the [`State::Live`] is
	/// being used.
	///
	/// Note that by default, this command does not overwrite the code, so in wasm execution, the
	/// live chain's code is used. This can be disabled if desired, see
	/// `ExecuteBlockCmd::overwrite_wasm_code`.
	///
	/// Note that if you do overwrite the wasm code, or generally use the local runtime for this,
	/// you might
	///   - not be able to decode the block, if the block format has changed.
	///   - quite possibly will get a signature verification failure, since the spec and
	///     transaction version are part of the signature's payload, and if they differ between
	///     your local runtime and the remote counterparts, the signatures cannot be verified.
	///   - almost certainly will get a state root mismatch, since, well, you are executing a
	///     different state transition function.
	///
	/// To make testing slightly more dynamic, you can disable the state root  check by enabling
	/// `ExecuteBlockCmd::no_check`. If you get signature verification errors, you should manually
	/// tweak your local runtime's spec version to fix this.
	///
	/// A subtle detail of execute block is that if you want to execute block 100 of a live chain
	/// again, you need to scrape the state of block 99. This is already done automatically if you
	/// use [`State::Live`], and the parent hash of the target block is used to scrape the state.
	/// If [`State::Snap`] is being used, then this needs to be manually taken into consideration.
	///
	/// This does not execute the same runtime api as normal block import do, namely
	/// `Core_execute_block`. Instead, it uses `TryRuntime_execute_block`, which can optionally
	/// skip state-root check (useful for trying a unreleased runtime), and can execute runtime
	/// sanity checks as well.
	ExecuteBlock(commands::execute_block::ExecuteBlockCmd),

	/// Executes *the offchain worker hooks* of a given block against some state.
	///
	/// Similar to [`Command::ExecuteBlock`], this command needs two inputs: the state, and the
	/// header data. Likewise, `--header-at` and `--header-uri` can be filled, or omitted if
	/// [`State::Live`] is used.
	///
	/// Similar to [`Command::ExecuteBlock`], this command does not overwrite the code, so in wasm
	/// execution, the live chain's code is used. This can be disabled if desired, see
	/// `OffchainWorkerCmd::overwrite_wasm_code`.
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
	/// NOTE: this does NOT execute the offchain worker hooks of mirrored blocks. This might be
	/// added in the future.
	///
	/// This does not support snapshot states, and can only work with a remote chain. Upon first
	/// connections, starts listening for finalized block events. Upon first block notification, it
	/// initializes the state from the remote node, and starts applying that block, plus all the
	/// blocks that follow, to the same growing state.
	FollowChain(commands::follow_chain::FollowChainCmd),

	/// Create a new snapshot file.
	CreateSnapshot(commands::create_snapshot::CreateSnapshotCmd),
}

#[derive(Debug, Clone)]
enum Runtime {
	/// Use the given path to the wasm binary file.
	///
	/// It must have been compiled with `try-runtime`.
	Path(PathBuf),

	/// Use the code of the remote node, or the snapshot.
	///
	/// In almost all cases, this is not what you want, because the code in the remote node does
	/// not have any of the try-runtime custom runtime APIs.
	Existing,
}

impl FromStr for Runtime {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		Ok(match s.to_lowercase().as_ref() {
			"existing" => Runtime::Existing,
			x @ _ => Runtime::Path(x.into()),
		})
	}
}

/// Shared parameters of the `try-runtime` commands
#[derive(Debug, Clone, clap::Parser)]
#[group(skip)]
pub struct SharedParams {
	/// Shared parameters of substrate cli.
	///
	/// TODO: this is only needed because try-runtime is embedded in the substrate CLI. It should
	/// go away.
	#[allow(missing_docs)]
	#[clap(flatten)]
	shared_params: sc_cli::SharedParams,

	/// The runtime to use.
	///
	/// Must be a path to a wasm blob, compiled with `try-runtime` feature flag.
	///
	/// Or, `existing`, indicating that you don't want to overwrite the runtime. This will use
	/// whatever comes from the remote node, or the snapshot file. This will most likely not work
	/// against a remote node, as no (sane) blockchain should compile its onchain wasm with
	/// `try-runtime` feature.
	#[arg(long)]
	runtime: Runtime,

	/// Type of wasm execution used.
	#[arg(
		long = "wasm-execution",
		value_name = "METHOD",
		value_enum,
		ignore_case = true,
		default_value_t = DEFAULT_WASM_EXECUTION_METHOD,
	)]
	wasm_method: WasmExecutionMethod,

	/// The WASM instantiation method to use.
	///
	/// Only has an effect when `wasm-execution` is set to `compiled`.
	#[arg(
		long = "wasm-instantiation-strategy",
		value_name = "STRATEGY",
		default_value_t = DEFAULT_WASMTIME_INSTANTIATION_STRATEGY,
		value_enum,
	)]
	wasmtime_instantiation_strategy: WasmtimeInstantiationStrategy,

	/// The number of 64KB pages to allocate for Wasm execution. Defaults to
	/// [`sc_service::Configuration.default_heap_pages`].
	#[arg(long)]
	heap_pages: Option<u64>,

	/// Overwrite the `state_version`.
	///
	/// Otherwise `remote-externalities` will automatically set the correct state version.
	#[arg(long, value_parser = parse::state_version)]
	overwrite_state_version: Option<StateVersion>,
}

/// Our `try-runtime` command.
///
/// See [`Command`] for more info.
#[derive(Debug, Clone, clap::Parser)]
pub struct TryRuntimeCmd {
	#[clap(flatten)]
	pub shared: SharedParams,

	#[command(subcommand)]
	pub command: Command,
}

/// A `Live` variant [`State`]
#[derive(Debug, Clone, clap::Args)]
pub struct LiveState {
	/// The url to connect to.
	#[arg(
		short,
		long,
		value_parser = parse::url,
	)]
	uri: String,

	/// The block hash at which to fetch the state.
	///
	/// If non provided, then the latest finalized head is used. This is particularly useful
	/// for [`Command::OnRuntimeUpgrade`].
	#[arg(
		short,
		long,
		value_parser = parse::hash,
	)]
	at: Option<String>,

	/// A pallet to scrape. Can be provided multiple times. If empty, entire chain state will
	/// be scraped.
	#[arg(short, long, num_args = 1..)]
	pallet: Vec<String>,

	/// Fetch the child-keys as well.
	///
	/// Default is `false`, if specific `--pallets` are specified, `true` otherwise. In other
	/// words, if you scrape the whole state the child tree data is included out of the box.
	/// Otherwise, it must be enabled explicitly using this flag.
	#[arg(long)]
	child_tree: bool,
}

/// The source of runtime *state* to use.
#[derive(Debug, Clone, clap::Subcommand)]
pub enum State {
	/// Use a state snapshot as the source of runtime state.
	///
	/// This can be crated by passing a value to [`State::Live::snapshot_path`].
	Snap {
		#[arg(short, long)]
		snapshot_path: PathBuf,
	},

	/// Use a live chain as the source of runtime state.
	Live(LiveState),
}

impl State {
	/// Create the [`remote_externalities::RemoteExternalities`] using [`remote-externalities`] from
	/// self.
	///
	/// This will override the code as it sees fit based on [`SharedParams::Runtime`]. It will also
	/// check the spec-version and name.
	pub(crate) async fn into_ext<Block: BlockT + DeserializeOwned, HostFns: HostFunctions>(
		&self,
		shared: &SharedParams,
		executor: &WasmExecutor<HostFns>,
	) -> sc_cli::Result<RemoteExternalities<Block>>
	where
		Block::Hash: FromStr,
		Block::Header: DeserializeOwned,
		Block::Hash: DeserializeOwned,
		<Block::Hash as FromStr>::Err: Debug,
	{
		let builder = match self {
			State::Snap { snapshot_path } =>
				Builder::<Block>::new().mode(Mode::Offline(OfflineConfig {
					state_snapshot: SnapshotConfig::new(snapshot_path),
				})),
			State::Live(LiveState { pallet, uri, at, child_tree }) => {
				let at = match at {
					Some(at_str) => Some(hash_of::<Block>(at_str)?),
					None => None,
				};
				Builder::<Block>::new().mode(Mode::Online(OnlineConfig {
					at,
					transport: uri.to_owned().into(),
					state_snapshot: None,
					pallets: pallet.clone(),
					child_trie: *child_tree,
					hashed_keys: vec![
						// we always download the code, but we almost always won't use it, based on
						// `Runtime`.
						well_known_keys::CODE.to_vec(),
						// we will always download this key, since it helps detect if we should do
						// runtime migration or not.
						[twox_128(b"System"), twox_128(b"LastRuntimeUpgrade")].concat(),
						[twox_128(b"System"), twox_128(b"Number")].concat(),
					],
					hashed_prefixes: vec![],
				}))
			},
		};

		// possibly overwrite the state version, should hardly be needed.
		let builder = if let Some(state_version) = shared.overwrite_state_version {
			log::warn!(
				target: LOG_TARGET,
				"overwriting state version to {:?}, you better know what you are doing.",
				state_version
			);
			builder.overwrite_state_version(state_version)
		} else {
			builder
		};

		// then, we prepare to replace the code based on what the CLI wishes.
		let maybe_code_to_overwrite = match shared.runtime {
			Runtime::Path(ref path) => Some(std::fs::read(path).map_err(|e| {
				format!("error while reading runtime file from {:?}: {:?}", path, e)
			})?),
			Runtime::Existing => None,
		};

		// build the main ext.
		let mut ext = builder.build().await?;

		// actually replace the code if needed.
		if let Some(new_code) = maybe_code_to_overwrite {
			let original_code = ext
				.execute_with(|| sp_io::storage::get(well_known_keys::CODE))
				.expect("':CODE:' is always downloaded in try-runtime-cli; qed");

			// NOTE: see the impl notes of `read_runtime_version`, the ext is almost not used here,
			// only as a backup.
			ext.insert(well_known_keys::CODE.to_vec(), new_code.clone());
			let old_version = <RuntimeVersion as Decode>::decode(
				&mut &*executor.read_runtime_version(&original_code, &mut ext.ext()).unwrap(),
			)
			.unwrap();
			log::info!(
				target: LOG_TARGET,
				"original spec: {:?}-{:?}",
				old_version.spec_name,
				old_version.spec_version
			);
			let new_version = <RuntimeVersion as Decode>::decode(
				&mut &*executor.read_runtime_version(&new_code, &mut ext.ext()).unwrap(),
			)
			.unwrap();
			log::info!(
				target: LOG_TARGET,
				"new spec: {:?}-{:?}",
				new_version.spec_name,
				new_version.spec_version
			);

			if new_version.spec_name != old_version.spec_name {
				return Err("Spec names must match.".into())
			}
		}

		// whatever runtime we have in store now must have been compiled with try-runtime feature.
		if !ensure_try_runtime::<Block, HostFns>(&executor, &mut ext) {
			return Err("given runtime is NOT compiled with try-runtime feature!".into())
		}

		Ok(ext)
	}
}

impl TryRuntimeCmd {
	pub async fn run<Block, HostFns>(&self) -> sc_cli::Result<()>
	where
		Block: BlockT<Hash = H256> + DeserializeOwned,
		Block::Header: DeserializeOwned,
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
		<NumberFor<Block> as FromStr>::Err: Debug,
		<NumberFor<Block> as TryInto<u64>>::Error: Debug,
		NumberFor<Block>: FromStr,
		HostFns: HostFunctions,
	{
		match &self.command {
			Command::OnRuntimeUpgrade(ref cmd) =>
				commands::on_runtime_upgrade::on_runtime_upgrade::<Block, HostFns>(
					self.shared.clone(),
					cmd.clone(),
				)
				.await,
			Command::OffchainWorker(cmd) =>
				commands::offchain_worker::offchain_worker::<Block, HostFns>(
					self.shared.clone(),
					cmd.clone(),
				)
				.await,
			Command::ExecuteBlock(cmd) =>
				commands::execute_block::execute_block::<Block, HostFns>(
					self.shared.clone(),
					cmd.clone(),
				)
				.await,
			Command::FollowChain(cmd) =>
				commands::follow_chain::follow_chain::<Block, HostFns>(
					self.shared.clone(),
					cmd.clone(),
				)
				.await,
			Command::CreateSnapshot(cmd) =>
				commands::create_snapshot::create_snapshot::<Block>(cmd.clone()).await,
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

pub(crate) fn build_executor<H: HostFunctions>(shared: &SharedParams) -> WasmExecutor<H> {
	let heap_pages = shared.heap_pages.or(Some(2048));
	let max_runtime_instances = 8;
	let runtime_cache_size = 2;

	WasmExecutor::new(
		sc_executor::WasmExecutionMethod::Interpreted,
		heap_pages,
		max_runtime_instances,
		None,
		runtime_cache_size,
	)
}

/// Ensure that the given `ext` is compiled with `try-runtime`
fn ensure_try_runtime<Block: BlockT, HostFns: HostFunctions>(
	executor: &WasmExecutor<HostFns>,
	ext: &mut TestExternalities,
) -> bool {
	use sp_api::RuntimeApiInfo;
	let final_code = ext
		.execute_with(|| sp_io::storage::get(well_known_keys::CODE))
		.expect("':CODE:' is always downloaded in try-runtime-cli; qed");
	let final_version = <RuntimeVersion as Decode>::decode(
		&mut &*executor.read_runtime_version(&final_code, &mut ext.ext()).unwrap(),
	)
	.unwrap();
	final_version
		.api_version(&<dyn frame_try_runtime::TryRuntime<Block>>::ID)
		.is_some()
}

/// Execute the given `method` and `data` on top of `ext`, returning the results (encoded) and the
/// state `changes`.
pub(crate) fn state_machine_call<Block: BlockT, HostFns: HostFunctions>(
	ext: &TestExternalities,
	executor: &WasmExecutor<HostFns>,
	method: &'static str,
	data: &[u8],
	extensions: Extensions,
) -> sc_cli::Result<(OverlayedChanges, Vec<u8>)> {
	let mut changes = Default::default();
	let encoded_results = StateMachine::new(
		&ext.backend,
		&mut changes,
		executor,
		method,
		data,
		extensions,
		&sp_state_machine::backend::BackendRuntimeCode::new(&ext.backend).runtime_code()?,
		sp_core::testing::TaskExecutor::new(),
	)
	.execute(sp_state_machine::ExecutionStrategy::AlwaysWasm)
	.map_err(|e| format!("failed to execute '{}': {}", method, e))
	.map_err::<sc_cli::Error, _>(Into::into)?;

	Ok((changes, encoded_results))
}

/// Same as [`state_machine_call`], but it also computes and prints the storage proof in different
/// size and formats.
///
/// Make sure [`LOG_TARGET`] is enabled in logging.
pub(crate) fn state_machine_call_with_proof<Block: BlockT, HostFns: HostFunctions>(
	ext: &TestExternalities,
	executor: &WasmExecutor<HostFns>,
	method: &'static str,
	data: &[u8],
	extensions: Extensions,
) -> sc_cli::Result<(OverlayedChanges, Vec<u8>)> {
	use parity_scale_codec::Encode;
	use sp_core::hexdisplay::HexDisplay;

	let mut changes = Default::default();
	let backend = ext.backend.clone();
	let runtime_code_backend = sp_state_machine::backend::BackendRuntimeCode::new(&backend);
	let proving_backend =
		TrieBackendBuilder::wrap(&backend).with_recorder(Default::default()).build();
	let runtime_code = runtime_code_backend.runtime_code()?;

	let pre_root = *backend.root();
	let encoded_results = StateMachine::new(
		&proving_backend,
		&mut changes,
		executor,
		method,
		data,
		extensions,
		&runtime_code,
		sp_core::testing::TaskExecutor::new(),
	)
	.execute(sp_state_machine::ExecutionStrategy::AlwaysWasm)
	.map_err(|e| format!("failed to execute {}: {}", method, e))
	.map_err::<sc_cli::Error, _>(Into::into)?;

	let proof = proving_backend
		.extract_proof()
		.expect("A recorder was set and thus, a storage proof can be extracted; qed");
	let proof_size = proof.encoded_size();
	let compact_proof = proof
		.clone()
		.into_compact_proof::<sp_runtime::traits::BlakeTwo256>(pre_root)
		.map_err(|e| {
			log::error!(target: LOG_TARGET, "failed to generate compact proof {}: {:?}", method, e);
			e
		})
		.unwrap_or(CompactProof { encoded_nodes: Default::default() });

	let compact_proof_size = compact_proof.encoded_size();
	let compressed_proof = zstd::stream::encode_all(&compact_proof.encode()[..], 0)
		.map_err(|e| {
			log::error!(
				target: LOG_TARGET,
				"failed to generate compressed proof {}: {:?}",
				method,
				e
			);
			e
		})
		.unwrap_or_default();

	let proof_nodes = proof.into_nodes();

	let humanize = |s| {
		if s < 1024 * 1024 {
			format!("{:.2} KB ({} bytes)", s as f64 / 1024f64, s)
		} else {
			format!(
				"{:.2} MB ({} KB) ({} bytes)",
				s as f64 / (1024f64 * 1024f64),
				s as f64 / 1024f64,
				s
			)
		}
	};
	log::debug!(
		target: LOG_TARGET,
		"proof: 0x{}... / {} nodes",
		HexDisplay::from(&proof_nodes.iter().flatten().cloned().take(10).collect::<Vec<_>>()),
		proof_nodes.len()
	);
	log::debug!(target: LOG_TARGET, "proof size: {}", humanize(proof_size));
	log::debug!(target: LOG_TARGET, "compact proof size: {}", humanize(compact_proof_size),);
	log::debug!(
		target: LOG_TARGET,
		"zstd-compressed compact proof {}",
		humanize(compressed_proof.len()),
	);

	log::debug!(target: LOG_TARGET, "{} executed without errors.", method);

	Ok((changes, encoded_results))
}

pub(crate) fn rpc_err_handler(error: impl Debug) -> &'static str {
	log::error!(target: LOG_TARGET, "rpc error: {:?}", error);
	"rpc error."
}
