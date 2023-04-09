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
//! 1. <https://docs.substrate.io/reference/command-line-tools/try-runtime/>
//! 2. <https://www.crowdcast.io/e/substrate-seminar/41>
//! 3. <https://docs.substrate.io/fundamentals/runtime-development/>
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
//! <https://forum.polkadot.network/t/state-trie-migration/852> for more info).
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
//!   runtime.
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
//! ## Note on signature and state-root checks
//!
//! All of the commands calling into `TryRuntime_execute_block` ([`Command::ExecuteBlock`] and
//! [`Command::FollowChain`]) disable both state root and signature checks. This is because in 99%
//! of the cases, the runtime that is being tested is different from the one that is stored in the
//! canonical chain state. This implies:
//!
//! 1. the state root will NEVER match, because `:CODE:` is different between the two.
//! 2. replaying all transactions will fail, because the spec-version is part of the transaction
//!    signature.
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
//! #[cfg(feature = "try-runtime")]
//! fn pre_upgrade() -> Result<Vec<u8>, &'static str> {}
//!
//! #[cfg(feature = "try-runtime")]
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
//! Similarly, each pallet can expose a function in `#[pallet::hooks]` section as follows:
//!
//! ```ignore
//! #[cfg(feature = "try-runtime")]
//! fn try_state(_: BlockNumber) -> Result<(), &'static str> {}
//! ```
//!
//! which is called on numerous code paths in the try-runtime tool. These checks should ensure that
//! the state of the pallet is consistent and correct. See `frame_support::try_runtime::TryState`
//! for more info.
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
//! For the following examples, we assume the existence of the following:
//!
//! 1. a substrate node compiled without `--feature try-runtime`, called `substrate`. This will be
//! the running node that you connect to. then, after some changes to this node, you compile it with
//! `--features try-runtime`. This gives you:
//! 2. a substrate binary that has the try-runtime sub-command enabled.
//! 3. a wasm blob that has try-runtime functionality.
//!
//! ```bash
//! # this is like your running deployed node.
//! cargo build --release && cp target/release/substrate .
//!
//! # this is like your WIP branch.
//! cargo build --release --features try-runtime
//! cp target/release/substrate substrate-try-runtime
//! cp ./target/release/wbuild/kitchensink-runtime/kitchensink_runtime.wasm runtime-try-runtime.wasm
//! ```
//!
//! > The above example is with `substrate`'s `kitchensink-runtime`, but is applicable to any
//! > substrate-based chain that has implemented `try-runtime-cli`.
//!
//! * If you run `try-runtime` subcommand against `substrate` binary listed above, you get the
//!   following error.
//!
//! ```bash
//! [substrate] ./substrate try-runtime
//! Error: Input("TryRuntime wasn't enabled when building the node. You can enable it with `--features try-runtime`.")
//! ```
//!
//! * If you run the same against `substrate-try-runtime`, it will work.
//!
//! ```bash
//! [substrate] ./substrate-try-runtime try-runtime
//! Try some command against runtime state
//!
//! Usage: substrate-try-runtime try-runtime [OPTIONS] --runtime <RUNTIME> <COMMAND>
//!
//! Commands:
//!   on-runtime-upgrade  Execute the migrations of the "local runtime"
//!   execute-block       Executes the given block against some state
//!   offchain-worker     Executes *the offchain worker hooks* of a given block against some state
//!   follow-chain        Follow the given chain's finalized blocks and apply all of its extrinsics
//!   create-snapshot     Create a new snapshot file
//!   help                Print this message or the help of the given subcommand(s)
//!
//! Options:
//!       --chain <CHAIN_SPEC>
//!           Specify the chain specification
//!       --dev
//!           Specify the development chain
//!   -d, --base-path <PATH>
//!           Specify custom base path
//!   -l, --log <LOG_PATTERN>...
//!           Sets a custom logging filter. Syntax is `<target>=<level>`, e.g. -lsync=debug
//!       --detailed-log-output
//!           Enable detailed log output
//!       --disable-log-color
//!           Disable log color output
//!       --enable-log-reloading
//!           Enable feature to dynamically update and reload the log filter
//!       --tracing-targets <TARGETS>
//!           Sets a custom profiling filter. Syntax is the same as for logging: `<target>=<level>`
//!       --tracing-receiver <RECEIVER>
//!           Receiver to process tracing messages [default: log] [possible values: log]
//!       --runtime <RUNTIME>
//!           The runtime to use
//!       --wasm-execution <METHOD>
//!           Type of wasm execution used [default: compiled] [possible values: interpreted-i-know-what-i-do, compiled]
//!       --wasm-instantiation-strategy <STRATEGY>
//!           The WASM instantiation method to use [default: pooling-copy-on-write] [possible values: pooling-copy-on-write, recreate-instance-copy-on-write, pooling, recreate-instance, legacy-instance-reuse]
//!       --heap-pages <HEAP_PAGES>
//!           The number of 64KB pages to allocate for Wasm execution. Defaults to [`sc_service::Configuration.default_heap_pages`]
//!       --overwrite-state-version <OVERWRITE_STATE_VERSION>
//!           Overwrite the `state_version`
//!   -h, --help
//!           Print help information (use `--help` for more detail)
//!   -V, --version
//!           Print version information
//! ```
//!
//! * Run the migrations of a given runtime on top of a live state.
//!
//! ```bash
//! # assuming there's `./substrate --dev --tmp --ws-port 9999` or similar running.
//! ./substrate-try-runtime \
//!     try-runtime \
//!     --runtime kitchensink_runtime.wasm \
//!     -lruntime=debug \
//!     on-runtime-upgrade \
//!     live --uri ws://localhost:9999
//! ```
//!
//! * Same as the previous one, but run it at specific block number's state. This means that this
//! block hash's state shall not yet have been pruned in `rpc.polkadot.io`.
//!
//! ```bash
//! ./substrate-try-runtime \
//!     try-runtime \
//!     --runtime kitchensink_runtime.wasm \
//!     -lruntime=debug \
//!     on-runtime-upgrade \
//!     live --uri ws://localhost:9999 \
//!     # replace with your desired block hash!
//!     --at 0xa1b16c1efd889a9f17375ec4dd5c1b4351a2be17fa069564fced10d23b9b3836
//! ```
//!
//! * Executing the same command with the [`Runtime::Existing`] will fail because the existing
//!   runtime, stored onchain in `substrate` binary that we compiled earlier does not have
//!   `try-runtime` feature!
//!
//! ```bash
//! ./substrate-try-runtime try-runtime --runtime existing -lruntime=debug on-runtime-upgrade live --uri ws://localhost:9999
//! ...
//! Error: Input("given runtime is NOT compiled with try-runtime feature!")
//! ```
//!
//! * Now, let's use a snapshot file. First, we create the snapshot:
//!
//! ```bash
//! ./substrate-try-runtime try-runtime --runtime existing -lruntime=debug create-snapshot --uri ws://localhost:9999
//! 2022-12-13 10:28:17.516  INFO main try-runtime::cli: snapshot path not provided (-s), using 'node-268@latest.snap'
//! 2022-12-13 10:28:17.516  INFO                 main remote-ext: since no at is provided, setting it to latest finalized head, 0xe7d0b614dfe89af65b33577aae46a6f958c974bf52f8a5e865a0f4faeb578d22
//! 2022-12-13 10:28:17.516  INFO                 main remote-ext: since no prefix is filtered, the data for all pallets will be downloaded
//! 2022-12-13 10:28:17.550  INFO                 main remote-ext: writing snapshot of 1611464 bytes to "node-268@latest.snap"
//! 2022-12-13 10:28:17.551  INFO                 main remote-ext: initialized state externalities with storage root 0x925e4e95de4c08474fb7f976c4472fa9b8a1091619cd7820a793bf796ee6d932 and state_version V1
//! ```
//!
//! > Note that the snapshot contains the `existing` runtime, which does not have the correct
//! > `try-runtime` feature. In the following commands, we still need to overwrite the runtime.
//!
//! Then, we can use it to have the same command as before, `on-runtime-upgrade`
//!
//! ```bash
//! try-runtime \
//!     --runtime runtime-try-runtime.wasm \
//!     -lruntime=debug \
//!     on-runtime-upgrade \
//!     snap -s node-268@latest.snap
//! ```
//!
//! * Execute the latest finalized block with the given runtime.
//!
//! ```bash
//! ./substrate-try-runtime try-runtime \
//!     --runtime runtime-try-runtime.wasm \
//!     -lruntime=debug \
//!     execute-block live \
//!     --uri ws://localhost:999
//! ```
//!
//! This can still be customized at a given block with `--at`. If you want to use a snapshot, you
//! can still use `--block-ws-uri` to provide a node form which the block data can be fetched.
//!
//! Moreover, this runs the `frame_support::try_runtime::TryState` hooks as well. The hooks to run
//! can be customized with the `--try-state`. For example:
//!
//! ```bash
//! ./substrate-try-runtime try-runtime \
//!     --runtime runtime-try-runtime.wasm \
//!     -lruntime=debug \
//!     execute-block live \
//!     --try-state System,Staking \
//!     --uri ws://localhost:999
//! ```
//!
//! Will only run the `try-state` of the two given pallets. See
//! [`frame_try_runtime::TryStateSelect`] for more information.
//!
//! * Follow our live chain's blocks using `follow-chain`, whilst running the try-state of 3 pallets
//!   in a round robin fashion
//!
//! ```bash
//! ./substrate-try-runtime \
//!     try-runtime \
//!     --runtime runtime-try-runtime.wasm \
//!     -lruntime=debug \
//!     follow-chain \
//!     --uri ws://localhost:9999 \
//!     --try-state rr-3
//! ```

#![cfg(feature = "try-runtime")]

use crate::block_building_info::BlockBuildingInfoProvider;
use parity_scale_codec::Decode;
use remote_externalities::{
	Builder, Mode, OfflineConfig, OnlineConfig, RemoteExternalities, SnapshotConfig,
	TestExternalities,
};
use sc_cli::{
	execution_method_from_cli, CliConfiguration, RuntimeVersion, WasmExecutionMethod,
	WasmtimeInstantiationStrategy, DEFAULT_WASMTIME_INSTANTIATION_STRATEGY,
	DEFAULT_WASM_EXECUTION_METHOD,
};
use sc_executor::{
	sp_wasm_interface::HostFunctions, HeapAllocStrategy, WasmExecutor, DEFAULT_HEAP_ALLOC_STRATEGY,
};
use sp_api::HashT;
use sp_core::{
	hexdisplay::HexDisplay,
	offchain::{
		testing::{TestOffchainExt, TestTransactionPoolExt},
		OffchainDbExt, OffchainWorkerExt, TransactionPoolExt,
	},
	storage::well_known_keys,
	traits::{CallContext, ReadRuntimeVersion, ReadRuntimeVersionExt},
	twox_128, H256,
};
use sp_externalities::Extensions;
use sp_inherents::InherentData;
use sp_keystore::{testing::MemoryKeystore, KeystoreExt};
use sp_runtime::{
	traits::{BlakeTwo256, Block as BlockT, NumberFor},
	DeserializeOwned, Digest,
};
use sp_state_machine::{CompactProof, OverlayedChanges, StateMachine, TrieBackendBuilder};
use sp_version::StateVersion;
use std::{fmt::Debug, path::PathBuf, str::FromStr};

pub mod block_building_info;
pub mod commands;
pub(crate) mod parse;
pub(crate) const LOG_TARGET: &str = "try-runtime::cli";

/// Possible commands of `try-runtime`.
#[derive(Debug, Clone, clap::Subcommand)]
pub enum Command {
	/// Execute the migrations of the given runtime
	///
	/// This uses a custom runtime api call, namely "TryRuntime_on_runtime_upgrade". The code path
	/// only triggers all of the `on_runtime_upgrade` hooks in the runtime, and optionally
	/// `try_state`.
	///
	/// See [`frame_try_runtime::TryRuntime`] and
	/// [`commands::on_runtime_upgrade::OnRuntimeUpgradeCmd`] for more information.
	OnRuntimeUpgrade(commands::on_runtime_upgrade::OnRuntimeUpgradeCmd),

	/// Executes the given block against some state.
	///
	/// This uses a custom runtime api call, namely "TryRuntime_execute_block". Some checks, such
	/// as state-root and signature checks are always disabled, and additional checks like
	/// `try-state` can be enabled.
	///
	/// See [`frame_try_runtime::TryRuntime`] and [`commands::execute_block::ExecuteBlockCmd`] for
	/// more information.
	ExecuteBlock(commands::execute_block::ExecuteBlockCmd),

	/// Executes *the offchain worker hooks* of a given block against some state.
	///
	/// This executes the same runtime api as normal block import, namely
	/// `OffchainWorkerApi_offchain_worker`.
	///
	/// See [`frame_try_runtime::TryRuntime`] and [`commands::offchain_worker::OffchainWorkerCmd`]
	/// for more information.
	OffchainWorker(commands::offchain_worker::OffchainWorkerCmd),

	/// Follow the given chain's finalized blocks and apply all of its extrinsics.
	///
	/// This is essentially repeated calls to [`Command::ExecuteBlock`].
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
	///
	/// This can only work if the block format between the remote chain and the new runtime being
	/// tested has remained the same, otherwise block decoding might fail.
	FollowChain(commands::follow_chain::FollowChainCmd),

	/// Produce a series of empty, consecutive blocks and execute them one-by-one.
	///
	/// To compare it with [`Command::FollowChain`]:
	///  - we don't have the delay of the original blocktime (for Polkadot 6s), but instead, we
	///    execute every block immediately
	///  - the only data that will be put into blocks are pre-runtime digest items and inherent
	///    extrinsics; both things should be defined in your node CLI handling level
	FastForward(commands::fast_forward::FastForwardCmd),

	/// Create a new snapshot file.
	CreateSnapshot(commands::create_snapshot::CreateSnapshotCmd),
}

#[derive(Debug, Clone)]
pub enum Runtime {
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
	pub shared_params: sc_cli::SharedParams,

	/// The runtime to use.
	///
	/// Must be a path to a wasm blob, compiled with `try-runtime` feature flag.
	///
	/// Or, `existing`, indicating that you don't want to overwrite the runtime. This will use
	/// whatever comes from the remote node, or the snapshot file. This will most likely not work
	/// against a remote node, as no (sane) blockchain should compile its onchain wasm with
	/// `try-runtime` feature.
	#[arg(long)]
	pub runtime: Runtime,

	/// Type of wasm execution used.
	#[arg(
		long = "wasm-execution",
		value_name = "METHOD",
		value_enum,
		ignore_case = true,
		default_value_t = DEFAULT_WASM_EXECUTION_METHOD,
	)]
	pub wasm_method: WasmExecutionMethod,

	/// The WASM instantiation method to use.
	///
	/// Only has an effect when `wasm-execution` is set to `compiled`.
	#[arg(
		long = "wasm-instantiation-strategy",
		value_name = "STRATEGY",
		default_value_t = DEFAULT_WASMTIME_INSTANTIATION_STRATEGY,
		value_enum,
	)]
	pub wasmtime_instantiation_strategy: WasmtimeInstantiationStrategy,

	/// The number of 64KB pages to allocate for Wasm execution. Defaults to
	/// [`sc_service::Configuration.default_heap_pages`].
	#[arg(long)]
	pub heap_pages: Option<u64>,

	/// Path to a file to export the storage proof into (as a JSON).
	/// If several blocks are executed, the path is interpreted as a folder
	/// where one file per block will be written (named `{block_number}-{block_hash}`).
	#[clap(long)]
	pub export_proof: Option<PathBuf>,

	/// Overwrite the `state_version`.
	///
	/// Otherwise `remote-externalities` will automatically set the correct state version.
	#[arg(long, value_parser = parse::state_version)]
	pub overwrite_state_version: Option<StateVersion>,
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
	/// If non provided, then the latest finalized head is used.
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
		state_snapshot: Option<SnapshotConfig>,
		try_runtime_check: bool,
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
					state_snapshot,
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
				"original spec: {:?}-{:?}, code hash: {:?}",
				old_version.spec_name,
				old_version.spec_version,
				HexDisplay::from(BlakeTwo256::hash(&original_code).as_fixed_bytes()),
			);
			let new_version = <RuntimeVersion as Decode>::decode(
				&mut &*executor.read_runtime_version(&new_code, &mut ext.ext()).unwrap(),
			)
			.unwrap();
			log::info!(
				target: LOG_TARGET,
				"new spec: {:?}-{:?}, code hash: {:?}",
				new_version.spec_name,
				new_version.spec_version,
				HexDisplay::from(BlakeTwo256::hash(&new_code).as_fixed_bytes())
			);

			if new_version.spec_name != old_version.spec_name {
				return Err("Spec names must match.".into())
			}
		}

		// whatever runtime we have in store now must have been compiled with try-runtime feature.
		if try_runtime_check {
			if !ensure_try_runtime::<Block, HostFns>(&executor, &mut ext) {
				return Err("given runtime is NOT compiled with try-runtime feature!".into())
			}
		}

		Ok(ext)
	}
}

impl TryRuntimeCmd {
	pub async fn run<Block, HostFns, BBIP>(
		&self,
		block_building_info_provider: Option<BBIP>,
	) -> sc_cli::Result<()>
	where
		Block: BlockT<Hash = H256> + DeserializeOwned,
		Block::Header: DeserializeOwned,
		Block::Hash: FromStr,
		<Block::Hash as FromStr>::Err: Debug,
		<NumberFor<Block> as FromStr>::Err: Debug,
		<NumberFor<Block> as TryInto<u64>>::Error: Debug,
		NumberFor<Block>: FromStr,
		HostFns: HostFunctions,
		BBIP: BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>>,
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
			Command::FastForward(cmd) =>
				commands::fast_forward::fast_forward::<Block, HostFns, BBIP>(
					self.shared.clone(),
					cmd.clone(),
					block_building_info_provider,
				)
				.await,
			Command::CreateSnapshot(cmd) =>
				commands::create_snapshot::create_snapshot::<Block, HostFns>(
					self.shared.clone(),
					cmd.clone(),
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
pub(crate) fn full_extensions<H: HostFunctions>(wasm_executor: WasmExecutor<H>) -> Extensions {
	let mut extensions = Extensions::default();
	let (offchain, _offchain_state) = TestOffchainExt::new();
	let (pool, _pool_state) = TestTransactionPoolExt::new();
	let keystore = MemoryKeystore::new();
	extensions.register(OffchainDbExt::new(offchain.clone()));
	extensions.register(OffchainWorkerExt::new(offchain));
	extensions.register(KeystoreExt::new(keystore));
	extensions.register(TransactionPoolExt::new(pool));
	extensions.register(ReadRuntimeVersionExt::new(wasm_executor));

	extensions
}

/// Build wasm executor by default config.
pub(crate) fn build_executor<H: HostFunctions>(shared: &SharedParams) -> WasmExecutor<H> {
	let heap_pages = shared
		.heap_pages
		.map_or(DEFAULT_HEAP_ALLOC_STRATEGY, |p| HeapAllocStrategy::Static { extra_pages: p as _ });

	WasmExecutor::builder()
		.with_execution_method(execution_method_from_cli(
			shared.wasm_method,
			shared.wasmtime_instantiation_strategy,
		))
		.with_onchain_heap_alloc_strategy(heap_pages)
		.with_offchain_heap_alloc_strategy(heap_pages)
		.build()
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
		CallContext::Offchain,
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
	maybe_export_proof: Option<PathBuf>,
) -> sc_cli::Result<(OverlayedChanges, Vec<u8>)> {
	use parity_scale_codec::Encode;

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
		CallContext::Offchain,
	)
	.execute(sp_state_machine::ExecutionStrategy::AlwaysWasm)
	.map_err(|e| format!("failed to execute {}: {}", method, e))
	.map_err::<sc_cli::Error, _>(Into::into)?;

	let proof = proving_backend
		.extract_proof()
		.expect("A recorder was set and thus, a storage proof can be extracted; qed");

	if let Some(path) = maybe_export_proof {
		let mut file = std::fs::File::create(&path).map_err(|e| {
			log::error!(
				target: LOG_TARGET,
				"Failed to create file {}: {:?}",
				path.to_string_lossy(),
				e
			);
			e
		})?;

		log::info!(target: LOG_TARGET, "Writing storage proof to {}", path.to_string_lossy());

		use std::io::Write as _;
		file.write_all(storage_proof_to_raw_json(&proof).as_bytes()).map_err(|e| {
			log::error!(
				target: LOG_TARGET,
				"Failed to write storage proof to {}: {:?}",
				path.to_string_lossy(),
				e
			);
			e
		})?;
	}

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

/// Converts a [`sp_state_machine::StorageProof`] into a JSON string.
fn storage_proof_to_raw_json(storage_proof: &sp_state_machine::StorageProof) -> String {
	serde_json::Value::Object(
		storage_proof
			.to_memory_db::<sp_runtime::traits::BlakeTwo256>()
			.drain()
			.iter()
			.map(|(key, (value, _n))| {
				(
					format!("0x{}", hex::encode(key.as_bytes())),
					serde_json::Value::String(format!("0x{}", hex::encode(value))),
				)
			})
			.collect(),
	)
	.to_string()
}
