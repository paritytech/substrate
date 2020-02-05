// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::{str::FromStr, path::PathBuf};
use structopt::{StructOpt, clap::arg_enum};
use sc_service::{
	AbstractService, Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
	config::DatabaseConfig,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use crate::VersionInfo;
use crate::error;
use std::fmt::Debug;
use log::info;
use sc_network::config::build_multiaddr;
use std::io;
use std::fs;
use std::io::{Read, Write, Seek};
use sp_runtime::generic::BlockId;
use crate::runtime::run_until_exit;
use crate::node_key::node_key_config;
use crate::execution_strategy::*;

pub use crate::execution_strategy::ExecutionStrategy;

impl Into<sc_client_api::ExecutionStrategy> for ExecutionStrategy {
	fn into(self) -> sc_client_api::ExecutionStrategy {
		match self {
			ExecutionStrategy::Native => sc_client_api::ExecutionStrategy::NativeWhenPossible,
			ExecutionStrategy::Wasm => sc_client_api::ExecutionStrategy::AlwaysWasm,
			ExecutionStrategy::Both => sc_client_api::ExecutionStrategy::Both,
			ExecutionStrategy::NativeElseWasm => sc_client_api::ExecutionStrategy::NativeElseWasm,
		}
	}
}

arg_enum! {
	/// How to execute Wasm runtime code
	#[allow(missing_docs)]
	#[derive(Debug, Clone, Copy)]
	pub enum WasmExecutionMethod {
		// Uses an interpreter.
		Interpreted,
		// Uses a compiled runtime.
		Compiled,
	}
}

impl WasmExecutionMethod {
	/// Returns list of variants that are not disabled by feature flags.
	fn enabled_variants() -> Vec<&'static str> {
		Self::variants()
			.iter()
			.cloned()
			.filter(|&name| cfg!(feature = "wasmtime") || name != "Compiled")
			.collect()
	}
}

impl Into<sc_service::config::WasmExecutionMethod> for WasmExecutionMethod {
	fn into(self) -> sc_service::config::WasmExecutionMethod {
		match self {
			WasmExecutionMethod::Interpreted => sc_service::config::WasmExecutionMethod::Interpreted,
			#[cfg(feature = "wasmtime")]
			WasmExecutionMethod::Compiled => sc_service::config::WasmExecutionMethod::Compiled,
			#[cfg(not(feature = "wasmtime"))]
			WasmExecutionMethod::Compiled => panic!(
				"Substrate must be compiled with \"wasmtime\" feature for compiled Wasm execution"
			),
		}
	}
}

arg_enum! {
	/// Whether off-chain workers are enabled.
	#[allow(missing_docs)]
	#[derive(Debug, Clone)]
	pub enum OffchainWorkerEnabled {
		Always,
		Never,
		WhenValidating,
	}
}

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, StructOpt, Clone)]
pub struct SharedParams {
	/// Specify the chain specification (one of dev, local or staging).
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain.
	#[structopt(long = "dev")]
	pub dev: bool,

	/// Specify custom base path.
	#[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
	pub base_path: Option<PathBuf>,

	/// Sets a custom logging filter.
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	pub log: Option<String>,
}

/// Parameters for block import.
#[derive(Debug, StructOpt, Clone)]
pub struct ImportParams {
	/// Specify the state pruning mode, a number of blocks to keep or 'archive'.
	///
	/// Default is to keep all block states if the node is running as a
	/// validator (i.e. 'archive'), otherwise state is only kept for the last
	/// 256 blocks.
	#[structopt(long = "pruning", value_name = "PRUNING_MODE")]
	pub pruning: Option<String>,

	/// Force start with unsafe pruning settings.
	///
	/// When running as a validator it is highly recommended to disable state
	/// pruning (i.e. 'archive') which is the default. The node will refuse to
	/// start as a validator if pruning is enabled unless this option is set.
	#[structopt(long = "unsafe-pruning")]
	pub unsafe_pruning: bool,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::enabled_variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub execution_strategies: ExecutionStrategies,

	/// Limit the memory the database cache can use.
	#[structopt(long = "db-cache", value_name = "MiB", default_value = "1024")]
	pub database_cache_size: u32,

	/// Specify the state cache size.
	#[structopt(long = "state-cache-size", value_name = "Bytes", default_value = "67108864")]
	pub state_cache_size: usize,
}

/// Parameters used to create the network configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct NetworkConfigurationParams {
	/// Specify a list of bootnodes.
	#[structopt(long = "bootnodes", value_name = "URL")]
	pub bootnodes: Vec<String>,

	/// Specify a list of reserved node addresses.
	#[structopt(long = "reserved-nodes", value_name = "URL")]
	pub reserved_nodes: Vec<String>,

	/// Whether to only allow connections to/from reserved nodes.
	///
	/// If you are a validator your node might still connect to other validator
	/// nodes regardless of whether they are defined as reserved nodes.
	#[structopt(long = "reserved-only")]
	pub reserved_only: bool,

	/// Specify a list of sentry node public addresses.
	#[structopt(
		long = "sentry-nodes",
		value_name = "URL",
		conflicts_with_all = &[ "sentry" ]
	)]
	pub sentry_nodes: Vec<String>,

	/// Listen on this multiaddress.
	#[structopt(long = "listen-addr", value_name = "LISTEN_ADDR")]
	pub listen_addr: Vec<String>,

	/// Specify p2p protocol TCP port.
	///
	/// Only used if --listen-addr is not specified.
	#[structopt(long = "port", value_name = "PORT")]
	pub port: Option<u16>,

	/// Allow connecting to private IPv4 addresses (as specified in
	/// [RFC1918](https://tools.ietf.org/html/rfc1918)), unless the address was passed with
	/// `--reserved-nodes` or `--bootnodes`.
	#[structopt(long = "no-private-ipv4")]
	pub no_private_ipv4: bool,

	/// Specify the number of outgoing connections we're trying to maintain.
	#[structopt(long = "out-peers", value_name = "COUNT", default_value = "25")]
	pub out_peers: u32,

	/// Specify the maximum number of incoming connections we're accepting.
	#[structopt(long = "in-peers", value_name = "COUNT", default_value = "25")]
	pub in_peers: u32,

	/// Disable mDNS discovery.
	///
	/// By default, the network will use mDNS to discover other nodes on the
	/// local network. This disables it. Automatically implied when using --dev.
	#[structopt(long = "no-mdns")]
	pub no_mdns: bool,

	/// Maximum number of peers to ask the same blocks in parallel.
	///
	/// This allows downlading announced blocks from multiple peers. Decrease to save
	/// traffic and risk increased latency.
	#[structopt(long = "max-parallel-downloads", value_name = "COUNT", default_value = "5")]
	pub max_parallel_downloads: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub node_key_params: NodeKeyParams,
}

arg_enum! {
	#[allow(missing_docs)]
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	pub enum NodeKeyType {
		Ed25519
	}
}

/// Parameters used to create the `NodeKeyConfig`, which determines the keypair
/// used for libp2p networking.
#[derive(Debug, StructOpt, Clone)]
pub struct NodeKeyParams {
	/// The secret key to use for libp2p networking.
	///
	/// The value is a string that is parsed according to the choice of
	/// `--node-key-type` as follows:
	///
	///   `ed25519`:
	///   The value is parsed as a hex-encoded Ed25519 32 bytes secret key,
	///   i.e. 64 hex characters.
	///
	/// The value of this option takes precedence over `--node-key-file`.
	///
	/// WARNING: Secrets provided as command-line arguments are easily exposed.
	/// Use of this option should be limited to development and testing. To use
	/// an externally managed secret key, use `--node-key-file` instead.
	#[structopt(long = "node-key", value_name = "KEY")]
	pub node_key: Option<String>,

	/// The type of secret key to use for libp2p networking.
	///
	/// The secret key of the node is obtained as follows:
	///
	///   * If the `--node-key` option is given, the value is parsed as a secret key
	///     according to the type. See the documentation for `--node-key`.
	///
	///   * If the `--node-key-file` option is given, the secret key is read from the
	///     specified file. See the documentation for `--node-key-file`.
	///
	///   * Otherwise, the secret key is read from a file with a predetermined,
	///     type-specific name from the chain-specific network config directory
	///     inside the base directory specified by `--base-dir`. If this file does
	///     not exist, it is created with a newly generated secret key of the
	///     chosen type.
	///
	/// The node's secret key determines the corresponding public key and hence the
	/// node's peer ID in the context of libp2p.
	#[structopt(
		long = "node-key-type",
		value_name = "TYPE",
		possible_values = &NodeKeyType::variants(),
		case_insensitive = true,
		default_value = "Ed25519"
	)]
	pub node_key_type: NodeKeyType,

	/// The file from which to read the node's secret key to use for libp2p networking.
	///
	/// The contents of the file are parsed according to the choice of `--node-key-type`
	/// as follows:
	///
	///   `ed25519`:
	///   The file must contain an unencoded 32 bytes Ed25519 secret key.
	///
	/// If the file does not exist, it is created with a newly generated secret key of
	/// the chosen type.
	#[structopt(long = "node-key-file", value_name = "FILE")]
	pub node_key_file: Option<PathBuf>,
}

/// Parameters used to create the pool configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct TransactionPoolParams {
	/// Maximum number of transactions in the transaction pool.
	#[structopt(long = "pool-limit", value_name = "COUNT", default_value = "8192")]
	pub pool_limit: usize,
	/// Maximum number of kilobytes of all transactions stored in the pool.
	#[structopt(long = "pool-kbytes", value_name = "COUNT", default_value = "20480")]
	pub pool_kbytes: usize,
}

arg_enum! {
	#[allow(missing_docs)]
	#[derive(Debug, Copy, Clone, PartialEq, Eq)]
	pub enum TracingReceiver {
		Log,
		Telemetry,
		Grafana,
	}
}

impl Into<sc_tracing::TracingReceiver> for TracingReceiver {
	fn into(self) -> sc_tracing::TracingReceiver {
		match self {
			TracingReceiver::Log => sc_tracing::TracingReceiver::Log,
			TracingReceiver::Telemetry => sc_tracing::TracingReceiver::Telemetry,
			TracingReceiver::Grafana => sc_tracing::TracingReceiver::Grafana,
		}
	}
}

/// Execution strategies parameters.
#[derive(Debug, StructOpt, Clone)]
pub struct ExecutionStrategies {
	/// The means of execution used when calling into the runtime while syncing blocks.
	#[structopt(
		long = "execution-syncing",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = DEFAULT_EXECUTION_SYNCING.as_str(),
	)]
	pub execution_syncing: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while importing blocks.
	#[structopt(
		long = "execution-import-block",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = DEFAULT_EXECUTION_IMPORT_BLOCK.as_str(),
	)]
	pub execution_import_block: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while constructing blocks.
	#[structopt(
		long = "execution-block-construction",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = DEFAULT_EXECUTION_BLOCK_CONSTRUCTION.as_str(),
	)]
	pub execution_block_construction: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while using an off-chain worker.
	#[structopt(
		long = "execution-offchain-worker",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = DEFAULT_EXECUTION_OFFCHAIN_WORKER.as_str(),
	)]
	pub execution_offchain_worker: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while not syncing, importing or constructing blocks.
	#[structopt(
		long = "execution-other",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = DEFAULT_EXECUTION_OTHER.as_str(),
	)]
	pub execution_other: ExecutionStrategy,

	/// The execution strategy that should be used by all execution contexts.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		conflicts_with_all = &[
			"execution-other",
			"execution-offchain-worker",
			"execution-block-construction",
			"execution-import-block",
			"execution-syncing",
		]
	)]
	pub execution: Option<ExecutionStrategy>,
}

/// The `run` command used to run a node.
#[derive(Debug, StructOpt, Clone)]
pub struct RunCmd {
	/// Enable validator mode.
	///
	/// The node will be started with the authority role and actively
	/// participate in any consensus task that it can (e.g. depending on
	/// availability of local keys).
	#[structopt(
		long = "validator",
		conflicts_with_all = &[ "sentry" ]
	)]
	pub validator: bool,

	/// Enable sentry mode.
	///
	/// The node will be started with the authority role and participate in
	/// consensus tasks as an "observer", it will never actively participate
	/// regardless of whether it could (e.g. keys are available locally). This
	/// mode is useful as a secure proxy for validators (which would run
	/// detached from the network), since we want this node to participate in
	/// the full consensus protocols in order to have all needed consensus data
	/// available to relay to private nodes.
	#[structopt(
		long = "sentry",
		conflicts_with_all = &[ "validator", "light" ]
	)]
	pub sentry: bool,

	/// Disable GRANDPA voter when running in validator mode, otherwise disables the GRANDPA observer.
	#[structopt(long = "no-grandpa")]
	pub no_grandpa: bool,

	/// Experimental: Run in light client mode.
	#[structopt(long = "light", conflicts_with = "sentry")]
	pub light: bool,

	/// Listen to all RPC interfaces.
	///
	/// Default is local. Note: not all RPC methods are safe to be exposed publicly. Use a RPC proxy
	/// server to filter out dangerous methods. More details: https://github.com/paritytech/substrate/wiki/Public-RPC.
	/// Use `--unsafe-rpc-external` to suppress the warning if you understand the risks.
	#[structopt(long = "rpc-external")]
	pub rpc_external: bool,

	/// Listen to all RPC interfaces.
	///
	/// Same as `--rpc-external`.
	#[structopt(long = "unsafe-rpc-external")]
	pub unsafe_rpc_external: bool,

	/// Listen to all Websocket interfaces.
	///
	/// Default is local. Note: not all RPC methods are safe to be exposed publicly. Use a RPC proxy
	/// server to filter out dangerous methods. More details: https://github.com/paritytech/substrate/wiki/Public-RPC.
	/// Use `--unsafe-ws-external` to suppress the warning if you understand the risks.
	#[structopt(long = "ws-external")]
	pub ws_external: bool,

	/// Listen to all Websocket interfaces.
	///
	/// Same as `--ws-external`.
	#[structopt(long = "unsafe-ws-external")]
	pub unsafe_ws_external: bool,

	/// Listen to all Grafana data source interfaces.
	///
	/// Default is local.
	#[structopt(long = "grafana-external")]
	pub grafana_external: bool,

	/// Specify HTTP RPC server TCP port.
	#[structopt(long = "rpc-port", value_name = "PORT")]
	pub rpc_port: Option<u16>,

	/// Specify WebSockets RPC server TCP port.
	#[structopt(long = "ws-port", value_name = "PORT")]
	pub ws_port: Option<u16>,

	/// Maximum number of WS RPC server connections.
	#[structopt(long = "ws-max-connections", value_name = "COUNT")]
	pub ws_max_connections: Option<usize>,

	/// Specify browser Origins allowed to access the HTTP & WS RPC servers.
	///
	/// A comma-separated list of origins (protocol://domain or special `null`
	/// value). Value of `all` will disable origin validation. Default is to
	/// allow localhost, https://polkadot.js.org and
	/// https://substrate-ui.parity.io origins. When running in --dev mode the
	/// default is to allow all origins.
	#[structopt(long = "rpc-cors", value_name = "ORIGINS", parse(try_from_str = parse_cors))]
	pub rpc_cors: Option<Cors>,

	/// Specify Grafana data source server TCP Port.
	#[structopt(long = "grafana-port", value_name = "PORT")]
	pub grafana_port: Option<u16>,

	/// The human-readable name for this node.
	///
	/// The node name will be reported to the telemetry server, if enabled.
	#[structopt(long = "name", value_name = "NAME")]
	pub name: Option<String>,

	/// Disable connecting to the Substrate telemetry server.
	///
	/// Telemetry is on by default on global chains.
	#[structopt(long = "no-telemetry")]
	pub no_telemetry: bool,

	/// The URL of the telemetry server to connect to.
	///
	/// This flag can be passed multiple times as a mean to specify multiple
	/// telemetry endpoints. Verbosity levels range from 0-9, with 0 denoting
	/// the least verbosity. If no verbosity level is specified the default is
	/// 0.
	#[structopt(long = "telemetry-url", value_name = "URL VERBOSITY", parse(try_from_str = parse_telemetry_endpoints))]
	pub telemetry_endpoints: Vec<(String, u8)>,

	/// Should execute offchain workers on every block.
	///
	/// By default it's only enabled for nodes that are authoring new blocks.
	#[structopt(
		long = "offchain-worker",
		value_name = "ENABLED",
		possible_values = &OffchainWorkerEnabled::variants(),
		case_insensitive = true,
		default_value = "WhenValidating"
	)]
	pub offchain_worker: OffchainWorkerEnabled,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_config: NetworkConfigurationParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pool_config: TransactionPoolParams,

	/// Shortcut for `--name Alice --validator` with session keys for `Alice` added to keystore.
	#[structopt(long, conflicts_with_all = &["bob", "charlie", "dave", "eve", "ferdie", "one", "two"])]
	pub alice: bool,

	/// Shortcut for `--name Bob --validator` with session keys for `Bob` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "charlie", "dave", "eve", "ferdie", "one", "two"])]
	pub bob: bool,

	/// Shortcut for `--name Charlie --validator` with session keys for `Charlie` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "dave", "eve", "ferdie", "one", "two"])]
	pub charlie: bool,

	/// Shortcut for `--name Dave --validator` with session keys for `Dave` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "eve", "ferdie", "one", "two"])]
	pub dave: bool,

	/// Shortcut for `--name Eve --validator` with session keys for `Eve` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "ferdie", "one", "two"])]
	pub eve: bool,

	/// Shortcut for `--name Ferdie --validator` with session keys for `Ferdie` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "one", "two"])]
	pub ferdie: bool,

	/// Shortcut for `--name One --validator` with session keys for `One` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "ferdie", "two"])]
	pub one: bool,

	/// Shortcut for `--name Two --validator` with session keys for `Two` added to keystore.
	#[structopt(long, conflicts_with_all = &["alice", "bob", "charlie", "dave", "eve", "ferdie", "one"])]
	pub two: bool,

	/// Enable authoring even when offline.
	#[structopt(long = "force-authoring")]
	pub force_authoring: bool,

	/// Comma separated list of targets for tracing
	#[structopt(long = "tracing-targets", value_name = "TARGETS")]
	pub tracing_targets: Option<String>,

	/// Receiver to process tracing messages
	#[structopt(
		long = "tracing-receiver",
		value_name = "RECEIVER",
		possible_values = &TracingReceiver::variants(),
		case_insensitive = true,
		default_value = "Log"
	)]
	pub tracing_receiver: TracingReceiver,

	/// Specify custom keystore path.
	#[structopt(long = "keystore-path", value_name = "PATH", parse(from_os_str))]
	pub keystore_path: Option<PathBuf>,

	/// Use interactive shell for entering the password used by the keystore.
	#[structopt(
		long = "password-interactive",
		conflicts_with_all = &[ "password", "password-filename" ]
	)]
	pub password_interactive: bool,

	/// Password used by the keystore.
	#[structopt(
		long = "password",
		conflicts_with_all = &[ "password-interactive", "password-filename" ]
	)]
	pub password: Option<String>,

	/// File that contains the password used by the keystore.
	#[structopt(
		long = "password-filename",
		value_name = "PATH",
		parse(from_os_str),
		conflicts_with_all = &[ "password-interactive", "password" ]
	)]
	pub password_filename: Option<PathBuf>
}

impl RunCmd {
	/// Get the `Sr25519Keyring` matching one of the flag
	pub fn get_keyring(&self) -> Option<sp_keyring::Sr25519Keyring> {
		use sp_keyring::Sr25519Keyring::*;

		if self.alice { Some(Alice) }
		else if self.bob { Some(Bob) }
		else if self.charlie { Some(Charlie) }
		else if self.dave { Some(Dave) }
		else if self.eve { Some(Eve) }
		else if self.ferdie { Some(Ferdie) }
		else if self.one { Some(One) }
		else if self.two { Some(Two) }
		else { None }
	}
}

/// Default to verbosity level 0, if none is provided.
fn parse_telemetry_endpoints(s: &str) -> Result<(String, u8), Box<dyn std::error::Error>> {
	let pos = s.find(' ');
	match pos {
		None => {
			Ok((s.to_owned(), 0))
		},
		Some(pos_) => {
			let verbosity = s[pos_ + 1..].parse()?;
			let url = s[..pos_].parse()?;
			Ok((url, verbosity))
		}
	}
}

/// CORS setting
///
/// The type is introduced to overcome `Option<Option<T>>`
/// handling of `structopt`.
#[derive(Clone, Debug)]
pub enum Cors {
	/// All hosts allowed
	All,
	/// Only hosts on the list are allowed.
	List(Vec<String>),
}

impl From<Cors> for Option<Vec<String>> {
	fn from(cors: Cors) -> Self {
		match cors {
			Cors::All => None,
			Cors::List(list) => Some(list),
		}
	}
}

/// Parse cors origins
fn parse_cors(s: &str) -> Result<Cors, Box<dyn std::error::Error>> {
	let mut is_all = false;
	let mut origins = Vec::new();
	for part in s.split(',') {
		match part {
			"all" | "*" => {
				is_all = true;
				break;
			},
			other => origins.push(other.to_owned()),
		}
	}

	Ok(if is_all { Cors::All } else { Cors::List(origins) })
}

/// The `build-spec` command used to build a specification.
#[derive(Debug, StructOpt, Clone)]
pub struct BuildSpecCmd {
	/// Force raw genesis storage output.
	#[structopt(long = "raw")]
	pub raw: bool,

	/// Disable adding the default bootnode to the specification.
	///
	/// By default the `/ip4/127.0.0.1/tcp/30333/p2p/NODE_PEER_ID` bootnode is added to the
	/// specification when no bootnode exists.
	#[structopt(long = "disable-default-bootnode")]
	pub disable_default_bootnode: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub node_key_params: NodeKeyParams,
}

/// Wrapper type of `String` which holds an arbitary sized unsigned integer formatted as decimal.
#[derive(Debug, Clone)]
pub struct BlockNumber(String);

impl FromStr for BlockNumber {
	type Err = String;

	fn from_str(block_number: &str) -> Result<Self, Self::Err> {
		if block_number.chars().any(|d| !d.is_digit(10)) {
			Err(format!(
				"Invalid block number: {}, expected decimal formatted unsigned integer",
				block_number
			))
		} else {
			Ok(Self(block_number.to_owned()))
		}
	}
}

impl BlockNumber {
	/// Wrapper on top of `std::str::parse<N>` but with `Error` as a `String`
	///
	/// See `https://doc.rust-lang.org/std/primitive.str.html#method.parse` for more elaborate
	/// documentation.
	pub fn parse<N>(&self) -> Result<N, String>
	where
		N: FromStr,
		N::Err: std::fmt::Debug,
	{
		self.0
			.parse()
			.map_err(|e| format!("BlockNumber: {} parsing failed because of {:?}", self.0, e))
	}
}

/// The `export-blocks` command used to export blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct ExportBlocksCmd {
	/// Output file name or stdout if unspecified.
	#[structopt(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify starting block number.
	///
	/// Default is 1.
	#[structopt(long = "from", value_name = "BLOCK")]
	pub from: Option<BlockNumber>,

	/// Specify last block number.
	///
	/// Default is best block.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<BlockNumber>,

	/// Use JSON output rather than binary.
	#[structopt(long = "json")]
	pub json: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// The `import-blocks` command used to import blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct ImportBlocksCmd {
	/// Input file or stdin if unspecified.
	#[structopt(parse(from_os_str))]
	pub input: Option<PathBuf>,

	/// The default number of 64KB pages to ever allocate for Wasm execution.
	///
	/// Don't alter this unless you know what you're doing.
	#[structopt(long = "default-heap-pages", value_name = "COUNT")]
	pub default_heap_pages: Option<u32>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

/// The `check-block` command used to validate blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct CheckBlockCmd {
	/// Block hash or number
	#[structopt(value_name = "HASH or NUMBER")]
	pub input: String,

	/// The default number of 64KB pages to ever allocate for Wasm execution.
	///
	/// Don't alter this unless you know what you're doing.
	#[structopt(long = "default-heap-pages", value_name = "COUNT")]
	pub default_heap_pages: Option<u32>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

/// The `revert` command used revert the chain to a previous state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: BlockNumber,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// The `purge-chain` command used to remove the whole chain.
#[derive(Debug, StructOpt, Clone)]
pub struct PurgeChainCmd {
	/// Skip interactive prompt by answering yes automatically.
	#[structopt(short = "y")]
	pub yes: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// The `benchmark` command used to benchmark FRAME pallets.
#[derive(Debug, StructOpt, Clone)]
pub struct BenchmarkCmd {
	/// Select a FRAME pallet to benchmark.
	#[structopt(short, long)]
	pub pallet: String,

	/// Select an extrinsic to benchmark.
	#[structopt(short, long)]
	pub extrinsic: String,

	/// Select how many steps of the parameters should we test.
	#[structopt(short, long, default_value = "1")]
	pub steps: u32,

	/// Select how many repetitions of this benchmark should run.
	#[structopt(short, long, default_value = "1")]
	pub repeat: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	/// The execution strategy that should be used for benchmarks
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
	)]
	pub execution: Option<ExecutionStrategy>,

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::enabled_variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,
}

/// All core commands that are provided by default.
///
/// The core commands are split into multiple subcommands and `Run` is the default subcommand. From
/// the CLI user perspective, it is not visible that `Run` is a subcommand. So, all parameters of
/// `Run` are exported as main executable parameters.
#[derive(Debug, Clone, StructOpt)]
pub enum Subcommand {
	/// Build a spec.json file, outputing to stdout.
	BuildSpec(BuildSpecCmd),

	/// Export blocks to a file.
	ExportBlocks(ExportBlocksCmd),

	/// Import blocks from file.
	ImportBlocks(ImportBlocksCmd),

	/// Validte a single block.
	CheckBlock(CheckBlockCmd),

	/// Revert chain to the previous state.
	Revert(RevertCmd),

	/// Remove the whole chain data.
	PurgeChain(PurgeChainCmd),

	/// Run runtime benchmarks.
	Benchmark(BenchmarkCmd),
}

impl Subcommand {
	/// Get the shared parameters of a `CoreParams` command
	pub fn get_shared_params(&self) -> &SharedParams {
		use Subcommand::*;

		match self {
			BuildSpec(params) => &params.shared_params,
			ExportBlocks(params) => &params.shared_params,
			ImportBlocks(params) => &params.shared_params,
			CheckBlock(params) => &params.shared_params,
			Revert(params) => &params.shared_params,
			PurgeChain(params) => &params.shared_params,
			Benchmark(params) => &params.shared_params,
		}
	}

	/// Run any `CoreParams` command
	pub fn run<G, E, B, BC, BB>(
		self,
		config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		match self {
			Subcommand::BuildSpec(cmd) => cmd.run(config),
			Subcommand::ExportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::ImportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::CheckBlock(cmd) => cmd.run(config, builder),
			Subcommand::PurgeChain(cmd) => cmd.run(config),
			Subcommand::Benchmark(cmd) => cmd.run(config, builder),
			Subcommand::Revert(cmd) => cmd.run(config, builder),
		}
	}
}

impl RunCmd {
	/// Run the command that runs the node
	pub fn run<G, E, FNL, FNF, SL, SF>(
		self,
		mut config: Configuration<G, E>,
		new_light: FNL,
		new_full: FNF,
		version: &VersionInfo,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		FNL: FnOnce(Configuration<G, E>) -> Result<SL, sc_service::error::Error>,
		FNF: FnOnce(Configuration<G, E>) -> Result<SF, sc_service::error::Error>,
		SL: AbstractService + Unpin,
		SF: AbstractService + Unpin,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		crate::update_config_for_running_node(
			&mut config,
			self,
		)?;

		crate::run_node(config, new_light, new_full, &version)
	}
}

impl BuildSpecCmd {
	/// Run the build-spec command
	pub fn run<G, E>(
		self,
		config: Configuration<G, E>,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		info!("Building chain spec");
		let mut spec = config.expect_chain_spec().clone();
		let raw_output = self.raw;

		if spec.boot_nodes().is_empty() && !self.disable_default_bootnode {
			let node_key = node_key_config(
				self.node_key_params.clone(),
				&Some(config
					.in_chain_config_dir(crate::DEFAULT_NETWORK_CONFIG_PATH)
					.expect("We provided a base_path")),
			)?;
			let keys = node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = build_multiaddr![
				Ip4([127, 0, 0, 1]),
				Tcp(30333u16),
				P2p(peer_id)
			];
			spec.add_boot_node(addr)
		}

		let json = sc_service::chain_ops::build_spec(spec, raw_output)?;

		print!("{}", json);

		Ok(())
	}
}

impl ExportBlocksCmd {
	/// Run the export-blocks command
	pub fn run<G, E, B, BC, BB>(
		self,
		mut config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		crate::fill_config_keystore_in_memory(&mut config)?;

		if let DatabaseConfig::Path { ref path, .. } = &config.database {
			info!("DB path: {}", path.display());
		}
		let from = self.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1);
		let to = self.to.as_ref().and_then(|t| t.parse().ok());

		let json = self.json;

		let file: Box<dyn io::Write> = match &self.output {
			Some(filename) => Box::new(fs::File::create(filename)?),
			None => Box::new(io::stdout()),
		};

		run_until_exit(config, |config| {
			Ok(builder(config)?.export_blocks(file, from.into(), to, json))
		})
	}
}

/// Internal trait used to cast to a dynamic type that implements Read and Seek.
trait ReadPlusSeek: Read + Seek {}

impl<T: Read + Seek> ReadPlusSeek for T {}

impl ImportBlocksCmd {
	/// Run the import-blocks command
	pub fn run<G, E, B, BC, BB>(
		self,
		mut config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		crate::fill_import_params(
			&mut config,
			&self.import_params,
			sc_service::Roles::FULL,
			self.shared_params.dev,
		)?;

		let file: Box<dyn ReadPlusSeek + Send> = match &self.input {
			Some(filename) => Box::new(fs::File::open(filename)?),
			None => {
				let mut buffer = Vec::new();
				io::stdin().read_to_end(&mut buffer)?;
				Box::new(io::Cursor::new(buffer))
			},
		};

		run_until_exit(config, |config| {
			Ok(builder(config)?.import_blocks(file, false))
		})
	}
}

impl CheckBlockCmd {
	/// Run the check-block command
	pub fn run<G, E, B, BC, BB>(
		self,
		mut config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		crate::fill_import_params(
			&mut config,
			&self.import_params,
			sc_service::Roles::FULL,
			self.shared_params.dev,
		)?;
		crate::fill_config_keystore_in_memory(&mut config)?;

		let input = if self.input.starts_with("0x") { &self.input[2..] } else { &self.input[..] };
		let block_id = match FromStr::from_str(input) {
			Ok(hash) => BlockId::hash(hash),
			Err(_) => match self.input.parse::<u32>() {
				Ok(n) => BlockId::number((n as u32).into()),
				Err(_) => return Err(error::Error::Input("Invalid hash or number specified".into())),
			}
		};

		let start = std::time::Instant::now();
		run_until_exit(config, |config| {
			Ok(builder(config)?.check_block(block_id))
		})?;
		println!("Completed in {} ms.", start.elapsed().as_millis());

		Ok(())
	}
}

impl PurgeChainCmd {
	/// Run the purge command
	pub fn run<G, E>(
		self,
		mut config: Configuration<G, E>,
	) -> error::Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		crate::fill_config_keystore_in_memory(&mut config)?;

		let db_path = match config.database {
			DatabaseConfig::Path { path, .. } => path,
			_ => {
				eprintln!("Cannot purge custom database implementation");
				return Ok(());
			}
		};

		if !self.yes {
			print!("Are you sure to remove {:?}? [y/N]: ", &db_path);
			io::stdout().flush().expect("failed to flush stdout");

			let mut input = String::new();
			io::stdin().read_line(&mut input)?;
			let input = input.trim();

			match input.chars().nth(0) {
				Some('y') | Some('Y') => {},
				_ => {
					println!("Aborted");
					return Ok(());
				},
			}
		}

		match fs::remove_dir_all(&db_path) {
			Ok(_) => {
				println!("{:?} removed.", &db_path);
				Ok(())
			},
			Err(ref err) if err.kind() == io::ErrorKind::NotFound => {
				eprintln!("{:?} did not exist.", &db_path);
				Ok(())
			},
			Err(err) => Result::Err(err.into())
		}
	}
}

impl RevertCmd {
	/// Run the revert command
	pub fn run<G, E, B, BC, BB>(
		self,
		mut config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		crate::fill_config_keystore_in_memory(&mut config)?;

		let blocks = self.num.parse()?;
		builder(config)?.revert_chain(blocks)?;

		Ok(())
	}
}

impl BenchmarkCmd {
	/// Runs the command and benchmarks the chain.
	pub fn run<G, E, B, BC, BB>(
		self,
		config: Configuration<G, E>,
		_builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		let spec = config.chain_spec.expect("chain_spec is always Some");
		let execution_strategy = self.execution.unwrap_or(ExecutionStrategy::Native).into();
		let wasm_method = self.wasm_method.into();
		let pallet = self.pallet;
		let extrinsic = self.extrinsic;
		let steps = self.steps;
		let repeat = self.repeat;
		sc_service::chain_ops::benchmark_runtime::<BB, BC::NativeDispatch, _, _>(spec, execution_strategy, wasm_method, pallet, extrinsic, steps, repeat)?;
		Ok(())
	}
}

