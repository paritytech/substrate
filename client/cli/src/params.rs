// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use crate::traits::{AugmentClap, GetLogFilter};

use std::path::PathBuf;
use structopt::{StructOpt, clap::{arg_enum, App, AppSettings, SubCommand, Arg}};

pub use crate::execution_strategy::ExecutionStrategy;

/// Auxiliary macro to implement `GetLogFilter` for all types that have the `shared_params` field.
macro_rules! impl_get_log_filter {
	( $type:ident ) => {
		impl $crate::GetLogFilter for $type {
			fn get_log_filter(&self) -> Option<String> {
				self.shared_params.get_log_filter()
			}
		}
	}
}

impl Into<client_api::ExecutionStrategy> for ExecutionStrategy {
	fn into(self) -> client_api::ExecutionStrategy {
		match self {
			ExecutionStrategy::Native => client_api::ExecutionStrategy::NativeWhenPossible,
			ExecutionStrategy::Wasm => client_api::ExecutionStrategy::AlwaysWasm,
			ExecutionStrategy::Both => client_api::ExecutionStrategy::Both,
			ExecutionStrategy::NativeElseWasm => client_api::ExecutionStrategy::NativeElseWasm,
		}
	}
}

arg_enum! {
	/// How to execute Wasm runtime code
	#[allow(missing_docs)]
	#[derive(Debug, Clone)]
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

impl Into<service::config::WasmExecutionMethod> for WasmExecutionMethod {
	fn into(self) -> service::config::WasmExecutionMethod {
		match self {
			WasmExecutionMethod::Interpreted => service::config::WasmExecutionMethod::Interpreted,
			#[cfg(feature = "wasmtime")]
			WasmExecutionMethod::Compiled => service::config::WasmExecutionMethod::Compiled,
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

impl GetLogFilter for SharedParams {
	fn get_log_filter(&self) -> Option<String> {
		self.log.clone()
	}
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
	pub node_key_params: NodeKeyParams
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
	pub node_key_file: Option<PathBuf>
}

/// Parameters used to create the pool configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct TransactionPoolParams {
	/// Maximum number of transactions in the transaction pool.
	#[structopt(long = "pool-limit", value_name = "COUNT", default_value = "512")]
	pub pool_limit: usize,
	/// Maximum number of kilobytes of all transactions stored in the pool.
	#[structopt(long = "pool-kbytes", value_name = "COUNT", default_value = "10240")]
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

impl Into<substrate_tracing::TracingReceiver> for TracingReceiver {
	fn into(self) -> substrate_tracing::TracingReceiver {
		match self {
			TracingReceiver::Log => substrate_tracing::TracingReceiver::Log,
			TracingReceiver::Telemetry => substrate_tracing::TracingReceiver::Telemetry,
			TracingReceiver::Grafana => substrate_tracing::TracingReceiver::Grafana,
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
		default_value = "NativeElseWasm"
	)]
	pub execution_syncing: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while importing blocks.
	#[structopt(
		long = "execution-import-block",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "NativeElseWasm"
	)]
	pub execution_import_block: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while constructing blocks.
	#[structopt(
		long = "execution-block-construction",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "Wasm"
	)]
	pub execution_block_construction: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while using an off-chain worker.
	#[structopt(
		long = "execution-offchain-worker",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "Native"
	)]
	pub execution_offchain_worker: ExecutionStrategy,

	/// The means of execution used when calling into the runtime while not syncing, importing or constructing blocks.
	#[structopt(
		long = "execution-other",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "Native"
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
		conflicts_with_all = &[ "validator" ]
	)]
	pub sentry: bool,

	/// Disable GRANDPA voter when running in validator mode, otherwise disables the GRANDPA observer.
	#[structopt(long = "no-grandpa")]
	pub no_grandpa: bool,

	/// Experimental: Run in light client mode.
	#[structopt(long = "light")]
	pub light: bool,

	/// Limit the memory the database cache can use.
	#[structopt(long = "db-cache", value_name = "MiB", default_value = "1024")]
	pub database_cache_size: u32,

	/// Specify the state cache size.
	#[structopt(long = "state-cache-size", value_name = "Bytes", default_value = "67108864")]
	pub state_cache_size: usize,

	/// Listen to all RPC interfaces.
	///
	/// Default is local.
	#[structopt(long = "rpc-external")]
	pub rpc_external: bool,

	/// Listen to all Websocket interfaces.
	///
	/// Default is local.
	#[structopt(long = "ws-external")]
	pub ws_external: bool,

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

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_config: NetworkConfigurationParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pool_config: TransactionPoolParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub keyring: Keyring,

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

/// Stores all required Cli values for a keyring test account.
struct KeyringTestAccountCliValues {
	help: String,
	conflicts_with: Vec<String>,
	name: String,
	variant: keyring::Sr25519Keyring,
}

lazy_static::lazy_static! {
	/// The Cli values for all test accounts.
	static ref TEST_ACCOUNTS_CLI_VALUES: Vec<KeyringTestAccountCliValues> = {
		keyring::Sr25519Keyring::iter().map(|a| {
			let help = format!(
				"Shortcut for `--name {} --validator` with session keys for `{}` added to keystore.",
				a,
				a,
			);
			let conflicts_with = keyring::Sr25519Keyring::iter()
				.filter(|b| a != *b)
				.map(|b| b.to_string().to_lowercase())
				.chain(std::iter::once("name".to_string()))
				.collect::<Vec<_>>();
			let name = a.to_string().to_lowercase();

			KeyringTestAccountCliValues {
				help,
				conflicts_with,
				name,
				variant: a,
			}
		}).collect()
	};
}

/// Wrapper for exposing the keyring test accounts into the Cli.
#[derive(Debug, Clone)]
pub struct Keyring {
	pub account: Option<keyring::Sr25519Keyring>,
}

impl StructOpt for Keyring {
	fn clap<'a, 'b>() -> App<'a, 'b> {
		unimplemented!("Should not be called for `TestAccounts`.")
	}

	fn from_clap(m: &::structopt::clap::ArgMatches) -> Self {
		Keyring {
			account: TEST_ACCOUNTS_CLI_VALUES.iter().find(|a| m.is_present(&a.name)).map(|a| a.variant),
		}
	}
}

impl AugmentClap for Keyring {
	fn augment_clap<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b> {
		TEST_ACCOUNTS_CLI_VALUES.iter().fold(app, |app, a| {
			let conflicts_with_strs = a.conflicts_with.iter().map(|s| s.as_str()).collect::<Vec<_>>();

			app.arg(
				Arg::with_name(&a.name)
					.long(&a.name)
					.help(&a.help)
					.conflicts_with_all(&conflicts_with_strs)
					.takes_value(false)
			)
		})
	}
}

impl Keyring {
	fn is_subcommand() -> bool {
		false
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

impl_augment_clap!(RunCmd);
impl_get_log_filter!(RunCmd);

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

impl_get_log_filter!(BuildSpecCmd);

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
	pub from: Option<u32>,

	/// Specify last block number.
	///
	/// Default is best block.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<u32>,

	/// Use JSON output rather than binary.
	#[structopt(long = "json")]
	pub json: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl_get_log_filter!(ExportBlocksCmd);

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

	/// Method for executing Wasm runtime code.
	#[structopt(
		long = "wasm-execution",
		value_name = "METHOD",
		possible_values = &WasmExecutionMethod::variants(),
		case_insensitive = true,
		default_value = "Interpreted"
	)]
	pub wasm_method: WasmExecutionMethod,

	/// The means of execution used when calling into the runtime while importing blocks.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		possible_values = &ExecutionStrategy::variants(),
		case_insensitive = true,
		default_value = "NativeElseWasm"
	)]
	pub execution: ExecutionStrategy,
}

impl_get_log_filter!(ImportBlocksCmd);

/// The `revert` command used revert the chain to a previous state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: u32,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl_get_log_filter!(RevertCmd);

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

impl_get_log_filter!(PurgeChainCmd);

/// All core commands that are provided by default.
///
/// The core commands are split into multiple subcommands and `Run` is the default subcommand. From
/// the CLI user perspective, it is not visible that `Run` is a subcommand. So, all parameters of
/// `Run` are exported as main executable parameters.
#[derive(Debug, Clone)]
pub enum CoreParams<CC, RP> {
	/// Run a node.
	Run(MergeParameters<RunCmd, RP>),

	/// Build a spec.json file, outputing to stdout.
	BuildSpec(BuildSpecCmd),

	/// Export blocks to a file.
	ExportBlocks(ExportBlocksCmd),

	/// Import blocks from file.
	ImportBlocks(ImportBlocksCmd),

	/// Revert chain to the previous state.
	Revert(RevertCmd),

	/// Remove the whole chain data.
	PurgeChain(PurgeChainCmd),

	/// Further custom subcommands.
	Custom(CC),
}

impl<CC, RP> StructOpt for CoreParams<CC, RP> where
	CC: StructOpt + GetLogFilter,
	RP: StructOpt + AugmentClap
{
	fn clap<'a, 'b>() -> App<'a, 'b> {
		RP::augment_clap(
			RunCmd::augment_clap(
				CC::clap().unset_setting(AppSettings::SubcommandRequiredElseHelp)
			)
		).subcommand(
			BuildSpecCmd::augment_clap(SubCommand::with_name("build-spec"))
				.about("Build a spec.json file, outputting to stdout.")
		)
		.subcommand(
			ExportBlocksCmd::augment_clap(SubCommand::with_name("export-blocks"))
				.about("Export blocks to a file. This file can only be re-imported \
						if it is in binary format (not JSON!)."
					)
		)
		.subcommand(
			ImportBlocksCmd::augment_clap(SubCommand::with_name("import-blocks"))
				.about("Import blocks from file.")
		)
		.subcommand(
			RevertCmd::augment_clap(SubCommand::with_name("revert"))
				.about("Revert chain to the previous state.")
		)
		.subcommand(
			PurgeChainCmd::augment_clap(SubCommand::with_name("purge-chain"))
				.about("Remove the whole chain data.")
		)
	}

	fn from_clap(matches: &::structopt::clap::ArgMatches) -> Self {
		match matches.subcommand() {
			("build-spec", Some(matches)) =>
				CoreParams::BuildSpec(BuildSpecCmd::from_clap(matches)),
			("export-blocks", Some(matches)) =>
				CoreParams::ExportBlocks(ExportBlocksCmd::from_clap(matches)),
			("import-blocks", Some(matches)) =>
				CoreParams::ImportBlocks(ImportBlocksCmd::from_clap(matches)),
			("revert", Some(matches)) => CoreParams::Revert(RevertCmd::from_clap(matches)),
			("purge-chain", Some(matches)) =>
				CoreParams::PurgeChain(PurgeChainCmd::from_clap(matches)),
			(_, None) => CoreParams::Run(MergeParameters::from_clap(matches)),
			_ => CoreParams::Custom(CC::from_clap(matches)),
		}
	}
}

impl<CC, RP> GetLogFilter for CoreParams<CC, RP> where CC: GetLogFilter {
	fn get_log_filter(&self) -> Option<String> {
		match self {
			CoreParams::Run(c) => c.left.get_log_filter(),
			CoreParams::BuildSpec(c) => c.get_log_filter(),
			CoreParams::ExportBlocks(c) => c.get_log_filter(),
			CoreParams::ImportBlocks(c) => c.get_log_filter(),
			CoreParams::PurgeChain(c) => c.get_log_filter(),
			CoreParams::Revert(c) => c.get_log_filter(),
			CoreParams::Custom(c) => c.get_log_filter(),
		}
	}
}

/// A special commandline parameter that expands to nothing.
/// Should be used as custom subcommand/run arguments if no custom values are required.
#[derive(Clone, Debug, Default)]
pub struct NoCustom {}

impl StructOpt for NoCustom {
	fn clap<'a, 'b>() -> App<'a, 'b> {
		App::new("NoCustom")
	}

	fn from_clap(_: &::structopt::clap::ArgMatches) -> Self {
		NoCustom {}
	}
}

impl AugmentClap for NoCustom {
	fn augment_clap<'a, 'b>(app: App<'a, 'b>) -> App<'a, 'b> {
		app
	}
}

impl GetLogFilter for NoCustom {
	fn get_log_filter(&self) -> Option<String> {
		None
	}
}

/// Merge all CLI parameters of `L` and `R` into the same level.
#[derive(Clone, Debug)]
pub struct MergeParameters<L, R> {
	/// The left side parameters.
	pub left: L,
	/// The right side parameters.
	pub right: R,
}

impl<L, R> StructOpt for MergeParameters<L, R> where L: StructOpt + AugmentClap, R: StructOpt {
	fn clap<'a, 'b>() -> App<'a, 'b> {
		L::augment_clap(R::clap())
	}

	fn from_clap(matches: &::structopt::clap::ArgMatches) -> Self {
		MergeParameters {
			left: L::from_clap(matches),
			right: R::from_clap(matches),
		}
	}
}
