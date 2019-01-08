// Copyright 2018 Parity Technologies (UK) Ltd.
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

use GetCoreParams;

use std::path::PathBuf;
use structopt::{StructOpt, clap::{arg_enum, _clap_count_exprs}};
use client;

arg_enum! {
	/// How to execute blocks
	#[derive(Debug, Clone)]
	pub enum ExecutionStrategy {
		Native,
		Wasm,
		Both,
	}
}

impl Into<client::ExecutionStrategy> for ExecutionStrategy {
	fn into(self) -> client::ExecutionStrategy {
		match self {
			ExecutionStrategy::Native => client::ExecutionStrategy::NativeWhenPossible,
			ExecutionStrategy::Wasm => client::ExecutionStrategy::AlwaysWasm,
			ExecutionStrategy::Both => client::ExecutionStrategy::Both,
		}
	}
}

/// CLI Parameters provided by default
#[derive(Debug, StructOpt, Clone)]
#[structopt(name = "Substrate")]
pub struct CoreParams {
	///Sets a custom logging filter
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	pub log: Option<String>,

	#[allow(missing_docs)]
	#[structopt(subcommand)]
	pub cmds: CoreCommands,
}

impl GetCoreParams for CoreParams {
	fn core_params(&self) -> CoreParams {
		self.clone()
	}
}

/// Shared parameters used by all `CoreParams`.
#[derive(Debug, StructOpt, Clone)]
pub struct SharedParams {
	/// Specify the chain specification (one of dev, local or staging)
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	pub chain: Option<String>,

	/// Specify the development chain
	#[structopt(long = "dev")]
	pub dev: bool,

	/// Specify custom base path.
	#[structopt(long = "base-path", short = "d", value_name = "PATH", parse(from_os_str))]
	pub base_path: Option<PathBuf>,
}

/// Parameters used to create the network configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct NetworkConfigurationParams {
	/// Specify a list of bootnodes
	#[structopt(long = "bootnodes", value_name = "URL")]
	pub bootnodes: Vec<String>,

	/// Specify a list of reserved node addresses
	#[structopt(long = "reserved-nodes", value_name = "URL")]
	pub reserved_nodes: Vec<String>,

	/// Listen on this multiaddress
	#[structopt(long = "listen-addr", value_name = "LISTEN_ADDR")]
	pub listen_addr: Vec<String>,

	/// Specify p2p protocol TCP port. Only used if --listen-addr is not specified.
	#[structopt(long = "port", value_name = "PORT")]
	pub port: Option<u16>,

	/// Specify node secret key (64-character hex string)
	#[structopt(long = "node-key", value_name = "KEY")]
	pub node_key: Option<String>,

	/// Specify the number of outgoing connections we're trying to maintain
	#[structopt(long = "out-peers", value_name = "OUT_PEERS", default_value = "25")]
	pub out_peers: u32,

	/// Specify the maximum number of incoming connections we're accepting
	#[structopt(long = "in-peers", value_name = "IN_PEERS", default_value = "25")]
	pub in_peers: u32,
}

/// The `run` command used to run a node.
#[derive(Debug, StructOpt, Clone)]
pub struct RunCmd {
	/// Specify custom keystore path
	#[structopt(long = "keystore-path", value_name = "PATH", parse(from_os_str))]
	pub keystore_path: Option<PathBuf>,

	/// Specify additional key seed
	#[structopt(long = "key", value_name = "STRING")]
	pub key: Option<String>,

	/// Enable validator mode
	#[structopt(long = "validator")]
	pub validator: bool,

	/// Run in light client mode
	#[structopt(long = "light")]
	pub light: bool,

	/// Limit the memory the database cache can use
	#[structopt(long = "db-cache", value_name = "MiB")]
	pub database_cache_size: Option<u32>,

	/// Listen to all RPC interfaces (default is local)
	#[structopt(long = "rpc-external")]
	pub rpc_external: bool,

	/// Listen to all Websocket interfaces (default is local)
	#[structopt(long = "ws-external")]
	pub ws_external: bool,

	/// Specify HTTP RPC server TCP port
	#[structopt(long = "rpc-port", value_name = "PORT")]
	pub rpc_port: Option<u16>,

	/// Specify WebSockets RPC server TCP port
	#[structopt(long = "ws-port", value_name = "PORT")]
	pub ws_port: Option<u16>,

	/// Specify the pruning mode, a number of blocks to keep or 'archive'. Default is 256.
	#[structopt(long = "pruning", value_name = "PRUNING_MODE")]
	pub pruning: Option<String>,

	/// The human-readable name for this node, as reported to the telemetry server, if enabled
	#[structopt(long = "name", value_name = "NAME")]
	pub name: Option<String>,

	/// Should connect to the Substrate telemetry server (telemetry is off by default on local chains)
	#[structopt(short = "t", long = "telemetry")]
	pub telemetry: bool,

	/// Should not connect to the Substrate telemetry server (telemetry is on by default on global chains)
	#[structopt(long = "no-telemetry")]
	pub no_telemetry: bool,

	/// The URL of the telemetry server. Implies --telemetry
	#[structopt(long = "telemetry-url", value_name = "TELEMETRY_URL")]
	pub telemetry_url: Option<String>,

	/// The means of execution used when calling into the runtime. Can be either wasm, native or both.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		raw(
			possible_values = "&ExecutionStrategy::variants()",
			case_insensitive = "true",
			default_value = r#""Both""#
		)
	)]
	pub execution: ExecutionStrategy,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_config: NetworkConfigurationParams,
}

/// The `build-spec` command used to build a specification.
#[derive(Debug, StructOpt, Clone)]
pub struct BuildSpecCmd {
	/// Force raw genesis storage output.
	#[structopt(long = "raw")]
	pub raw: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	/// Specify node secret key (64-character hex string)
	#[structopt(long = "node-key", value_name = "KEY")]
	pub node_key: Option<String>,
}

/// The `export-blocks` command used to export blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct ExportBlocksCmd {
	/// Output file name or stdout if unspecified.
	#[structopt(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify starting block number. 1 by default.
	#[structopt(long = "from", value_name = "BLOCK")]
	pub from: Option<u64>,

	/// Specify last block number. Best block by default.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<u64>,

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

	/// The means of execution used when executing blocks. Can be either wasm, native or both.
	#[structopt(
		long = "execution",
		value_name = "STRATEGY",
		raw(
			possible_values = "&ExecutionStrategy::variants()",
			case_insensitive = "true",
			default_value = r#""Both""#
		)
	)]
	pub execution: ExecutionStrategy,

	/// The means of execution used when calling into the runtime. Can be either wasm, native or both.
	#[structopt(
		long = "api-execution",
		value_name = "STRATEGY",
		raw(
			possible_values = "&ExecutionStrategy::variants()",
			case_insensitive = "true",
			default_value = r#""Both""#
		)
	)]
	pub api_execution: ExecutionStrategy,

	/// The maximum number of 64KB pages to ever allocate for Wasm execution. Don't alter this unless you know what you're doing.
	#[structopt(long = "max-heap-pages", value_name = "COUNT")]
	pub max_heap_pages: Option<u32>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// The `revert` command used revert the chain to a previos state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert. Default is 256.
	pub num: Option<u64>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// The `purge-chain` command used to remove the whole chain.
#[derive(Debug, StructOpt, Clone)]
pub struct PurgeChainCmd {
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

/// Subcommands provided by Default
#[derive(Debug, StructOpt, Clone)]
pub enum CoreCommands {
	/// Run a node.
	#[structopt(name = "run")]
	Run(RunCmd),

	/// Build a spec.json file, outputing to stdout
	#[structopt(name = "build-spec")]
	BuildSpec(BuildSpecCmd),

	/// Export blocks to a file
	#[structopt(name = "export-blocks")]
	ExportBlocks(ExportBlocksCmd),

	/// Import blocks from file.
	#[structopt(name = "import-blocks")]
	ImportBlocks(ImportBlocksCmd),

	///Revert chain to the previous state
	#[structopt(name = "revert")]
	Revert(RevertCmd),

	/// Remove the whole chain data.
	#[structopt(name = "purge-chain")]
	PurgeChain(PurgeChainCmd),
}
