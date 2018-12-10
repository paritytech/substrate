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

use std::path::PathBuf;
use structopt::StructOpt;

/// CLI Parameters provided by default
#[derive(Debug, StructOpt)]
#[structopt(name = "Substrate")]
pub struct CoreParams {
	///Sets a custom logging filter
	#[structopt(short = "l", long = "log", value_name = "LOG_PATTERN")]
	log: Option<String>,

	/// Specify custom keystore path
	#[structopt(long = "keystore-path", value_name = "PATH", parse(from_os_str))]
	keystore_path: Option<PathBuf>,

	/// Specify additional key seed
	#[structopt(long = "key", value_name = "STRING")]
	key: Option<String>,

	/// Specify node secret key (64-character hex string)
	#[structopt(long = "node-key", value_name = "KEY")]
	node_key: Option<String>,

	/// Enable validator mode
	#[structopt(long = "validator")]
	validator: bool,

	/// Run in light client mode
	#[structopt(long = "light")]
	light: bool,

	/// Listen on this multiaddress
	#[structopt(long = "listen-addr", value_name = "LISTEN_ADDR")]
	listen_addr: Vec<String>,

	/// Specify p2p protocol TCP port. Only used if --listen-addr is not specified.
	#[structopt(long = "port", value_name = "PORT")]
	port: Option<u32>,

	/// Listen to all RPC interfaces (default is local)
	#[structopt(long = "rpc-external")]
	rpc_external: bool,

	/// Listen to all Websocket interfaces (default is local)
	#[structopt(long = "ws-external")]
	ws_external: bool,

	/// Specify HTTP RPC server TCP port
	#[structopt(long = "rpc-port", value_name = "PORT")]
	rpc_port: Option<u32>,

	/// Specify WebSockets RPC server TCP port
	#[structopt(long = "ws-port", value_name = "PORT")]
	ws_port: Option<u32>,

	/// Specify a list of bootnodes
	#[structopt(long = "bootnodes", value_name = "URL")]
	bootnodes: Vec<String>,

	/// Specify a list of reserved node addresses
	#[structopt(long = "reserved-nodes", value_name = "URL")]
	reserved_nodes: Vec<String>,

	/// Specify the number of outgoing connections we're trying to maintain
	#[structopt(long = "out-peers", value_name = "OUT_PEERS")]
	out_peers: Option<u8>,

	/// Specify the maximum number of incoming connections we're accepting
	#[structopt(long = "in-peers", value_name = "IN_PEERS")]
	in_peers: Option<u8>,

	/// Specify the pruning mode, a number of blocks to keep or 'archive'. Default is 256.
	#[structopt(long = "pruning", value_name = "PRUNING_MODE")]
	pruning: Option<u32>,

	/// The human-readable name for this node, as reported to the telemetry server, if enabled
	#[structopt(long = "name", value_name = "NAME")]
	name: Option<String>,

	/// Should connect to the Substrate telemetry server (telemetry is off by default on local chains)
	#[structopt(short = "t", long = "telemetry")]
	telemetry: bool,

	/// Should not connect to the Substrate telemetry server (telemetry is on by default on global chains)
	#[structopt(long = "no-telemetry")]
	no_telemetry: bool,

	/// The URL of the telemetry server. Implies --telemetry
	#[structopt(long = "telemetry-url", value_name = "TELEMETRY_URL")]
	telemetry_url: Option<String>,

	/// The means of execution used when calling into the runtime. Can be either wasm, native or both.
	#[structopt(long = "execution", value_name = "STRATEGY")]
	execution: Option<ExecutionStrategy>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	shared_flags: SharedFlags,

	#[structopt(subcommand)]
	cmds: Option<CoreCommands>,
}

/// How to execute blocks
#[derive(Debug, StructOpt)]
pub enum ExecutionStrategy {
	/// Execute native only
	Native,
	/// Execute wasm only
	Wasm,
	/// Execute natively when possible, wasm otherwise
	Both,
}

impl Default for ExecutionStrategy {
	fn default() -> Self {
		ExecutionStrategy::Both
	}
}

impl std::str::FromStr for ExecutionStrategy {
	type Err = String;
	fn from_str(input: &str) -> Result<Self, Self::Err> {
		match input {
			"native" => Ok(ExecutionStrategy::Native),
			"wasm" | "webassembly" => Ok(ExecutionStrategy::Wasm),
			"both" => Ok(ExecutionStrategy::Both),
			_ => Err("Please specify either 'native', 'wasm' or 'both".to_owned())

		}
	}
}

/// Flags used by `CoreParams` and almost all `CoreCommands`.
#[derive(Debug, StructOpt)]
pub struct SharedFlags {
	/// Specify the chain specification (one of dev, local or staging)
	#[structopt(long = "chain", value_name = "CHAIN_SPEC")]
	chain: Option<String>,

	/// Specify the development chain
	#[structopt(long = "dev")]
	dev: bool,

	/// Specify custom base path.
	#[structopt(long = "base-path", short = "d", value_name = "PATH")]
	base_path: Option<String>,
}

/// Subcommands provided by Default
#[derive(Debug, StructOpt)]
pub enum CoreCommands {
	/// Build a spec.json file, outputing to stdout
	#[structopt(name = "build-spec")]
	BuildSpec {
		/// Force raw genesis storage output.
		#[structopt(long = "raw")]
		raw: bool,
	},

	/// Export blocks to a file
	#[structopt(name = "export-blocks")]
	ExportBlocks {
		/// Output file name or stdout if unspecified.
		#[structopt(parse(from_os_str))]
		output: Option<PathBuf>,

		/// Specify starting block number. 1 by default.
		#[structopt(long = "from", value_name = "BLOCK")]
		from: Option<u128>,

		/// Specify last block number. Best block by default.
		#[structopt(long = "to", value_name = "BLOCK")]
		to: Option<u128>,

		/// Use JSON output rather than binary.
		#[structopt(long = "json")]
		json: bool,

		#[allow(missing_docs)]
		#[structopt(flatten)]
		shared_flags: SharedFlags,
	},

	/// Import blocks from file.
	#[structopt(name = "import-blocks")]
	ImportBlocks {
		/// Input file or stdin if unspecified.
		#[structopt(parse(from_os_str))]
		input: Option<PathBuf>,

		/// The means of execution used when executing blocks. Can be either wasm, native or both.
		#[structopt(long = "execution", value_name = "STRATEGY")]
		execution: ExecutionStrategy,

		/// The means of execution used when calling into the runtime. Can be either wasm, native or both.
		#[structopt(long = "api-execution", value_name = "STRATEGY")]
		api_execution: ExecutionStrategy,

		/// The maximum number of 64KB pages to ever allocate for Wasm execution. Don't alter this unless you know what you're doing.
		#[structopt(long = "max-heap-pages", value_name = "COUNT")]
		max_heap_pages: Option<u32>,

		#[allow(missing_docs)]
		#[structopt(flatten)]
		shared_flags: SharedFlags,
	},

	///Revert chain to the previous state
	#[structopt(name = "revert")]
	Revert {
		/// Number of blocks to revert. Default is 256.
		num: Option<u32>,

		#[allow(missing_docs)]
		#[structopt(flatten)]
		shared_flags: SharedFlags,
	},

	/// Remove the whole chain data.
	#[structopt(name = "purge-chain")]
	PurgeChain {
		#[allow(missing_docs)]
		#[structopt(flatten)]
		shared_flags: SharedFlags,
	},
}
