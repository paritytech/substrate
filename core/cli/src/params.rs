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

use crate::traits::{AugmentClap, GetLogFilter};

use std::path::PathBuf;
use structopt::{StructOpt, clap::{arg_enum, _clap_count_exprs, App, AppSettings, SubCommand}};
use client;

/// Auxialary macro to implement `GetLogFilter` for all types that have the `shared_params` field.
macro_rules! impl_get_log_filter {
	( $type:ident ) => {
		impl $crate::GetLogFilter for $type {
			fn get_log_filter(&self) -> Option<String> {
				self.shared_params.get_log_filter()
			}
		}
	}
}

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

	///Sets a custom logging filter
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

	/// Should not connect to the Substrate telemetry server (telemetry is on by default on global chains)
	#[structopt(long = "no-telemetry")]
	pub no_telemetry: bool,

	/// The URL of the telemetry server to connect to
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

impl_augment_clap!(RunCmd);
impl_get_log_filter!(RunCmd);

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

impl_get_log_filter!(BuildSpecCmd);

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

impl_get_log_filter!(ExportBlocksCmd);

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

impl_get_log_filter!(ImportBlocksCmd);

/// The `revert` command used revert the chain to a previos state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: u64,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl_get_log_filter!(RevertCmd);

/// The `purge-chain` command used to remove the whole chain.
#[derive(Debug, StructOpt, Clone)]
pub struct PurgeChainCmd {
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
				.about("Build a spec.json file, outputing to stdout.")
		)
		.subcommand(
			ExportBlocksCmd::augment_clap(SubCommand::with_name("export-blocks"))
				.about("Export blocks to a file.")
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
#[derive(Clone, Debug)]
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
