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
	config::{DatabaseConfig, KeystoreConfig}, ChainSpec, PruningMode,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use crate::VersionInfo;
use crate::error;
use std::fmt::Debug;
use log::info;
use sc_network::{
	config::{build_multiaddr, NonReservedPeerMode, TransportConfig, NodeKeyConfig},
	multiaddr::Protocol,
};
use std::io;
use std::fs;
use std::iter;
use std::io::{Read, Write, Seek};
use std::net::{SocketAddr, Ipv4Addr};
use regex::Regex;
use sp_runtime::generic::BlockId;
use sc_telemetry::TelemetryEndpoints;
use names::{Generator, Name};
use crate::runtime::run_until_exit;
use crate::execution_strategy::*;

pub use crate::execution_strategy::ExecutionStrategy;

pub use crate::commands::import_params::ImportParams;
pub use crate::commands::transaction_pool_params::TransactionPoolParams;
pub use crate::commands::shared_params::SharedParams;
pub use crate::commands::node_key_params::NodeKeyParams;
pub use crate::commands::network_configuration_params::NetworkConfigurationParams;
pub use crate::commands::runcmd::RunCmd;
pub use crate::commands::export_blocks_cmd::ExportBlocksCmd;
pub use crate::commands::build_spec_cmd::BuildSpecCmd;
pub use crate::commands::import_blocks_cmd::ImportBlocksCmd;
pub use crate::commands::check_block_cmd::CheckBlockCmd;
pub use crate::commands::revert_cmd::RevertCmd;
pub use crate::commands::purge_chain_cmd::PurgeChainCmd;

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
			Subcommand::Revert(cmd) => cmd.run(config, builder),
		}
	}
}
