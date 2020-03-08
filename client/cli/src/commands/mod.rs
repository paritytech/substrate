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

mod runcmd;
mod export_blocks_cmd;
mod build_spec_cmd;
mod import_blocks_cmd;
mod check_block_cmd;
mod revert_cmd;
mod purge_chain_cmd;

use std::fmt::Debug;
use structopt::StructOpt;

use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand, ChainSpec,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::VersionInfo;
use crate::params::SharedParams;

pub use crate::commands::runcmd::RunCmd;
pub use crate::commands::export_blocks_cmd::ExportBlocksCmd;
pub use crate::commands::build_spec_cmd::BuildSpecCmd;
pub use crate::commands::import_blocks_cmd::ImportBlocksCmd;
pub use crate::commands::check_block_cmd::CheckBlockCmd;
pub use crate::commands::revert_cmd::RevertCmd;
pub use crate::commands::purge_chain_cmd::PurgeChainCmd;

/// default sub directory to store network config
const DEFAULT_NETWORK_CONFIG_PATH : &'static str = "network";

/// All core commands that are provided by default.
///
/// The core commands are split into multiple subcommands and `Run` is the default subcommand. From
/// the CLI user perspective, it is not visible that `Run` is a subcommand. So, all parameters of
/// `Run` are exported as main executable parameters.
#[derive(Debug, Clone, StructOpt)]
pub enum Subcommand {
	/// Build a spec.json file, outputing to stdout.
	BuildSpec(build_spec_cmd::BuildSpecCmd),

	/// Export blocks to a file.
	ExportBlocks(export_blocks_cmd::ExportBlocksCmd),

	/// Import blocks from file.
	ImportBlocks(import_blocks_cmd::ImportBlocksCmd),

	/// Validate a single block.
	CheckBlock(check_block_cmd::CheckBlockCmd),

	/// Revert chain to the previous state.
	Revert(revert_cmd::RevertCmd),

	/// Remove the whole chain data.
	PurgeChain(purge_chain_cmd::PurgeChainCmd),
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
		match self {
			Subcommand::BuildSpec(cmd) => cmd.run(config),
			Subcommand::ExportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::ImportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::CheckBlock(cmd) => cmd.run(config, builder),
			Subcommand::PurgeChain(cmd) => cmd.run(config),
			Subcommand::Revert(cmd) => cmd.run(config, builder),
		}
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<G, E, F>(
		&self,
		mut config: &mut Configuration<G, E>,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		F: FnOnce(&str) -> Result<Option<ChainSpec<G, E>>, String>,
	{
		match self {
			Subcommand::BuildSpec(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::ExportBlocks(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::ImportBlocks(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::CheckBlock(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::PurgeChain(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Revert(cmd) => cmd.update_config(&mut config, spec_factory, version),
		}
	}

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	pub fn init(&self, version: &VersionInfo) -> error::Result<()> {
		self.get_shared_params().init(version)
	}
}
