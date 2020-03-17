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
mod generate_node_key;
mod generate;
mod inspect;
mod sign;
mod sign_transaction;
mod utils;
mod transfer;
mod verify;
mod vanity;
mod insert;
#[cfg(test)]
pub mod tests;

use std::fmt::{Debug, Display};
use std::str::FromStr;
use structopt::StructOpt;
use parity_scale_codec::Codec;
use sc_service::{Configuration, ServiceBuilderCommand, ChainSpec};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::VersionInfo;
use crate::params::SharedParams;

pub use crate::commands::utils::*;
pub use crate::commands::runcmd::RunCmd;
pub use crate::commands::export_blocks_cmd::ExportBlocksCmd;
pub use crate::commands::build_spec_cmd::BuildSpecCmd;
pub use crate::commands::import_blocks_cmd::ImportBlocksCmd;
pub use crate::commands::check_block_cmd::CheckBlockCmd;
pub use crate::commands::revert_cmd::RevertCmd;
pub use crate::commands::purge_chain_cmd::PurgeChainCmd;
pub use crate::commands::generate::GenerateCmd;
pub use crate::commands::generate_node_key::GenerateNodeKeyCmd;
pub use crate::commands::insert::InsertCmd;
pub use crate::commands::sign::SignCmd;
pub use crate::commands::sign_transaction::SignTransactionCmd;
pub use crate::commands::transfer::TransferCmd;
pub use crate::commands::vanity::VanityCmd;
pub use crate::commands::verify::VerifyCmd;


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

	/// Generate a random node libp2p key, save it to file and print its peer ID
	GenerateNodeKey(generate_node_key::GenerateNodeKeyCmd),

	/// Generate a random account
	Generate(generate::GenerateCmd),

	/// Gets a public key and a SS58 address from the provided Secret URI
	Inspect(inspect::InspectCmd),

	/// Insert a key to the keystore of a node.
	Insert(insert::InsertCmd),

	/// Sign a message, with a given (secret) key
	Sign(sign::SignCmd),

	/// Sign transaction from encoded Call. Returns a signed and encoded UncheckedMortalCompactExtrinsic as hex.
	SignTransaction(sign_transaction::SignTransactionCmd),

	/// Author and sign a Node pallet_balances::Transfer transaction with a given (secret) key.
	Transfer(transfer::TransferCmd),

	/// Verify a signature for a message, provided on STDIN, with a given (public or secret) key.
	Verify(verify::VerifyCmd),

	/// Generate a seed that provides a vanity address.
	Vanity(vanity::VanityCmd),
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
			GenerateNodeKey(params) => &params.shared_params,
			Generate(params) => &params.shared_params,
			Inspect(params) => &params.shared_params,
			Insert(params) => &params.shared_params,
			Sign(params) => &params.shared_params,
			SignTransaction(params) => &params.shared_params,
			Transfer(params) => &params.shared_params,
			Verify(params) => &params.shared_params,
			Vanity(params) => &params.shared_params,
		}
	}

	/// Run any `CoreParams` command
	pub fn run<RA, B, BC, Block>(
		self,
		config: Configuration,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration) -> Result<BC, sc_service::error::Error>,
		BC: ServiceBuilderCommand<Block =Block> + Unpin,
		Block: BlockT + Debug,
		<<Block::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		Block::Hash: std::str::FromStr,
		RA: RuntimeAdapter,
		<IndexFor<RA> as FromStr>::Err: Display,
		<BalanceFor<RA> as FromStr>::Err: Display,
		CallFor<RA>: Codec,
	{
		match self {
			Subcommand::BuildSpec(cmd) => cmd.run(config),
			Subcommand::ExportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::ImportBlocks(cmd) => cmd.run(config, builder),
			Subcommand::CheckBlock(cmd) => cmd.run(config, builder),
			Subcommand::PurgeChain(cmd) => cmd.run(config),
			Subcommand::Revert(cmd) => cmd.run(config, builder),
			Subcommand::GenerateNodeKey(cmd) => cmd.run(),
			Subcommand::Generate(cmd) => cmd.run(),
			Subcommand::Inspect(cmd) => cmd.run(),
			Subcommand::Sign(cmd) => cmd.run(),
			Subcommand::Verify(cmd) => cmd.run(),
			Subcommand::Vanity(cmd) => cmd.run(),
			Subcommand::Transfer(cmd) => cmd.run::<RA>(),
			Subcommand::SignTransaction(cmd) => cmd.run::<RA>(),
			Subcommand::Insert(cmd) => cmd.run::<RA>(),
		}
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<F>(
		&self,
		mut config: &mut Configuration,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		F: FnOnce(&str) -> Result<Box<dyn ChainSpec>, String>,
	{
		match self {
			Subcommand::BuildSpec(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::ExportBlocks(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::ImportBlocks(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::CheckBlock(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::PurgeChain(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Revert(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::GenerateNodeKey(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Generate(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Inspect(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Insert(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Sign(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::SignTransaction(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Transfer(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Verify(cmd) => cmd.update_config(&mut config, spec_factory, version),
			Subcommand::Vanity(cmd) => cmd.update_config(&mut config, spec_factory, version),
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
