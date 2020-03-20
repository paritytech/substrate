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

mod build_spec_cmd;
mod check_block_cmd;
mod export_blocks_cmd;
mod import_blocks_cmd;
mod purge_chain_cmd;
mod revert_cmd;
mod runcmd;

pub use crate::commands::build_spec_cmd::BuildSpecCmd;
pub use crate::commands::check_block_cmd::CheckBlockCmd;
pub use crate::commands::export_blocks_cmd::ExportBlocksCmd;
pub use crate::commands::import_blocks_cmd::ImportBlocksCmd;
pub use crate::commands::purge_chain_cmd::PurgeChainCmd;
pub use crate::commands::revert_cmd::RevertCmd;
pub use crate::commands::runcmd::RunCmd;
use crate::params::SharedParams;
use crate::CliConfiguration;
use crate::Result;
use crate::SubstrateCLI;
use app_dirs::{AppDataType, AppInfo};
use core::future::Future;
use core::pin::Pin;
use sc_client_api::execution_extensions::ExecutionStrategies;
use sc_network::config::NodeKeyConfig;
use sc_service::{
	config::DatabaseConfig, config::KeystoreConfig, config::NetworkConfiguration,
	config::WasmExecutionMethod, ChainSpec, ChainSpecExtension, Configuration, PruningMode, Roles,
	RuntimeGenesis, ServiceBuilderCommand,
};
use sc_tracing::TracingReceiver;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::fmt::Debug;
use std::path::PathBuf;
use std::sync::Arc;
use structopt::StructOpt;

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

	/// Validate a single block.
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

	/// Initialize substrate. This must be done only once.
	///
	/// This method:
	///
	/// 1. Set the panic handler
	/// 2. Raise the FD limit
	/// 3. Initialize the logger
	pub fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<()>
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		self.get_shared_params().init::<C, G, E>()
	}
}

macro_rules! match_and_call {
	(fn $method:ident ( &self $(, $arg:ident : $ty:ty)* ) $(-> $result:ty)?) => {
		fn $method (&self, $($arg : $ty),*) $(-> $result)? {
			match self {
				Subcommand::BuildSpec(cmd) => cmd.$method($($arg),*),
				Subcommand::ExportBlocks(cmd) => cmd.$method($($arg),*),
				Subcommand::ImportBlocks(cmd) => cmd.$method($($arg),*),
				Subcommand::CheckBlock(cmd) => cmd.$method($($arg),*),
				Subcommand::Revert(cmd) => cmd.$method($($arg),*),
				Subcommand::PurgeChain(cmd) => cmd.$method($($arg),*),
			}
		}
	};

	(fn $method:ident <C: SubstrateCLI<G, E>, G, E> ( &self $(, $arg:ident : $ty:ty)* ) $(-> $result:ty)?
	where
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	) => {
		fn $method <C: SubstrateCLI<G, E>, G, E> (&self, $($arg : $ty),*) $(-> $result)?
		where
			G: RuntimeGenesis,
			E: ChainSpecExtension,
		{
			match self {
				Subcommand::BuildSpec(cmd) => cmd.$method::<C, G, E>($($arg),*),
				Subcommand::ExportBlocks(cmd) => cmd.$method::<C, G, E>($($arg),*),
				Subcommand::ImportBlocks(cmd) => cmd.$method::<C, G, E>($($arg),*),
				Subcommand::CheckBlock(cmd) => cmd.$method::<C, G, E>($($arg),*),
				Subcommand::Revert(cmd) => cmd.$method::<C, G, E>($($arg),*),
				Subcommand::PurgeChain(cmd) => cmd.$method::<C, G, E>($($arg),*),
			}
		}
	};
}

impl CliConfiguration for Subcommand {
	match_and_call! { fn get_base_path(&self) -> Result<Option<&PathBuf>> }

	match_and_call! { fn get_is_dev(&self) -> Result<bool> }

	match_and_call! { fn get_database_config(&self, base_path: &PathBuf, cache_size: Option<usize>) -> Result<DatabaseConfig> }

	match_and_call! {
		fn get_chain_spec<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<ChainSpec<G, E>>
		where
			G: RuntimeGenesis,
			E: ChainSpecExtension,
	}

	match_and_call! {
		fn init<C: SubstrateCLI<G, E>, G, E>(&self) -> Result<()>
		where
			G: RuntimeGenesis,
			E: ChainSpecExtension,
	}

	match_and_call! { fn get_pruning(&self, is_dev: bool, roles: Roles) -> Result<PruningMode> }

	match_and_call! { fn get_tracing_receiver(&self) -> Result<TracingReceiver> }

	match_and_call! { fn get_tracing_targets(&self) -> Result<Option<String>> }

	match_and_call! { fn get_state_cache_size(&self) -> Result<usize> }

	match_and_call! { fn get_wasm_method(&self) -> Result<WasmExecutionMethod> }

	match_and_call! { fn get_execution_strategies(&self, is_dev: bool) -> Result<ExecutionStrategies> }

	match_and_call! { fn get_database_cache_size(&self) -> Result<Option<usize>> }

	match_and_call! { fn get_node_key(&self, net_config_dir: &PathBuf) -> Result<NodeKeyConfig> }
}
