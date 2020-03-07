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

use std::fmt::Debug;
use structopt::StructOpt;
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand, ChainSpec, Roles,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::VersionInfo;
use crate::params::{BlockNumber, SharedParams, PruningParams};

/// The `revert` command used revert the chain to a previous state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: BlockNumber,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

impl RevertCmd {
	/// Run the revert command
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
		let blocks = self.num.parse()?;
		builder(config)?.revert_chain(blocks)?;

		Ok(())
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
		self.shared_params.update_config(&mut config, spec_factory, version)?;
		self.pruning_params.update_config(&mut config, Roles::FULL, true)?;
		config.use_in_memory_keystore()?;

		Ok(())
	}
}
