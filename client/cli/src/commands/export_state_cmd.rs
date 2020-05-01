// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::{
	CliConfiguration, error, params::{PruningParams, SharedParams, BlockNumberOrHash},
};
use log::info;
use sc_service::{Configuration, ServiceBuilderCommand};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{fmt::Debug, str::FromStr};
use structopt::StructOpt;

/// The `export-state` command used to export the state of a given block into
/// a chain spec.
#[derive(Debug, StructOpt, Clone)]
pub struct ExportStateCmd {
	/// Block hash or number.
	#[structopt(value_name = "HASH or NUMBER")]
	pub input: Option<BlockNumberOrHash>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

impl ExportStateCmd {
	/// Run the `export-state` command
	pub fn run<B, BC, BB>(
		&self,
		config: Configuration,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration) -> Result<BC, sc_service::error::Error>,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: BlockT + Debug,
		<NumberFor<BB> as FromStr>::Err: std::fmt::Debug,
		BB::Hash: FromStr,
		<BB::Hash as FromStr>::Err: std::fmt::Debug,
	{
		info!("Exporting raw state...");
		let mut input_spec = config.chain_spec.cloned_box();
		let block_id = self.input.clone().map(|b| b.parse()).transpose()?;
		let raw_state = builder(config)?.export_raw_state(block_id)?;
		input_spec.set_storage(raw_state);

		info!("Generating new chain spec...");
		let json = sc_service::chain_ops::build_spec(&*input_spec, true)?;

		print!("{}", json);

		Ok(())
	}
}

impl CliConfiguration for ExportStateCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}
