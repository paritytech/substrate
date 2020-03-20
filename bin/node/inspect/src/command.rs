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

//! Command ran by the CLI

use std::str::FromStr;

use crate::cli::{InspectCmd, InspectSubCmd};
use crate::Inspector;
use sc_cli::{substrate_cli_params, CliConfiguration, Result};
use sc_service::{
	new_full_client, ChainSpecExtension, Configuration, NativeExecutionDispatch, RuntimeGenesis,
};
use sp_runtime::traits::Block;

impl InspectCmd {
	/// Run the inspect command, passing the inspector.
	pub fn run<B, RA, EX, G, E>(self, config: Configuration<G, E>) -> Result<()>
	where
		B: Block,
		B::Hash: FromStr,
		RA: Send + Sync + 'static,
		EX: NativeExecutionDispatch + 'static,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
	{
		let client = new_full_client::<B, RA, EX, _, _>(&config)?;
		let inspect = Inspector::<B>::new(client);

		match self.command {
			InspectSubCmd::Block { input } => {
				let input = input.parse()?;
				let res = inspect.block(input).map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			}
			InspectSubCmd::Extrinsic { input } => {
				let input = input.parse()?;
				let res = inspect.extrinsic(input).map_err(|e| format!("{}", e))?;
				println!("{}", res);
				Ok(())
			}
		}
	}
}

#[substrate_cli_params(shared_params = shared_params, import_params = import_params)]
impl CliConfiguration for InspectCmd {}
