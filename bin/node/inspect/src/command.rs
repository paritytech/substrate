// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Command ran by the CLI

use crate::{
	cli::{InspectCmd, InspectSubCmd},
	Inspector,
};
use sc_cli::{CliConfiguration, ImportParams, Result, SharedParams};
use sc_service::{Configuration, NativeExecutionDispatch};
use sp_runtime::traits::Block;

impl InspectCmd {
	/// Run the inspect command, passing the inspector.
	pub fn run<B, RA, D>(&self, config: Configuration) -> Result<()>
	where
		B: Block,
		RA: Send + Sync + 'static,
		D: NativeExecutionDispatch + 'static,
	{
		let executor = sc_service::new_native_or_wasm_executor::<D>(&config);
		let client = sc_service::new_full_client::<B, RA, _>(&config, None, executor)?;
		let inspect = Inspector::<B>::new(client);

		match &self.command {
			InspectSubCmd::Block { input } => {
				let input = input.parse()?;
				let res = inspect.block(input).map_err(|e| e.to_string())?;
				println!("{res}");
				Ok(())
			},
			InspectSubCmd::Extrinsic { input } => {
				let input = input.parse()?;
				let res = inspect.extrinsic(input).map_err(|e| e.to_string())?;
				println!("{res}");
				Ok(())
			},
		}
	}
}

impl CliConfiguration for InspectCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
