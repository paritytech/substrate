// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Command ran by the CLI

use crate::cli::{InspectCmd, InspectSubCmd};
use crate::Inspector;
use sc_cli::{CliConfiguration, ImportParams, Result, SharedParams};
use sc_service::{new_full_client, Configuration, NativeExecutionDispatch};
use sp_runtime::traits::Block;
use std::str::FromStr;

impl InspectCmd {
	/// Run the inspect command, passing the inspector.
	pub fn run<B, RA, EX>(&self, config: Configuration) -> Result<()>
	where
		B: Block,
		B::Hash: FromStr,
		RA: Send + Sync + 'static,
		EX: NativeExecutionDispatch + 'static,
	{
		let client = new_full_client::<B, RA, EX>(&config)?;
		let inspect = Inspector::<B>::new(client);

		match &self.command {
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

impl CliConfiguration for InspectCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
