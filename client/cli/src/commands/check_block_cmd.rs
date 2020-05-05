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

use crate::{
	CliConfiguration, error, params::{ImportParams, SharedParams, BlockNumberOrHash},
};
use sc_service::{Configuration, ServiceBuilderCommand};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{fmt::Debug, str::FromStr};
use structopt::StructOpt;

/// The `check-block` command used to validate blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct CheckBlockCmd {
	/// Block hash or number
	#[structopt(value_name = "HASH or NUMBER")]
	pub input: BlockNumberOrHash,

	/// The default number of 64KB pages to ever allocate for Wasm execution.
	///
	/// Don't alter this unless you know what you're doing.
	#[structopt(long = "default-heap-pages", value_name = "COUNT")]
	pub default_heap_pages: Option<u32>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub import_params: ImportParams,
}

impl CheckBlockCmd {
	/// Run the check-block command
	pub async fn run<B, BC, BB>(
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
		let start = std::time::Instant::now();
		builder(config)?.check_block(self.input.parse()?).await?;
		println!("Completed in {} ms.", start.elapsed().as_millis());

		Ok(())
	}
}

impl CliConfiguration for CheckBlockCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
