// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::error;
use crate::params::ImportParams;
use crate::params::SharedParams;
use crate::params::BlockNumberOrHash;
use crate::CliConfiguration;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::fmt::Debug;
use std::str::FromStr;
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
	pub async fn run<B, BA, CE, IQ, RA>(
		&self,
		client: std::sync::Arc<sc_service::Client<BA, CE, B, RA>>,
		import_queue: IQ,
	) -> error::Result<()>
	where
		B: BlockT + for<'de> serde::Deserialize<'de>,
		BA: sc_client_api::backend::Backend<B> + 'static,
		CE: sc_client_api::call_executor::CallExecutor<B> + Send + Sync + 'static,
		IQ: sc_service::ImportQueue<B> + 'static,
		RA: Send + Sync + 'static,
		<B as BlockT>::Hash: FromStr,
		<<B as BlockT>::Hash as FromStr>::Err: Debug,
		<<<B as BlockT>::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let start = std::time::Instant::now();
		let block_id = self.input.parse()?;
		sc_service::check_block(client, import_queue, block_id).await?;
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
