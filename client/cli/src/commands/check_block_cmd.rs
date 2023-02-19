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

use crate::{
	error,
	params::{BlockNumberOrHash, ImportParams, SharedParams},
	CliConfiguration,
};
use clap::Parser;
use sc_client_api::{BlockBackend, HeaderBackend};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{fmt::Debug, str::FromStr, sync::Arc};

/// The `check-block` command used to validate blocks.
#[derive(Debug, Clone, Parser)]
pub struct CheckBlockCmd {
	/// Block hash or number
	#[arg(value_name = "HASH or NUMBER")]
	pub input: BlockNumberOrHash,

	/// The default number of 64KB pages to ever allocate for Wasm execution.
	///
	/// Don't alter this unless you know what you're doing.
	#[arg(long, value_name = "COUNT")]
	pub default_heap_pages: Option<u32>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,
}

impl CheckBlockCmd {
	/// Run the check-block command
	pub async fn run<B, C, IQ>(&self, client: Arc<C>, import_queue: IQ) -> error::Result<()>
	where
		B: BlockT + for<'de> serde::Deserialize<'de>,
		C: BlockBackend<B> + HeaderBackend<B> + Send + Sync + 'static,
		IQ: sc_service::ImportQueue<B> + 'static,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let start = std::time::Instant::now();
		sc_service::chain_ops::check_block(client, import_queue, self.input.parse()?).await?;
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
