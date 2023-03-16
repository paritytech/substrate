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
	params::{ImportParams, SharedParams},
	CliConfiguration,
};
use clap::Parser;
use sc_client_api::HeaderBackend;
use sc_service::chain_ops::import_blocks;
use sp_runtime::traits::Block as BlockT;
use std::{
	fmt::Debug,
	fs,
	io::{self, Read, Seek},
	path::PathBuf,
	sync::Arc,
};

/// The `import-blocks` command used to import blocks.
#[derive(Debug, Parser)]
pub struct ImportBlocksCmd {
	/// Input file or stdin if unspecified.
	#[arg()]
	pub input: Option<PathBuf>,

	/// The default number of 64KB pages to ever allocate for Wasm execution.
	///
	/// Don't alter this unless you know what you're doing.
	#[arg(long, value_name = "COUNT")]
	pub default_heap_pages: Option<u32>,

	/// Try importing blocks from binary format rather than JSON.
	#[arg(long)]
	pub binary: bool,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub import_params: ImportParams,
}

/// Internal trait used to cast to a dynamic type that implements Read and Seek.
trait ReadPlusSeek: Read + Seek {}

impl<T: Read + Seek> ReadPlusSeek for T {}

impl ImportBlocksCmd {
	/// Run the import-blocks command
	pub async fn run<B, C, IQ>(&self, client: Arc<C>, import_queue: IQ) -> error::Result<()>
	where
		C: HeaderBackend<B> + Send + Sync + 'static,
		B: BlockT + for<'de> serde::Deserialize<'de>,
		IQ: sc_service::ImportQueue<B> + 'static,
	{
		let file: Box<dyn Read + Send> = match &self.input {
			Some(filename) => Box::new(fs::File::open(filename)?),
			None => Box::new(io::stdin()),
		};

		import_blocks(client, import_queue, file, false, self.binary)
			.await
			.map_err(Into::into)
	}
}

impl CliConfiguration for ImportBlocksCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn import_params(&self) -> Option<&ImportParams> {
		Some(&self.import_params)
	}
}
