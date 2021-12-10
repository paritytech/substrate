// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Provides the [`MetadataDump`] command for dumping the runtime metadata.

use crate::{
	error,
	params::SharedParams,
	CliConfiguration,
};
use log::info;
use sc_client_api::UsageProvider;
use sp_runtime::{traits::Block as BlockT, generic::BlockId};
use std::{fmt::Debug, fs, io::{self, Write}, path::PathBuf, sync::Arc};
use structopt::StructOpt;
use sp_api::{ProvideRuntimeApi, Metadata};

/// The `metadata-dump` command used to dump the metadata of the runtime.
#[derive(Debug, StructOpt, Clone)]
pub struct MetadataDump {
	/// Output file name or stdout if unspecified.
	#[structopt(long, short = "o", parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Use binary output rather than hex.
	#[structopt(long)]
	pub binary: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl MetadataDump {
	/// Run the metadata-dump command
	pub fn run<B, C>(&self, client: Arc<C>) -> error::Result<()>
	where
		B: BlockT,
		C: ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: Metadata<B>,
	{
		let best_hash = client.usage_info().chain.best_hash;
		let metadata = client.runtime_api().metadata(&BlockId::Hash(best_hash))?;

		info!("Dumping metadata for block `{:?}`.", best_hash);

		// Convert the metadata to the requested format
		let metadata_output = if self.binary {
			metadata.to_vec()
		} else {
			hex::encode(&*metadata).as_bytes().to_vec()
		};

		// And print or write it to a file.
		if let Some(ref output) = self.output {
			fs::write(output, metadata_output)
		} else {
			io::stdout().lock().write_all(&metadata_output)
		}.map_err(Into::into)
	}
}

impl CliConfiguration for MetadataDump {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
