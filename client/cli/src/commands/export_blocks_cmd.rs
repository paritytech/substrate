// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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
	params::{DatabaseParams, GenericNumber, PruningParams, SharedParams},
	CliConfiguration,
};
use clap::Parser;
use log::info;
use sc_client_api::{BlockBackend, UsageProvider};
use sc_service::{chain_ops::export_blocks, config::DatabaseSource};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{fmt::Debug, fs, io, path::PathBuf, str::FromStr, sync::Arc};

/// The `export-blocks` command used to export blocks.
#[derive(Debug, Clone, Parser)]
pub struct ExportBlocksCmd {
	/// Output file name or stdout if unspecified.
	#[clap(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify starting block number.
	///
	/// Default is 1.
	#[clap(long, value_name = "BLOCK")]
	pub from: Option<GenericNumber>,

	/// Specify last block number.
	///
	/// Default is best block.
	#[clap(long, value_name = "BLOCK")]
	pub to: Option<GenericNumber>,

	/// Use binary output rather than JSON.
	#[clap(long)]
	pub binary: bool,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,
}

impl ExportBlocksCmd {
	/// Run the export-blocks command
	pub async fn run<B, C>(
		&self,
		client: Arc<C>,
		database_config: DatabaseSource,
	) -> error::Result<()>
	where
		B: BlockT,
		C: BlockBackend<B> + UsageProvider<B> + 'static,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseSource::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		let from = self.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1u32);
		let to = self.to.as_ref().and_then(|t| t.parse().ok());

		let binary = self.binary;

		let file: Box<dyn io::Write> = match &self.output {
			Some(filename) => Box::new(fs::File::create(filename)?),
			None => Box::new(io::stdout()),
		};

		export_blocks(client, file, from.into(), to, binary).await.map_err(Into::into)
	}
}

impl CliConfiguration for ExportBlocksCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}
}
