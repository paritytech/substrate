// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Experimental: commands for using snapshots.

use crate::error;
use crate::params::{GenericNumber, DatabaseParams, PruningParams, SharedParams};
use crate::CliConfiguration;
use log::info;
use sc_service::config::DatabaseConfig;
use sc_client_api::SnapshotConfig;
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::fmt::Debug;
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::Arc;
use structopt::StructOpt;

/// The `snapshot` command used to export snapshot.
#[derive(Debug, StructOpt)]
pub struct SnapshotExportCmd {
	/// Output file name or stdout if unspecified.
	#[structopt(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify snapshot block number to import.
	///
	/// Default is best block.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<GenericNumber>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

/// The `snapshot` command used to import snapshot.
#[derive(Debug, StructOpt)]
pub struct SnapshotImportCmd {
	/// Input file or stdin if unspecified.
	#[structopt(parse(from_os_str))]
	pub input: Option<PathBuf>,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub database_params: DatabaseParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

impl SnapshotImportCmd {
	/// Run the import-snapshot command
	pub async fn run<B, BA>(
		&self,
		backend: Arc<BA>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		let mut file: Box<dyn std::io::Read + Send> = match &self.input {
			Some(filename) => Box::new(zstd::Decoder::new(std::fs::File::open(filename)?)?),
			None => Box::new(zstd::Decoder::new(std::io::stdin())?),
		};

		backend.snapshot_sync().import_sync(&mut file)?;
		Ok(())
	}
}

impl SnapshotExportCmd {
	/// Run the export-snapshot command
	pub async fn run<B, BA>(
		&self,
		backend: Arc<BA>,
		database_config: DatabaseConfig,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		if let DatabaseConfig::RocksDb { ref path, .. } = database_config {
			info!("DB path: {}", path.display());
		}

		let chain_info = backend.blockchain().info();
		let finalized_hash = chain_info.finalized_hash;
		let finalized_number = chain_info.finalized_number;
		let (to, default_block) = if let Some(to) = self.to.as_ref() {
			let to = to.parse()?;
			let to_hash = backend.blockchain().hash(to)?.expect("Block number out of range.");
			(to, to_hash)
		} else {
			(finalized_number, finalized_hash)
		};
		let range = SnapshotConfig {
			to,
			to_hash: default_block.clone(),
			from: to, // Single block snapshot.
			from_hash: default_block,
		};

		info!("Export using config : {:?}, chain info : {:?}", range, chain_info);
		if let Some(path) = &self.output {
			let out = std::fs::File::create(path)?;
			let mut out = zstd::Encoder::new(out, 3)?;
			backend.snapshot_sync().export_sync(&mut out, range)?;
			out.finish()?;
		} else {
			let out = std::io::stdout();
			let mut out = zstd::Encoder::new(out, 3)?;
			backend.snapshot_sync().export_sync(&mut out, range)?;
			out.finish()?;
		};

		Ok(())
	}
}

impl CliConfiguration for SnapshotExportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}

impl CliConfiguration for SnapshotImportCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}
