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

use std::io;
use std::fs;
use std::path::PathBuf;
use std::fmt::Debug;
use log::info;
use structopt::StructOpt;
use sc_service::{
	Configuration, ServiceBuilderCommand, ChainSpec,
	config::DatabaseConfig, Roles,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::VersionInfo;
use crate::runtime::run_until_exit;
use crate::params::{SharedParams, BlockNumber, PruningParams};

/// The `export-blocks` command used to export blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct ExportBlocksCmd {
	/// Output file name or stdout if unspecified.
	#[structopt(parse(from_os_str))]
	pub output: Option<PathBuf>,

	/// Specify starting block number.
	///
	/// Default is 1.
	#[structopt(long = "from", value_name = "BLOCK")]
	pub from: Option<BlockNumber>,

	/// Specify last block number.
	///
	/// Default is best block.
	#[structopt(long = "to", value_name = "BLOCK")]
	pub to: Option<BlockNumber>,

	/// Use binary output rather than JSON.
	#[structopt(long = "binary", value_name = "BOOL", parse(try_from_str), default_value("false"))]
	pub binary: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

impl ExportBlocksCmd {
	/// Run the export-blocks command
	pub fn run<B, BC, BB>(
		self,
		config: Configuration,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration) -> Result<BC, sc_service::error::Error>,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		if let DatabaseConfig::Path { ref path, .. } = config.expect_database() {
			info!("DB path: {}", path.display());
		}
		let from = self.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1);
		let to = self.to.as_ref().and_then(|t| t.parse().ok());

		let binary = self.binary;

		let file: Box<dyn io::Write> = match &self.output {
			Some(filename) => Box::new(fs::File::create(filename)?),
			None => Box::new(io::stdout()),
		};

		run_until_exit(config, |config| {
			Ok(builder(config)?.export_blocks(file, from.into(), to, binary))
		})
	}

	/// Update and prepare a `Configuration` with command line parameters
	pub fn update_config<F>(
		&self,
		mut config: &mut Configuration,
		spec_factory: F,
		version: &VersionInfo,
	) -> error::Result<()> where
		F: FnOnce(&str) -> Result<Box<dyn ChainSpec>, String>,
	{
		self.shared_params.update_config(&mut config, spec_factory, version)?;
		self.pruning_params.update_config(&mut config, Roles::FULL, true)?;
		config.use_in_memory_keystore()?;

		Ok(())
	}
}
