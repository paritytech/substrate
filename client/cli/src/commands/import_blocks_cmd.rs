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

use std::fmt::Debug;
use std::io::{Read, Seek, self};
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;
use sc_service::{
	Configuration, ServiceBuilderCommand, ChainSpec, Roles,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::VersionInfo;
use crate::runtime::run_until_exit;
use crate::params::SharedParams;
use crate::params::ImportParams;

/// The `import-blocks` command used to import blocks.
#[derive(Debug, StructOpt, Clone)]
pub struct ImportBlocksCmd {
	/// Input file or stdin if unspecified.
	#[structopt(parse(from_os_str))]
	pub input: Option<PathBuf>,

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

/// Internal trait used to cast to a dynamic type that implements Read and Seek.
trait ReadPlusSeek: Read + Seek {}

impl<T: Read + Seek> ReadPlusSeek for T {}

impl ImportBlocksCmd {
	/// Run the import-blocks command
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
		let file: Box<dyn ReadPlusSeek + Send> = match &self.input {
			Some(filename) => Box::new(fs::File::open(filename)?),
			None => {
				let mut buffer = Vec::new();
				io::stdin().read_to_end(&mut buffer)?;
				Box::new(io::Cursor::new(buffer))
			},
		};

		run_until_exit(config, |config| {
			Ok(builder(config)?.import_blocks(file, false))
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
		self.import_params.update_config(&mut config, Roles::FULL, self.shared_params.dev)?;
		config.use_in_memory_keystore()?;

		Ok(())
	}
}
