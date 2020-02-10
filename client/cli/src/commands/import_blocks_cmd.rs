use std::fmt::Debug;
use std::io::{Read, Write, Seek, self};
use std::fs;
use std::{str::FromStr, path::PathBuf};
use structopt::{StructOpt, clap::arg_enum};
use log::info;
use sc_network::{
	config::{build_multiaddr, NonReservedPeerMode, TransportConfig, NodeKeyConfig},
	multiaddr::Protocol,
};
use sc_service::{
	AbstractService, Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
	config::{DatabaseConfig, KeystoreConfig}, ChainSpec, PruningMode,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::runtime::run_until_exit;
use crate::execution_strategy::*;
use crate::execution_strategy::ExecutionStrategy;
use crate::commands::shared_params::SharedParams;
use crate::commands::node_key_params::NodeKeyParams;
use crate::commands::import_params::ImportParams;

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
	pub fn run<G, E, B, BC, BB>(
		self,
		mut config: Configuration<G, E>,
		builder: B,
	) -> error::Result<()>
	where
		B: FnOnce(Configuration<G, E>) -> Result<BC, sc_service::error::Error>,
		G: RuntimeGenesis,
		E: ChainSpecExtension,
		BC: ServiceBuilderCommand<Block = BB> + Unpin,
		BB: sp_runtime::traits::Block + Debug,
		<<<BB as BlockT>::Header as HeaderT>::Number as std::str::FromStr>::Err: std::fmt::Debug,
		<BB as BlockT>::Hash: std::str::FromStr,
	{
		self.import_params.update_config(
			&mut config,
			sc_service::Roles::FULL,
			self.shared_params.dev,
		)?;

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
}
