use std::io;
use std::fs;
use std::path::PathBuf;
use std::fmt::Debug;
use log::info;
use structopt::StructOpt;
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
	config::DatabaseConfig,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::runtime::run_until_exit;
use crate::params::SharedParams;
use crate::params::BlockNumber;

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

	/// Use JSON output rather than binary.
	#[structopt(long = "json")]
	pub json: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl ExportBlocksCmd {
	/// Run the export-blocks command
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
		assert!(config.chain_spec.is_some(), "chain_spec must be present before continuing");

		config.use_in_memory_keystore()?;

		if let DatabaseConfig::Path { ref path, .. } = config.expect_database() {
			info!("DB path: {}", path.display());
		}
		let from = self.from.as_ref().and_then(|f| f.parse().ok()).unwrap_or(1);
		let to = self.to.as_ref().and_then(|t| t.parse().ok());

		let json = self.json;

		let file: Box<dyn io::Write> = match &self.output {
			Some(filename) => Box::new(fs::File::create(filename)?),
			None => Box::new(io::stdout()),
		};

		run_until_exit(config, |config| {
			Ok(builder(config)?.export_blocks(file, from.into(), to, json))
		})
	}
}
