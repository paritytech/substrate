use std::fmt::Debug;
use structopt::StructOpt;
use sc_service::{
	Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};

use crate::error;
use crate::params::BlockNumber;
use crate::params::SharedParams;

/// The `revert` command used revert the chain to a previous state.
#[derive(Debug, StructOpt, Clone)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: BlockNumber,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl RevertCmd {
	/// Run the revert command
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

		let blocks = self.num.parse()?;
		builder(config)?.revert_chain(blocks)?;

		Ok(())
	}
}
