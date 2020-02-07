use structopt::{StructOpt, clap::arg_enum};
use sc_service::{
	AbstractService, Configuration, ChainSpecExtension, RuntimeGenesis, ServiceBuilderCommand,
	config::{DatabaseConfig, KeystoreConfig}, ChainSpec, PruningMode,
};

use crate::error;
use crate::execution_strategy::*;
use crate::execution_strategy::ExecutionStrategy;

/// Parameters used to create the pool configuration.
#[derive(Debug, StructOpt, Clone)]
pub struct TransactionPoolParams {
	/// Maximum number of transactions in the transaction pool.
	#[structopt(long = "pool-limit", value_name = "COUNT", default_value = "8192")]
	pub pool_limit: usize,
	/// Maximum number of kilobytes of all transactions stored in the pool.
	#[structopt(long = "pool-kbytes", value_name = "COUNT", default_value = "20480")]
	pub pool_kbytes: usize,
}

impl TransactionPoolParams {
	/// Fill the given `PoolConfiguration` by looking at the cli parameters.
	pub fn update_config<G, E>(
		&self,
		config: &mut Configuration<G, E>,
	) -> error::Result<()> {
		// ready queue
		config.transaction_pool.ready.count = self.pool_limit;
		config.transaction_pool.ready.total_bytes = self.pool_kbytes * 1024;

		// future queue
		let factor = 10;
		config.transaction_pool.future.count = self.pool_limit / factor;
		config.transaction_pool.future.total_bytes = self.pool_kbytes * 1024 / factor;

		Ok(())
	}
}
