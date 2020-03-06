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

use structopt::StructOpt;
use sc_service::Configuration;
use crate::error;

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
