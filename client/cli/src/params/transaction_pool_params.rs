// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use sc_service::config::TransactionPoolOptions;
use structopt::StructOpt;

/// Parameters used to create the pool configuration.
#[derive(Debug, StructOpt)]
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
	pub fn transaction_pool(&self) -> TransactionPoolOptions {
		let mut opts = TransactionPoolOptions::default();

		// ready queue
		opts.ready.count = self.pool_limit;
		opts.ready.total_bytes = self.pool_kbytes * 1024;

		// future queue
		let factor = 10;
		opts.future.count = self.pool_limit / factor;
		opts.future.total_bytes = self.pool_kbytes * 1024 / factor;

		opts
	}
}
