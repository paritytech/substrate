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

use clap::Args;
use sc_service::config::TransactionPoolOptions;

/// Parameters used to create the pool configuration.
#[derive(Debug, Clone, Args)]
pub struct TransactionPoolParams {
	/// Maximum number of transactions in the transaction pool.
	#[clap(long, value_name = "COUNT", default_value = "8192")]
	pub pool_limit: usize,

	/// Maximum number of kilobytes of all transactions stored in the pool.
	#[clap(long, value_name = "COUNT", default_value = "20480")]
	pub pool_kbytes: usize,

	/// How long a transaction is banned for, if it is considered invalid. Defaults to 1800s.
	#[clap(long, value_name = "SECONDS")]
	pub tx_ban_seconds: Option<u64>,
}

impl TransactionPoolParams {
	/// Fill the given `PoolConfiguration` by looking at the cli parameters.
	pub fn transaction_pool(&self, is_dev: bool) -> TransactionPoolOptions {
		let mut opts = TransactionPoolOptions::default();

		// ready queue
		opts.ready.count = self.pool_limit;
		opts.ready.total_bytes = self.pool_kbytes * 1024;

		// future queue
		let factor = 10;
		opts.future.count = self.pool_limit / factor;
		opts.future.total_bytes = self.pool_kbytes * 1024 / factor;

		opts.ban_time = if let Some(ban_seconds) = self.tx_ban_seconds {
			std::time::Duration::from_secs(ban_seconds)
		} else if is_dev {
			std::time::Duration::from_secs(0)
		} else {
			std::time::Duration::from_secs(30 * 60)
		};

		opts
	}
}
