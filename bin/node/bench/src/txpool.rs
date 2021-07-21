// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Transaction pool integrated benchmarks.
//!
//! The goal of this benchmark is to figure out time needed to fill
//! the transaction pool for the next block.

use std::borrow::Cow;

use node_testing::bench::{BenchDb, BlockType, DatabaseType, KeyTypes, Profile};

use sc_transaction_pool::BasicPool;
use sc_transaction_pool_api::{TransactionPool, TransactionSource};
use sp_runtime::generic::BlockId;

use crate::core::{self, Mode, Path};

pub struct PoolBenchmarkDescription {
	pub database_type: DatabaseType,
}

pub struct PoolBenchmark {
	database: BenchDb,
}

impl core::BenchmarkDescription for PoolBenchmarkDescription {
	fn path(&self) -> Path {
		Path::new(&["node", "txpool"])
	}

	fn setup(self: Box<Self>) -> Box<dyn core::Benchmark> {
		Box::new(PoolBenchmark {
			database: BenchDb::with_key_types(self.database_type, 50_000, KeyTypes::Sr25519),
		})
	}

	fn name(&self) -> Cow<'static, str> {
		"Transaction pool benchmark".into()
	}
}

impl core::Benchmark for PoolBenchmark {
	fn run(&mut self, mode: Mode) -> std::time::Duration {
		let context = self.database.create_context(Profile::Wasm);

		let _ = context
			.client
			.runtime_version_at(&BlockId::Number(0))
			.expect("Failed to get runtime version")
			.spec_version;

		if mode == Mode::Profile {
			std::thread::park_timeout(std::time::Duration::from_secs(3));
		}

		let executor = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			true.into(),
			None,
			executor,
			context.client.clone(),
		);

		let generated_transactions = self
			.database
			.block_content(
				BlockType::RandomTransfersKeepAlive.to_content(Some(100)),
				&context.client,
			)
			.into_iter()
			.collect::<Vec<_>>();

		let start = std::time::Instant::now();
		let submissions = generated_transactions
			.into_iter()
			.map(|tx| txpool.submit_one(&BlockId::Number(0), TransactionSource::External, tx));
		futures::executor::block_on(futures::future::join_all(submissions));
		let elapsed = start.elapsed();

		if mode == Mode::Profile {
			std::thread::park_timeout(std::time::Duration::from_secs(1));
		}
		elapsed
	}
}
