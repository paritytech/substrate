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

//! Block import benchmark.
//!
//! This benchmark is expected to measure block import operation of
//! some more or less full block.
//!
//! As we also want to protect against cold-cache attacks, this
//! benchmark should not rely on any caching (except those that
//! DO NOT depend on user input). Thus block generation should be
//! based on randomized operation.
//!
//! This is supposed to be very simple benchmark and is not subject
//! to much configuring - just block full of randomized transactions.
//! It is not supposed to measure runtime modules weight correctness

use std::borrow::Cow;

use node_primitives::Block;
use node_testing::bench::{BenchDb, BlockType, DatabaseType, KeyTypes, Profile};
use sc_client_api::backend::Backend;
use sp_runtime::generic::BlockId;
use sp_state_machine::InspectState;

use crate::{
	common::SizeType,
	core::{self, Mode, Path},
};

pub struct ImportBenchmarkDescription {
	pub profile: Profile,
	pub key_types: KeyTypes,
	pub block_type: BlockType,
	pub size: SizeType,
	pub database_type: DatabaseType,
}

pub struct ImportBenchmark {
	profile: Profile,
	database: BenchDb,
	block: Block,
	block_type: BlockType,
}

impl core::BenchmarkDescription for ImportBenchmarkDescription {
	fn path(&self) -> Path {
		let mut path = Path::new(&["node", "import"]);

		match self.profile {
			Profile::Wasm => path.push("wasm"),
			Profile::Native => path.push("native"),
		}

		match self.key_types {
			KeyTypes::Sr25519 => path.push("sr25519"),
			KeyTypes::Ed25519 => path.push("ed25519"),
		}

		match self.block_type {
			BlockType::RandomTransfersKeepAlive => path.push("transfer_keep_alive"),
			BlockType::RandomTransfersReaping => path.push("transfer_reaping"),
			BlockType::Noop => path.push("noop"),
		}

		match self.database_type {
			DatabaseType::RocksDb => path.push("rocksdb"),
			DatabaseType::ParityDb => path.push("paritydb"),
		}

		path.push(&format!("{}", self.size));

		path
	}

	fn setup(self: Box<Self>) -> Box<dyn core::Benchmark> {
		let profile = self.profile;
		let mut bench_db = BenchDb::with_key_types(self.database_type, 50_000, self.key_types);
		let block = bench_db.generate_block(self.block_type.to_content(self.size.transactions()));
		Box::new(ImportBenchmark {
			database: bench_db,
			block_type: self.block_type,
			block,
			profile,
		})
	}

	fn name(&self) -> Cow<'static, str> {
		format!(
			"Block import ({:?}/{}, {:?}, {:?} backend)",
			self.block_type, self.size, self.profile, self.database_type,
		)
		.into()
	}
}

impl core::Benchmark for ImportBenchmark {
	fn run(&mut self, mode: Mode) -> std::time::Duration {
		let mut context = self.database.create_context(self.profile);

		let _ = context
			.client
			.runtime_version_at(&BlockId::Number(0))
			.expect("Failed to get runtime version")
			.spec_version;

		if mode == Mode::Profile {
			std::thread::park_timeout(std::time::Duration::from_secs(3));
		}

		let start = std::time::Instant::now();
		context.import_block(self.block.clone());
		let elapsed = start.elapsed();

		// Sanity checks.
		context
			.client
			.state_at(&BlockId::number(1))
			.expect("state_at failed for block#1")
			.inspect_state(|| {
				match self.block_type {
					BlockType::RandomTransfersKeepAlive => {
						// should be 7 per signed extrinsic + 1 per unsigned
						// we have 1 unsigned and the rest are signed in the block
						// those 7 events per signed are:
						//    - withdraw (Balances::Withdraw) for charging the transaction fee
						//    - new account (System::NewAccount) as we always transfer fund to
						//      non-existent account
						//    - endowed (Balances::Endowed) for this new account
						//    - successful transfer (Event::Transfer) for this transfer operation
						//    - 2x deposit (Balances::Deposit and Treasury::Deposit) for depositing
						//      the transaction fee into the treasury
						//    - extrinsic success
						assert_eq!(
							node_runtime::System::events().len(),
							(self.block.extrinsics.len() - 1) * 7 + 1,
						);
					},
					BlockType::Noop => {
						assert_eq!(
							node_runtime::System::events().len(),
							// should be 2 per signed extrinsic + 1 per unsigned
							// we have 1 unsigned and the rest are signed in the block
							// those 2 events per signed are:
							//    - deposit event for charging transaction fee
							//    - extrinsic success
							(self.block.extrinsics.len() - 1) * 2 + 1,
						);
					},
					_ => {},
				}
			});

		if mode == Mode::Profile {
			std::thread::park_timeout(std::time::Duration::from_secs(1));
		}

		log::info!(
			target: "bench-logistics",
			"imported block with {} tx, took: {:#?}",
			self.block.extrinsics.len(),
			elapsed,
		);

		log::info!(
			target: "bench-logistics",
			"usage info: {}",
			context.backend.usage_info()
				.expect("RocksDB backend always provides usage info!"),
		);

		elapsed
	}
}
