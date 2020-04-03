// Copyright 2020 Parity Technologies (UK) Ltd.
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

use node_testing::bench::{BenchDb, Profile, BlockType, KeyTypes};
use node_primitives::Block;
use sc_client_api::backend::Backend;
use sp_runtime::generic::BlockId;

use crate::core::{self, Path};

pub enum SizeType { Small, Medium, Large }

impl SizeType {
	fn transactions(&self) -> usize {
		match self {
			SizeType::Small => 10,
			SizeType::Medium => 100,
			SizeType::Large => 500,
		}
	}
}

pub struct ImportBenchmarkDescription {
	pub profile: Profile,
	pub key_types: KeyTypes,
	pub size: SizeType,
}

pub struct ImportBenchmark {
	profile: Profile,
	database: BenchDb,
	block: Block,
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

		match self.size {
			SizeType::Small => path.push("small"),
			SizeType::Medium => path.push("medium"),
			SizeType::Large => path.push("large"),
		}

		path
	}

	fn setup(self: Box<Self>) -> Box<dyn core::Benchmark> {
		let profile = self.profile;
		let mut bench_db = BenchDb::with_key_types(self.size.transactions(), self.key_types);
		let block = bench_db.generate_block(BlockType::RandomTransfers(100));
		Box::new(ImportBenchmark {
			database: bench_db,
			block,
			profile,
		})
	}

	fn name(&self) -> Cow<'static, str> {
		match self.profile {
			Profile::Wasm => "Import benchmark (random transfers, wasm)".into(),
			Profile::Native => "Import benchmark (random transfers, native)".into(),
		}
	}
}

impl core::Benchmark for ImportBenchmark {
	fn run(&mut self) -> std::time::Duration {
		let mut context = self.database.create_context(self.profile);

		let _ = context.client.runtime_version_at(&BlockId::Number(0))
			.expect("Failed to get runtime version")
			.spec_version;

		let start = std::time::Instant::now();
		context.import_block(self.block.clone());
		let elapsed = start.elapsed();

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