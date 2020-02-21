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

use std::fmt;
use node_testing::bench::{BenchDb, Profile};
use node_primitives::Block;
use sp_runtime::generic::BlockId;
use criterion::{Criterion, criterion_group, criterion_main};
use sc_client_api::backend::Backend;

criterion_group!(
	name = benches;
	config = Criterion::default().sample_size(50).warm_up_time(std::time::Duration::from_secs(20));
	targets = bench_block_import
);
criterion_group!(
	name = wasm_size;
	config = Criterion::default().sample_size(10);
	targets = bench_wasm_size_import
);
criterion_group!(
	name = profile;
	config = Criterion::default().sample_size(10);
	targets = profile_block_import
);
criterion_main!(benches, profile);

fn bench_block_import(c: &mut Criterion) {
	sc_cli::init_logger("");
	// for future uses, uncomment if something wrong.
	// sc_cli::init_logger("sc_client=debug");

	let mut bench_db = BenchDb::new(128);
	let block = bench_db.generate_block(100);

	log::trace!(
		target: "bench-logistics",
		"Seed database directory: {}",
		bench_db.path().display(),
	);

	c.bench_function_over_inputs("import block",
		move |bencher, profile| {
			bencher.iter_batched(
				|| {
					let context = bench_db.create_context(*profile);

					// mostly to just launch compiler before benching!
					let version = context.client.runtime_version_at(&BlockId::Number(0))
						.expect("Failed to get runtime version")
						.spec_version;

					log::trace!(
						target: "bench-logistics",
						"Next iteration database directory: {}, runtime version: {}",
						context.path().display(), version,
					);

					context
				},
				|mut context| {
					let start = std::time::Instant::now();
					context.import_block(block.clone());
					let elapsed = start.elapsed();

					log::info!(
						target: "bench-logistics",
						"imported block with {} tx, took: {:#?}",
						block.extrinsics.len(),
						elapsed,
					);

					log::info!(
						target: "bench-logistics",
						"usage info: {}",
						context.backend.usage_info()
							.expect("RocksDB backend always provides usage info!"),
					);
				},
				criterion::BatchSize::PerIteration,
			);
		},
		vec![Profile::Wasm, Profile::Native],
	);
}

// This is not an actual benchmark, so don't use it to measure anything.
//   It just produces special pattern of cpu load that allows easy picking
//   the part of block import for the profiling in the tool of choice.
fn profile_block_import(c: &mut Criterion) {
	sc_cli::init_logger("");

	let mut bench_db = BenchDb::new(128);
	let block = bench_db.generate_block(100);

	c.bench_function("profile block",
		move |bencher| {
			bencher.iter_batched(
				|| {
					bench_db.create_context(Profile::Native)
				},
				|mut context| {
					// until better osx signpost/callgrind signal is possible to use
					// in rust, we just pause everything completely to help choosing
					// actual profiling interval
					std::thread::park_timeout(std::time::Duration::from_secs(2));
					context.import_block(block.clone());
					// and here as well
					std::thread::park_timeout(std::time::Duration::from_secs(2));
					log::info!(
						target: "bench-logistics",
						"imported block, usage info: {}",
						context.backend.usage_info()
							.expect("RocksDB backend always provides usage info!"),
					)
				},
				criterion::BatchSize::PerIteration,
			);
		},
	);
}

struct Setup {
	db: BenchDb,
	block: Block,
}

struct SetupIterator {
	current: usize,
	finish: usize,
	multiplier: usize,
}

impl SetupIterator {
	fn new(current: usize, finish: usize, multiplier: usize) -> Self {
		SetupIterator { current, finish, multiplier }
	}
}

impl Iterator for SetupIterator {
	type Item = Setup;

	fn next(&mut self) -> Option<Setup> {
		if self.current >= self.finish { return None }

		self.current += 1;

		let size = self.current * self.multiplier;
		let mut db = BenchDb::new(size);
		let block = db.generate_block(size);
		Some(Setup { db, block })
	}
}

impl fmt::Debug for Setup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Setup: {} tx/block", self.block.extrinsics.len())
    }
}

fn bench_wasm_size_import(c: &mut Criterion) {
	sc_cli::init_logger("");

	c.bench_function_over_inputs("wasm_size_import",
		move |bencher, setup| {
			bencher.iter_batched(
				|| {
					setup.db.create_context(Profile::Wasm)
				},
				|mut context| {
					context.import_block(setup.block.clone());
				},
				criterion::BatchSize::PerIteration,
			);
		},
		SetupIterator::new(5, 15, 50),
	);
}
