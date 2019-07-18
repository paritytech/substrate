// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! Benchmark the execution time of Wasm runtime calls.

use consensus::BlockOrigin;
use codec::Encode;
use primitives::NeverNativeValue;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use substrate_client::{CallExecutor, NeverOffchainExt};
use substrate_client::backend::{Backend as BackendT, BlockImportOperation};
use state_machine::{ExecutionManager, OverlayedChanges};
use std::sync::Arc;
use std::time::Duration;
use test_client::prelude::*;
use test_client::runtime::Transfer;

#[cfg(feature = "test-helpers")]
use client::in_mem::Backend as InMemoryBackend;

use criterion::{Criterion, criterion_group, criterion_main, BatchSize};
criterion_group! {
	name = benches;
	config = Criterion::default()
		.sample_size(400)
		.measurement_time(Duration::from_secs(60));
	targets = benchmark_block_import, benchmark_runtime_version
}
criterion_main!(benches);

/// Benchmark the time to make a Core_execute_block call into the test runtime on a simple block
/// with a single transfer.
fn benchmark_block_import(c: &mut Criterion) {
	c.bench_function(
		"Runtime module restoration",
		|b| {
			// Construct backend as in TestClientBuilder::with_default_backend.
			let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
			let client = TestClientBuilder::with_backend(backend.clone()).build();

			// Build and import a block. This populates the state backend cache.
			let block_builder = client.new_block(Default::default()).unwrap();
			let block = block_builder.bake().unwrap();
			client.import(BlockOrigin::Own, block).unwrap();

			// Build a new block to benchmark the import timing of.
			let mut block_builder = client.new_block(Default::default()).unwrap();
			block_builder.push_transfer(Transfer {
				from: AccountKeyring::Alice.into(),
				to: AccountKeyring::Ferdie.into(),
				amount: 42,
				nonce: 0,
			}).unwrap();

			let block = block_builder.bake().unwrap();
			let parent_hash = block.header().parent_hash();
			let state_root = block.header().state_root();
			let encoded_block = block.encode();

			b.iter_batched_ref(
				|| OverlayedChanges::default(),
				|overlay| {
					let executor = client.executor();

					let mut op = backend.begin_operation().unwrap();
					backend.begin_state_operation(&mut op, BlockId::Hash(*parent_hash)).unwrap();

					let transaction_state = op.state().unwrap().unwrap();

					let (_, storage_update, _) = executor.call_at_state::<
						_,
						_,
						fn(_, _) -> _,
						NeverNativeValue,
						fn() -> _
					>(
						transaction_state,
						overlay,
						"Core_execute_block",
						&encoded_block,
						ExecutionManager::AlwaysWasm,
						None,
						NeverOffchainExt::new(),
					).unwrap();

					// Check that block execution was successful by comparing final state root to
					// expected.
					assert_eq!(*state_root, storage_update.1);
				},
				BatchSize::SmallInput,
			)
		}
	);
}

/// Benchmark the time to make a Core_version call into the test runtime.
fn benchmark_runtime_version(c: &mut Criterion) {
	c.bench_function(
		"Runtime module restoration",
		|b| {
			// Construct backend as in TestClientBuilder::with_default_backend.
			let backend = Arc::new(Backend::new_test(std::u32::MAX, std::u64::MAX));
			let client = TestClientBuilder::with_backend(backend.clone()).build();

			// Build and import a block. This populates the state backend cache.
			let block_builder = client.new_block(Default::default()).unwrap();
			let block = block_builder.bake().unwrap();
			client.import(BlockOrigin::Own, block).unwrap();

			let executor = client.executor();
			let expected_version = executor.runtime_version(&BlockId::number(1)).unwrap();

			b.iter_batched_ref(
				|| OverlayedChanges::default(),
				|overlay| {
					let mut op = backend.begin_operation().unwrap();
					backend.begin_state_operation(&mut op, BlockId::number(1)).unwrap();

					let transaction_state = op.state().unwrap().unwrap();

					let (result, _, _) = executor.call_at_state::<
						_,
						_,
						fn(_, _) -> _,
						NeverNativeValue,
						fn() -> _
					>(
						transaction_state,
						overlay,
						"Core_version",
						&[],
						ExecutionManager::AlwaysWasm,
						None,
						NeverOffchainExt::new(),
					).unwrap();

					// Check that execution was successful by comparing to actual runtime version.
					assert_eq!(result.as_encoded(), expected_version.encode());
				},
				BatchSize::SmallInput,
			)
		}
	);
}
