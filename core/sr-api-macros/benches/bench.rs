// Copyright 2018 - 2019 Parity Technologies (UK) Ltd.
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

use criterion::{Criterion, criterion_group, criterion_main};
use test_client::runtime::TestAPI;
use runtime_primitives::{generic::BlockId, traits::ProvideRuntimeApi};
use state_machine::ExecutionStrategy;

fn sr_api_benchmark(c: &mut Criterion) {
	c.bench_function("add one with same runtime api", |b| {
		let client = test_client::new();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);

		b.iter(|| runtime_api.benchmark_add_one(&block_id, &1))
	});

	c.bench_function("add one with recreating runtime api", |b| {
		let client = test_client::new();
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);

		b.iter(|| client.runtime_api().benchmark_add_one(&block_id, &1))
	});

	c.bench_function("vector add one with same runtime api", |b| {
		let client = test_client::new();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| runtime_api.benchmark_vector_add_one(&block_id, &data))
	});

	c.bench_function("vector add one with recreating runtime api", |b| {
		let client = test_client::new();
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| client.runtime_api().benchmark_vector_add_one(&block_id, &data))
	});

	c.bench_function("calling function by function pointer in wasm", |b| {
		let client = test_client::new_with_execution_strategy(ExecutionStrategy::AlwaysWasm);
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);
		b.iter(|| client.runtime_api().benchmark_indirect_call(&block_id).unwrap())
	});

	c.bench_function("calling function in wasm", |b| {
		let client = test_client::new_with_execution_strategy(ExecutionStrategy::AlwaysWasm);
		let block_id = BlockId::Number(client.info().unwrap().chain.best_number);
		b.iter(|| client.runtime_api().benchmark_direct_call(&block_id).unwrap())
	});
}

criterion_group!(benches, sr_api_benchmark);
criterion_main!(benches);
