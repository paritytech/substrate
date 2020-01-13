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

use criterion::{Criterion, criterion_group, criterion_main};
use substrate_test_runtime_client::{
	DefaultTestClientBuilderExt, TestClientBuilder,
	TestClientBuilderExt, runtime::TestAPI,
};
use sp_runtime::generic::BlockId;
use sp_state_machine::ExecutionStrategy;
use sp_api::ProvideRuntimeApi;

fn sp_api_benchmark(c: &mut Criterion) {
	c.bench_function("add one with same runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.chain_info().best_number);

		b.iter(|| runtime_api.benchmark_add_one(&block_id, &1))
	});

	c.bench_function("add one with recreating runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let block_id = BlockId::Number(client.chain_info().best_number);

		b.iter(|| client.runtime_api().benchmark_add_one(&block_id, &1))
	});

	c.bench_function("vector add one with same runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let runtime_api = client.runtime_api();
		let block_id = BlockId::Number(client.chain_info().best_number);
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| runtime_api.benchmark_vector_add_one(&block_id, &data))
	});

	c.bench_function("vector add one with recreating runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let block_id = BlockId::Number(client.chain_info().best_number);
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| client.runtime_api().benchmark_vector_add_one(&block_id, &data))
	});

	c.bench_function("calling function by function pointer in wasm", |b| {
		let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
		let block_id = BlockId::Number(client.chain_info().best_number);
		b.iter(|| client.runtime_api().benchmark_indirect_call(&block_id).unwrap())
	});

	c.bench_function("calling function in wasm", |b| {
		let client = TestClientBuilder::new().set_execution_strategy(ExecutionStrategy::AlwaysWasm).build();
		let block_id = BlockId::Number(client.chain_info().best_number);
		b.iter(|| client.runtime_api().benchmark_direct_call(&block_id).unwrap())
	});
}

criterion_group!(benches, sp_api_benchmark);
criterion_main!(benches);
