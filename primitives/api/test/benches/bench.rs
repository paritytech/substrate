// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use criterion::{criterion_group, criterion_main, Criterion};
use sp_api::ProvideRuntimeApi;
use sp_state_machine::ExecutionStrategy;
use substrate_test_runtime_client::{
	runtime::TestAPI, DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
};

fn sp_api_benchmark(c: &mut Criterion) {
	c.bench_function("add one with same runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let runtime_api = client.runtime_api();
		let best_hash = client.chain_info().best_hash;

		b.iter(|| runtime_api.benchmark_add_one(best_hash, &1))
	});

	c.bench_function("add one with recreating runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let best_hash = client.chain_info().best_hash;

		b.iter(|| client.runtime_api().benchmark_add_one(best_hash, &1))
	});

	c.bench_function("vector add one with same runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let runtime_api = client.runtime_api();
		let best_hash = client.chain_info().best_hash;
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| runtime_api.benchmark_vector_add_one(best_hash, &data))
	});

	c.bench_function("vector add one with recreating runtime api", |b| {
		let client = substrate_test_runtime_client::new();
		let best_hash = client.chain_info().best_hash;
		let data = vec![0; 1000];

		b.iter_with_large_drop(|| client.runtime_api().benchmark_vector_add_one(best_hash, &data))
	});

	c.bench_function("calling function by function pointer in wasm", |b| {
		let client = TestClientBuilder::new()
			.set_execution_strategy(ExecutionStrategy::AlwaysWasm)
			.build();
		let best_hash = client.chain_info().best_hash;
		b.iter(|| client.runtime_api().benchmark_indirect_call(best_hash).unwrap())
	});

	c.bench_function("calling function in wasm", |b| {
		let client = TestClientBuilder::new()
			.set_execution_strategy(ExecutionStrategy::AlwaysWasm)
			.build();
		let best_hash = client.chain_info().best_hash;
		b.iter(|| client.runtime_api().benchmark_direct_call(best_hash).unwrap())
	});
}

criterion_group!(benches, sp_api_benchmark);
criterion_main!(benches);
