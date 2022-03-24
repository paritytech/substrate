// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use sc_executor_common::{runtime_blob::RuntimeBlob, wasm_runtime::WasmModule};
use sc_runtime_test::wasm_binary_unwrap as test_runtime;
use sp_wasm_interface::HostFunctions as _;
use std::sync::Arc;

enum Method {
	Interpreted,
	#[cfg(feature = "wasmtime")]
	Compiled {
		fast_instance_reuse: bool,
	},
}

// This is just a bog-standard Kusama runtime with the extra `test_empty_return`
// function copy-pasted from the test runtime.
fn kusama_runtime() -> &'static [u8] {
	include_bytes!("kusama_runtime.wasm")
}

fn initialize(runtime: &[u8], method: Method) -> Arc<dyn WasmModule> {
	let blob = RuntimeBlob::uncompress_if_needed(runtime).unwrap();
	let host_functions = sp_io::SubstrateHostFunctions::host_functions();
	let heap_pages = 2048;
	let allow_missing_func_imports = true;

	match method {
		Method::Interpreted => sc_executor_wasmi::create_runtime(
			blob,
			heap_pages,
			host_functions,
			allow_missing_func_imports,
		)
		.map(|runtime| -> Arc<dyn WasmModule> { Arc::new(runtime) }),
		#[cfg(feature = "wasmtime")]
		Method::Compiled { fast_instance_reuse } =>
			sc_executor_wasmtime::create_runtime::<sp_io::SubstrateHostFunctions>(
				blob,
				sc_executor_wasmtime::Config {
					max_memory_size: None,
					allow_missing_func_imports,
					cache_path: None,
					semantics: sc_executor_wasmtime::Semantics {
						extra_heap_pages: heap_pages,
						fast_instance_reuse,
						deterministic_stack_limit: None,
						canonicalize_nans: false,
						parallel_compilation: true,
					},
				},
			)
			.map(|runtime| -> Arc<dyn WasmModule> { Arc::new(runtime) }),
	}
	.unwrap()
}

fn bench_call_instance(c: &mut Criterion) {
	let _ = env_logger::try_init();

	#[cfg(feature = "wasmtime")]
	{
		let runtime = initialize(test_runtime(), Method::Compiled { fast_instance_reuse: true });
		c.bench_function("call_instance_test_runtime_with_fast_instance_reuse", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap())
		});
	}

	#[cfg(feature = "wasmtime")]
	{
		let runtime = initialize(test_runtime(), Method::Compiled { fast_instance_reuse: false });
		c.bench_function("call_instance_test_runtime_without_fast_instance_reuse", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap());
		});
	}

	#[cfg(feature = "wasmtime")]
	{
		let runtime = initialize(kusama_runtime(), Method::Compiled { fast_instance_reuse: true });
		c.bench_function("call_instance_kusama_runtime_with_fast_instance_reuse", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap())
		});
	}

	#[cfg(feature = "wasmtime")]
	{
		let runtime = initialize(kusama_runtime(), Method::Compiled { fast_instance_reuse: false });
		c.bench_function("call_instance_kusama_runtime_without_fast_instance_reuse", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap());
		});
	}

	{
		let runtime = initialize(test_runtime(), Method::Interpreted);
		c.bench_function("call_instance_test_runtime_interpreted", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap())
		});
	}

	{
		let runtime = initialize(kusama_runtime(), Method::Interpreted);
		c.bench_function("call_instance_kusama_runtime_interpreted", |b| {
			let mut instance = runtime.new_instance().unwrap();
			b.iter(|| instance.call_export("test_empty_return", &[0]).unwrap())
		});
	}
}

criterion_group! {
	name = benches;
	config = Criterion::default();
	targets = bench_call_instance
}
criterion_main!(benches);
