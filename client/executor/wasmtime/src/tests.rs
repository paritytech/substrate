// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use codec::{Decode as _, Encode as _};
use sc_executor_common::{error::Error, runtime_blob::RuntimeBlob, wasm_runtime::WasmModule};
use sc_runtime_test::wasm_binary_unwrap;
use std::sync::Arc;

type HostFunctions = sp_io::SubstrateHostFunctions;

struct RuntimeBuilder {
	code: Option<String>,
	fast_instance_reuse: bool,
	canonicalize_nans: bool,
	deterministic_stack: bool,
	extra_heap_pages: u64,
	max_memory_size: Option<usize>,
	precompile_runtime: bool,
}

impl RuntimeBuilder {
	/// Returns a new builder that won't use the fast instance reuse mechanism, but instead will
	/// create a new runtime instance each time.
	fn new_on_demand() -> Self {
		Self {
			code: None,
			fast_instance_reuse: false,
			canonicalize_nans: false,
			deterministic_stack: false,
			extra_heap_pages: 1024,
			max_memory_size: None,
			precompile_runtime: false,
		}
	}

	fn use_wat(&mut self, code: String) -> &mut Self {
		self.code = Some(code);
		self
	}

	fn canonicalize_nans(&mut self, canonicalize_nans: bool) -> &mut Self {
		self.canonicalize_nans = canonicalize_nans;
		self
	}

	fn deterministic_stack(&mut self, deterministic_stack: bool) -> &mut Self {
		self.deterministic_stack = deterministic_stack;
		self
	}

	fn precompile_runtime(&mut self, precompile_runtime: bool) -> &mut Self {
		self.precompile_runtime = precompile_runtime;
		self
	}

	fn max_memory_size(&mut self, max_memory_size: Option<usize>) -> &mut Self {
		self.max_memory_size = max_memory_size;
		self
	}

	fn build(&mut self) -> Arc<dyn WasmModule> {
		let blob = {
			let wasm: Vec<u8>;

			let wasm = match self.code {
				None => wasm_binary_unwrap(),
				Some(ref wat) => {
					wasm = wat::parse_str(wat).expect("wat parsing failed");
					&wasm
				},
			};

			RuntimeBlob::uncompress_if_needed(&wasm)
				.expect("failed to create a runtime blob out of test runtime")
		};

		let config = crate::Config {
			max_memory_size: self.max_memory_size,
			allow_missing_func_imports: true,
			cache_path: None,
			semantics: crate::Semantics {
				fast_instance_reuse: self.fast_instance_reuse,
				deterministic_stack_limit: match self.deterministic_stack {
					true => Some(crate::DeterministicStackLimit {
						logical_max: 65536,
						native_stack_max: 256 * 1024 * 1024,
					}),
					false => None,
				},
				canonicalize_nans: self.canonicalize_nans,
				parallel_compilation: true,
				extra_heap_pages: self.extra_heap_pages,
			},
		};

		let rt = if self.precompile_runtime {
			let artifact = crate::prepare_runtime_artifact(blob, &config.semantics).unwrap();
			unsafe { crate::create_runtime_from_artifact::<HostFunctions>(&artifact, config) }
		} else {
			crate::create_runtime::<HostFunctions>(blob, config)
		}
		.expect("cannot create runtime");

		Arc::new(rt) as Arc<dyn WasmModule>
	}
}

#[test]
fn test_nan_canonicalization() {
	let runtime = RuntimeBuilder::new_on_demand().canonicalize_nans(true).build();

	let mut instance = runtime.new_instance().expect("failed to instantiate a runtime");

	/// A NaN with canonical payload bits.
	const CANONICAL_NAN_BITS: u32 = 0x7fc00000;
	/// A NaN value with an abitrary payload.
	const ARBITRARY_NAN_BITS: u32 = 0x7f812345;

	// This test works like this: we essentially do
	//
	//     a + b
	//
	// where
	//
	//     * a is a nan with arbitrary bits in its payload
	//     * b is 1.
	//
	// according to the wasm spec, if one of the inputs to the operation is a non-canonical NaN
	// then the value be a NaN with non-deterministic payload bits.
	//
	// However, with the `canonicalize_nans` option turned on above, we expect that the output will
	// be a canonical NaN.
	//
	// We exterpolate the results of this tests so that we assume that all intermediate computations
	// that involve floats are sanitized and cannot produce a non-deterministic NaN.

	let params = (u32::to_le_bytes(ARBITRARY_NAN_BITS), u32::to_le_bytes(1)).encode();
	let res = {
		let raw_result = instance.call_export("test_fp_f32add", &params).unwrap();
		u32::from_le_bytes(<[u8; 4]>::decode(&mut &raw_result[..]).unwrap())
	};
	assert_eq!(res, CANONICAL_NAN_BITS);
}

#[test]
fn test_stack_depth_reaching() {
	const TEST_GUARD_PAGE_SKIP: &str = include_str!("test-guard-page-skip.wat");

	let runtime = RuntimeBuilder::new_on_demand()
		.use_wat(TEST_GUARD_PAGE_SKIP.to_string())
		.deterministic_stack(true)
		.build();
	let mut instance = runtime.new_instance().expect("failed to instantiate a runtime");

	match instance.call_export("test-many-locals", &[]).unwrap_err() {
		Error::AbortedDueToTrap(error) => {
			let expected = "wasm trap: wasm `unreachable` instruction executed";
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

#[test]
fn test_max_memory_pages_imported_memory_without_precompilation() {
	test_max_memory_pages(true, false);
}

#[test]
fn test_max_memory_pages_exported_memory_without_precompilation() {
	test_max_memory_pages(false, false);
}

#[test]
fn test_max_memory_pages_imported_memory_with_precompilation() {
	test_max_memory_pages(true, true);
}

#[test]
fn test_max_memory_pages_exported_memory_with_precompilation() {
	test_max_memory_pages(false, true);
}

fn test_max_memory_pages(import_memory: bool, precompile_runtime: bool) {
	fn try_instantiate(
		max_memory_size: Option<usize>,
		wat: String,
		precompile_runtime: bool,
	) -> Result<(), Box<dyn std::error::Error>> {
		let runtime = RuntimeBuilder::new_on_demand()
			.use_wat(wat)
			.max_memory_size(max_memory_size)
			.precompile_runtime(precompile_runtime)
			.build();
		let mut instance = runtime.new_instance()?;
		let _ = instance.call_export("main", &[])?;
		Ok(())
	}

	fn memory(initial: u32, maximum: Option<u32>, import: bool) -> String {
		let memory = if let Some(maximum) = maximum {
			format!("(memory $0 {} {})", initial, maximum)
		} else {
			format!("(memory $0 {})", initial)
		};

		if import {
			format!("(import \"env\" \"memory\" {})", memory)
		} else {
			format!("{}\n(export \"memory\" (memory $0))", memory)
		}
	}

	const WASM_PAGE_SIZE: usize = 65536;

	// check the old behavior if preserved. That is, if no limit is set we allow 4 GiB of memory.
	try_instantiate(
		None,
		format!(
			r#"
			(module
				{}
				(global (export "__heap_base") i32 (i32.const 0))
				(func (export "main")
					(param i32 i32) (result i64)
					(i64.const 0)
				)
			)
			"#,
			/*
				We want to allocate the maximum number of pages supported in wasm for this test.
				However, due to a bug in wasmtime (I think wasmi is also affected) it is only possible
				to allocate 65536 - 1 pages.

				Then, during creation of the Substrate Runtime instance, 1024 (heap_pages) pages are
				mounted.

				Thus 65535 = 64511 + 1024
			*/
			memory(64511, None, import_memory)
		),
		precompile_runtime,
	)
	.unwrap();

	// max is not specified, therefore it's implied to be 65536 pages (4 GiB).
	//
	// max_memory_size = (1 (initial) + 1024 (heap_pages)) * WASM_PAGE_SIZE
	try_instantiate(
		Some((1 + 1024) * WASM_PAGE_SIZE),
		format!(
			r#"
			(module
				{}
				(global (export "__heap_base") i32 (i32.const 0))
				(func (export "main")
					(param i32 i32) (result i64)
					(i64.const 0)
				)
			)
			"#,
			// 1 initial, max is not specified.
			memory(1, None, import_memory)
		),
		precompile_runtime,
	)
	.unwrap();

	// max is specified explicitly to 2048 pages.
	try_instantiate(
		Some((1 + 1024) * WASM_PAGE_SIZE),
		format!(
			r#"
			(module
				{}
				(global (export "__heap_base") i32 (i32.const 0))
				(func (export "main")
					(param i32 i32) (result i64)
					(i64.const 0)
				)
			)
			"#,
			// Max is 2048.
			memory(1, Some(2048), import_memory)
		),
		precompile_runtime,
	)
	.unwrap();

	// memory grow should work as long as it doesn't exceed 1025 pages in total.
	try_instantiate(
		Some((0 + 1024 + 25) * WASM_PAGE_SIZE),
		format!(
			r#"
			(module
				{}
				(global (export "__heap_base") i32 (i32.const 0))
				(func (export "main")
					(param i32 i32) (result i64)

					;; assert(memory.grow returns != -1)
					(if
						(i32.eq
							(memory.grow
								(i32.const 25)
							)
							(i32.const -1)
						)
						(unreachable)
					)

					(i64.const 0)
				)
			)
			"#,
			// Zero starting pages.
			memory(0, None, import_memory)
		),
		precompile_runtime,
	)
	.unwrap();

	// We start with 1025 pages and try to grow at least one.
	try_instantiate(
		Some((1 + 1024) * WASM_PAGE_SIZE),
		format!(
			r#"
			(module
				{}
				(global (export "__heap_base") i32 (i32.const 0))
				(func (export "main")
					(param i32 i32) (result i64)

					;; assert(memory.grow returns == -1)
					(if
						(i32.ne
							(memory.grow
								(i32.const 1)
							)
							(i32.const -1)
						)
						(unreachable)
					)

					(i64.const 0)
				)
			)
			"#,
			// Initial=1, meaning after heap pages mount the total will be already 1025.
			memory(1, None, import_memory)
		),
		precompile_runtime,
	)
	.unwrap();
}

// This test takes quite a while to execute in a debug build (over 6 minutes on a TR 3970x)
// so it's ignored by default unless it was compiled with `--release`.
#[cfg_attr(build_type = "debug", ignore)]
#[test]
fn test_instances_without_reuse_are_not_leaked() {
	let runtime = crate::create_runtime::<HostFunctions>(
		RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
		crate::Config {
			max_memory_size: None,
			allow_missing_func_imports: true,
			cache_path: None,
			semantics: crate::Semantics {
				fast_instance_reuse: false,
				deterministic_stack_limit: None,
				canonicalize_nans: false,
				parallel_compilation: true,
				extra_heap_pages: 2048,
			},
		},
	)
	.unwrap();

	// As long as the `wasmtime`'s `Store` lives the instances spawned through it
	// will live indefinitely. Currently it has a maximum limit of 10k instances,
	// so let's spawn 10k + 1 of them to make sure our code doesn't keep the `Store`
	// alive longer than it is necessary. (And since we disabled instance reuse
	// a new instance will be spawned on each call.)
	let mut instance = runtime.new_instance().unwrap();
	for _ in 0..10001 {
		instance.call_export("test_empty_return", &[0]).unwrap();
	}
}
