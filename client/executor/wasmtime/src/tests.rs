// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use sc_executor_common::{
	error::Error,
	runtime_blob::RuntimeBlob,
	wasm_runtime::{HeapAllocStrategy, WasmModule, DEFAULT_HEAP_ALLOC_STRATEGY},
};
use sc_runtime_test::wasm_binary_unwrap;

use crate::InstantiationStrategy;

type HostFunctions = sp_io::SubstrateHostFunctions;

#[macro_export]
macro_rules! test_wasm_execution {
	(@no_legacy_instance_reuse $method_name:ident) => {
		paste::item! {
			#[test]
			fn [<$method_name _recreate_instance_cow>]() {
				$method_name(
					InstantiationStrategy::RecreateInstanceCopyOnWrite
				);
			}

			#[test]
			fn [<$method_name _recreate_instance_vanilla>]() {
				$method_name(
					InstantiationStrategy::RecreateInstance
				);
			}

			#[test]
			fn [<$method_name _pooling_cow>]() {
				$method_name(
					InstantiationStrategy::PoolingCopyOnWrite
				);
			}

			#[test]
			fn [<$method_name _pooling_vanilla>]() {
				$method_name(
					InstantiationStrategy::Pooling
				);
			}
		}
	};

	($method_name:ident) => {
		test_wasm_execution!(@no_legacy_instance_reuse $method_name);

		paste::item! {
			#[test]
			fn [<$method_name _legacy_instance_reuse>]() {
				$method_name(
					InstantiationStrategy::LegacyInstanceReuse
				);
			}
		}
	};
}

struct RuntimeBuilder {
	code: Option<String>,
	instantiation_strategy: InstantiationStrategy,
	canonicalize_nans: bool,
	deterministic_stack: bool,
	heap_pages: HeapAllocStrategy,
	precompile_runtime: bool,
	tmpdir: Option<tempfile::TempDir>,
}

impl RuntimeBuilder {
	fn new(instantiation_strategy: InstantiationStrategy) -> Self {
		Self {
			code: None,
			instantiation_strategy,
			canonicalize_nans: false,
			deterministic_stack: false,
			heap_pages: DEFAULT_HEAP_ALLOC_STRATEGY,
			precompile_runtime: false,
			tmpdir: None,
		}
	}

	fn use_wat(mut self, code: String) -> Self {
		self.code = Some(code);
		self
	}

	fn canonicalize_nans(mut self, canonicalize_nans: bool) -> Self {
		self.canonicalize_nans = canonicalize_nans;
		self
	}

	fn deterministic_stack(mut self, deterministic_stack: bool) -> Self {
		self.deterministic_stack = deterministic_stack;
		self
	}

	fn precompile_runtime(mut self, precompile_runtime: bool) -> Self {
		self.precompile_runtime = precompile_runtime;
		self
	}

	fn heap_alloc_strategy(mut self, heap_pages: HeapAllocStrategy) -> Self {
		self.heap_pages = heap_pages;
		self
	}

	fn build(&mut self) -> impl WasmModule + '_ {
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
			allow_missing_func_imports: true,
			cache_path: None,
			semantics: crate::Semantics {
				instantiation_strategy: self.instantiation_strategy,
				deterministic_stack_limit: match self.deterministic_stack {
					true => Some(crate::DeterministicStackLimit {
						logical_max: 65536,
						native_stack_max: 256 * 1024 * 1024,
					}),
					false => None,
				},
				canonicalize_nans: self.canonicalize_nans,
				parallel_compilation: true,
				heap_alloc_strategy: self.heap_pages,
				wasm_multi_value: false,
				wasm_bulk_memory: false,
				wasm_reference_types: false,
				wasm_simd: false,
			},
		};

		if self.precompile_runtime {
			let dir = tempfile::tempdir().unwrap();
			let path = dir.path().join("runtime.bin");

			// Delay the removal of the temporary directory until we're dropped.
			self.tmpdir = Some(dir);

			let artifact = crate::prepare_runtime_artifact(blob, &config.semantics).unwrap();
			std::fs::write(&path, artifact).unwrap();
			unsafe { crate::create_runtime_from_artifact::<HostFunctions>(&path, config) }
		} else {
			crate::create_runtime::<HostFunctions>(blob, config)
		}
		.expect("cannot create runtime")
	}
}

fn deep_call_stack_wat(depth: usize) -> String {
	format!(
		r#"
			(module
			  (memory $0 32)
			  (export "memory" (memory $0))
			  (global (export "__heap_base") i32 (i32.const 0))
			  (func (export "overflow") call 0)

			  (func $overflow (param $0 i32)
			    (block $label$1
			      (br_if $label$1
			        (i32.ge_u
			          (local.get $0)
			          (i32.const {depth})
			        )
			      )
			      (call $overflow
			        (i32.add
			          (local.get $0)
			          (i32.const 1)
			        )
			      )
			    )
			  )

			  (func (export "main")
			    (param i32 i32) (result i64)
			    (call $overflow (i32.const 0))
			    (i64.const 0)
			  )
			)
		"#
	)
}

// These two tests ensure that the `wasmtime`'s stack size limit and the amount of
// stack space used by a single stack frame doesn't suddenly change without us noticing.
//
// If they do (e.g. because we've pulled in a new version of `wasmtime`) we want to know
// that it did, regardless of how small the change was.
//
// If these tests starting failing it doesn't necessarily mean that something is broken;
// what it means is that one (or multiple) of the following has to be done:
//   a) the tests may need to be updated for the new call depth,
//   b) the stack limit may need to be changed to maintain backwards compatibility,
//   c) the root cause of the new call depth limit determined, and potentially fixed,
//   d) the new call depth limit may need to be validated to ensure it doesn't prevent any
//      existing chain from syncing (if it was effectively decreased)

// We need two limits here since depending on whether the code is compiled in debug
// or in release mode the maximum call depth is slightly different.
const CALL_DEPTH_LOWER_LIMIT: usize = 65455;
const CALL_DEPTH_UPPER_LIMIT: usize = 65509;

test_wasm_execution!(test_consume_under_1mb_of_stack_does_not_trap);
fn test_consume_under_1mb_of_stack_does_not_trap(instantiation_strategy: InstantiationStrategy) {
	let wat = deep_call_stack_wat(CALL_DEPTH_LOWER_LIMIT);
	let mut builder = RuntimeBuilder::new(instantiation_strategy).use_wat(wat);
	let runtime = builder.build();
	let mut instance = runtime.new_instance().expect("failed to instantiate a runtime");
	instance.call_export("main", &[]).unwrap();
}

test_wasm_execution!(test_consume_over_1mb_of_stack_does_trap);
fn test_consume_over_1mb_of_stack_does_trap(instantiation_strategy: InstantiationStrategy) {
	let wat = deep_call_stack_wat(CALL_DEPTH_UPPER_LIMIT + 1);
	let mut builder = RuntimeBuilder::new(instantiation_strategy).use_wat(wat);
	let runtime = builder.build();
	let mut instance = runtime.new_instance().expect("failed to instantiate a runtime");
	match instance.call_export("main", &[]).unwrap_err() {
		Error::AbortedDueToTrap(error) => {
			let expected = "wasm trap: call stack exhausted";
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(test_nan_canonicalization);
fn test_nan_canonicalization(instantiation_strategy: InstantiationStrategy) {
	let mut builder = RuntimeBuilder::new(instantiation_strategy).canonicalize_nans(true);
	let runtime = builder.build();

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

test_wasm_execution!(test_stack_depth_reaching);
fn test_stack_depth_reaching(instantiation_strategy: InstantiationStrategy) {
	const TEST_GUARD_PAGE_SKIP: &str = include_str!("test-guard-page-skip.wat");

	let mut builder = RuntimeBuilder::new(instantiation_strategy)
		.use_wat(TEST_GUARD_PAGE_SKIP.to_string())
		.deterministic_stack(true);

	let runtime = builder.build();
	let mut instance = runtime.new_instance().expect("failed to instantiate a runtime");

	match instance.call_export("test-many-locals", &[]).unwrap_err() {
		Error::AbortedDueToTrap(error) => {
			let expected = "wasm trap: wasm `unreachable` instruction executed";
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(test_max_memory_pages_imported_memory_without_precompilation);
fn test_max_memory_pages_imported_memory_without_precompilation(
	instantiation_strategy: InstantiationStrategy,
) {
	test_max_memory_pages(instantiation_strategy, true, false);
}

test_wasm_execution!(test_max_memory_pages_exported_memory_without_precompilation);
fn test_max_memory_pages_exported_memory_without_precompilation(
	instantiation_strategy: InstantiationStrategy,
) {
	test_max_memory_pages(instantiation_strategy, false, false);
}

test_wasm_execution!(@no_legacy_instance_reuse test_max_memory_pages_imported_memory_with_precompilation);
fn test_max_memory_pages_imported_memory_with_precompilation(
	instantiation_strategy: InstantiationStrategy,
) {
	test_max_memory_pages(instantiation_strategy, true, true);
}

test_wasm_execution!(@no_legacy_instance_reuse test_max_memory_pages_exported_memory_with_precompilation);
fn test_max_memory_pages_exported_memory_with_precompilation(
	instantiation_strategy: InstantiationStrategy,
) {
	test_max_memory_pages(instantiation_strategy, false, true);
}

fn test_max_memory_pages(
	instantiation_strategy: InstantiationStrategy,
	import_memory: bool,
	precompile_runtime: bool,
) {
	fn call(
		heap_alloc_strategy: HeapAllocStrategy,
		wat: String,
		instantiation_strategy: InstantiationStrategy,
		precompile_runtime: bool,
	) -> Result<(), Box<dyn std::error::Error>> {
		let mut builder = RuntimeBuilder::new(instantiation_strategy)
			.use_wat(wat)
			.heap_alloc_strategy(heap_alloc_strategy)
			.precompile_runtime(precompile_runtime);

		let runtime = builder.build();
		let mut instance = runtime.new_instance().unwrap();
		let _ = instance.call_export("main", &[])?;
		Ok(())
	}

	fn memory(initial: u32, maximum: u32, import: bool) -> String {
		let memory = format!("(memory $0 {} {})", initial, maximum);

		if import {
			format!("(import \"env\" \"memory\" {})", memory)
		} else {
			format!("{}\n(export \"memory\" (memory $0))", memory)
		}
	}

	let assert_grow_ok = |alloc_strategy: HeapAllocStrategy, initial_pages: u32, max_pages: u32| {
		eprintln!("assert_grow_ok({alloc_strategy:?}, {initial_pages}, {max_pages})");

		call(
			alloc_strategy,
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
				memory(initial_pages, max_pages, import_memory)
			),
			instantiation_strategy,
			precompile_runtime,
		)
		.unwrap()
	};

	let assert_grow_fail =
		|alloc_strategy: HeapAllocStrategy, initial_pages: u32, max_pages: u32| {
			eprintln!("assert_grow_fail({alloc_strategy:?}, {initial_pages}, {max_pages})");

			call(
				alloc_strategy,
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
					memory(initial_pages, max_pages, import_memory)
				),
				instantiation_strategy,
				precompile_runtime,
			)
			.unwrap()
		};

	assert_grow_ok(HeapAllocStrategy::Dynamic { maximum_pages: Some(10) }, 1, 10);
	assert_grow_ok(HeapAllocStrategy::Dynamic { maximum_pages: Some(10) }, 9, 10);
	assert_grow_fail(HeapAllocStrategy::Dynamic { maximum_pages: Some(10) }, 10, 10);

	assert_grow_ok(HeapAllocStrategy::Dynamic { maximum_pages: None }, 1, 10);
	assert_grow_ok(HeapAllocStrategy::Dynamic { maximum_pages: None }, 9, 10);
	assert_grow_ok(HeapAllocStrategy::Dynamic { maximum_pages: None }, 10, 10);

	assert_grow_fail(HeapAllocStrategy::Static { extra_pages: 10 }, 1, 10);
	assert_grow_fail(HeapAllocStrategy::Static { extra_pages: 10 }, 9, 10);
	assert_grow_fail(HeapAllocStrategy::Static { extra_pages: 10 }, 10, 10);
}

// This test takes quite a while to execute in a debug build (over 6 minutes on a TR 3970x)
// so it's ignored by default unless it was compiled with `--release`.
#[cfg_attr(build_type = "debug", ignore)]
#[test]
fn test_instances_without_reuse_are_not_leaked() {
	let runtime = crate::create_runtime::<HostFunctions>(
		RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
		crate::Config {
			allow_missing_func_imports: true,
			cache_path: None,
			semantics: crate::Semantics {
				instantiation_strategy: InstantiationStrategy::RecreateInstance,
				deterministic_stack_limit: None,
				canonicalize_nans: false,
				parallel_compilation: true,
				heap_alloc_strategy: DEFAULT_HEAP_ALLOC_STRATEGY,
				wasm_multi_value: false,
				wasm_bulk_memory: false,
				wasm_reference_types: false,
				wasm_simd: false,
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

#[test]
fn test_rustix_version_matches_with_wasmtime() {
	let metadata = cargo_metadata::MetadataCommand::new()
		.manifest_path("../../../Cargo.toml")
		.exec()
		.unwrap();

	let wasmtime_rustix = metadata
		.packages
		.iter()
		.find(|pkg| pkg.name == "wasmtime-runtime")
		.unwrap()
		.dependencies
		.iter()
		.find(|dep| dep.name == "rustix")
		.unwrap();
	let our_rustix = metadata
		.packages
		.iter()
		.find(|pkg| pkg.name == "sc-executor-wasmtime")
		.unwrap()
		.dependencies
		.iter()
		.find(|dep| dep.name == "rustix")
		.unwrap();

	if wasmtime_rustix.req != our_rustix.req {
		panic!(
			"our version of rustix ({0}) doesn't match wasmtime's ({1}); \
				bump the version in `sc-executor-wasmtime`'s `Cargo.toml' to '{1}' and try again",
			our_rustix.req, wasmtime_rustix.req,
		);
	}
}
