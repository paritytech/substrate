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

#[cfg(target_os = "linux")]
mod linux;

use assert_matches::assert_matches;
use codec::{Decode, Encode};
use sc_executor_common::{
	error::Error,
	runtime_blob::RuntimeBlob,
	wasm_runtime::{HeapAllocStrategy, WasmModule, DEFAULT_HEAP_ALLOC_STRATEGY},
};
use sc_runtime_test::wasm_binary_unwrap;
use sp_core::{
	blake2_128, blake2_256, ed25519, map,
	offchain::{testing, OffchainDbExt, OffchainWorkerExt},
	sr25519,
	traits::Externalities,
	Pair,
};
use sp_runtime::traits::BlakeTwo256;
use sp_state_machine::TestExternalities as CoreTestExternalities;
use sp_trie::{LayoutV1 as Layout, TrieConfiguration};
use std::sync::Arc;
use tracing_subscriber::layer::SubscriberExt;

use crate::WasmExecutionMethod;

pub type TestExternalities = CoreTestExternalities<BlakeTwo256>;
type HostFunctions = sp_io::SubstrateHostFunctions;

/// Simple macro that runs a given method as test with the available wasm execution methods.
#[macro_export]
macro_rules! test_wasm_execution {
	($method_name:ident) => {
		paste::item! {
			#[test]
			fn [<$method_name _interpreted>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Interpreted);
			}

			#[test]
			fn [<$method_name _compiled_recreate_instance_cow>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Compiled {
					instantiation_strategy: sc_executor_wasmtime::InstantiationStrategy::RecreateInstanceCopyOnWrite
				});
			}

			#[test]
			fn [<$method_name _compiled_recreate_instance_vanilla>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Compiled {
					instantiation_strategy: sc_executor_wasmtime::InstantiationStrategy::RecreateInstance
				});
			}

			#[test]
			fn [<$method_name _compiled_pooling_cow>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Compiled {
					instantiation_strategy: sc_executor_wasmtime::InstantiationStrategy::PoolingCopyOnWrite
				});
			}

			#[test]
			fn [<$method_name _compiled_pooling_vanilla>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Compiled {
					instantiation_strategy: sc_executor_wasmtime::InstantiationStrategy::Pooling
				});
			}

			#[test]
			fn [<$method_name _compiled_legacy_instance_reuse>]() {
				let _ = sp_tracing::try_init_simple();
				$method_name(WasmExecutionMethod::Compiled {
					instantiation_strategy: sc_executor_wasmtime::InstantiationStrategy::LegacyInstanceReuse
				});
			}
		}
	};

	(interpreted_only $method_name:ident) => {
		paste::item! {
			#[test]
			fn [<$method_name _interpreted>]() {
				$method_name(WasmExecutionMethod::Interpreted);
			}
		}
	};
}

fn call_in_wasm<E: Externalities>(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut E,
) -> Result<Vec<u8>, Error> {
	let executor = crate::WasmExecutor::<HostFunctions>::builder()
		.with_execution_method(execution_method)
		.build();

	executor.uncached_call(
		RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
		ext,
		true,
		function,
		call_data,
	)
}

test_wasm_execution!(returning_should_work);
fn returning_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	let output = call_in_wasm("test_empty_return", &[], wasm_method, &mut ext).unwrap();
	assert_eq!(output, vec![0u8; 0]);
}

test_wasm_execution!(call_not_existing_function);
fn call_not_existing_function(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_calling_missing_external", &[], wasm_method, &mut ext).unwrap_err() {
		Error::AbortedDueToTrap(error) => {
			let expected = match wasm_method {
				WasmExecutionMethod::Interpreted => "Other: Function `missing_external` is only a stub. Calling a stub is not allowed.",
				WasmExecutionMethod::Compiled { .. } => "call to a missing function env:missing_external"
			};
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(call_yet_another_not_existing_function);
fn call_yet_another_not_existing_function(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_calling_yet_another_missing_external", &[], wasm_method, &mut ext)
		.unwrap_err()
	{
		Error::AbortedDueToTrap(error) => {
			let expected = match wasm_method {
				WasmExecutionMethod::Interpreted => "Other: Function `yet_another_missing_external` is only a stub. Calling a stub is not allowed.",
				WasmExecutionMethod::Compiled { .. } => "call to a missing function env:yet_another_missing_external"
			};
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(panicking_should_work);
fn panicking_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	let output = call_in_wasm("test_panic", &[], wasm_method, &mut ext);
	assert!(output.is_err());

	let output = call_in_wasm("test_conditional_panic", &[0], wasm_method, &mut ext);
	assert_eq!(Decode::decode(&mut &output.unwrap()[..]), Ok(Vec::<u8>::new()));

	let output = call_in_wasm("test_conditional_panic", &vec![2].encode(), wasm_method, &mut ext);
	assert!(output.is_err());
}

test_wasm_execution!(storage_should_work);
fn storage_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	// Test value must be bigger than 32 bytes
	// to test the trie versioning.
	let value = vec![7u8; 60];

	{
		let mut ext = ext.ext();
		ext.set_storage(b"foo".to_vec(), b"bar".to_vec());

		let output = call_in_wasm("test_data_in", &value.encode(), wasm_method, &mut ext).unwrap();

		assert_eq!(output, b"all ok!".to_vec().encode());
	}

	let expected = TestExternalities::new(sp_core::storage::Storage {
		top: map![
			b"input".to_vec() => value,
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		],
		children_default: map![],
	});
	assert_eq!(ext, expected);
}

test_wasm_execution!(clear_prefix_should_work);
fn clear_prefix_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	{
		let mut ext = ext.ext();
		ext.set_storage(b"aaa".to_vec(), b"1".to_vec());
		ext.set_storage(b"aab".to_vec(), b"2".to_vec());
		ext.set_storage(b"aba".to_vec(), b"3".to_vec());
		ext.set_storage(b"abb".to_vec(), b"4".to_vec());
		ext.set_storage(b"bbb".to_vec(), b"5".to_vec());

		// This will clear all entries which prefix is "ab".
		let output =
			call_in_wasm("test_clear_prefix", &b"ab".to_vec().encode(), wasm_method, &mut ext)
				.unwrap();

		assert_eq!(output, b"all ok!".to_vec().encode());
	}

	let expected = TestExternalities::new(sp_core::storage::Storage {
		top: map![
			b"aaa".to_vec() => b"1".to_vec(),
			b"aab".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"5".to_vec()
		],
		children_default: map![],
	});
	assert_eq!(expected, ext);
}

test_wasm_execution!(blake2_256_should_work);
fn blake2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm("test_blake2_256", &[0], wasm_method, &mut ext,).unwrap(),
		blake2_256(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm("test_blake2_256", &b"Hello world!".to_vec().encode(), wasm_method, &mut ext,)
			.unwrap(),
		blake2_256(&b"Hello world!"[..]).to_vec().encode(),
	);
}

test_wasm_execution!(blake2_128_should_work);
fn blake2_128_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm("test_blake2_128", &[0], wasm_method, &mut ext,).unwrap(),
		blake2_128(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm("test_blake2_128", &b"Hello world!".to_vec().encode(), wasm_method, &mut ext,)
			.unwrap(),
		blake2_128(&b"Hello world!"[..]).to_vec().encode(),
	);
}

test_wasm_execution!(sha2_256_should_work);
fn sha2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm("test_sha2_256", &[0], wasm_method, &mut ext,).unwrap(),
		array_bytes::hex2bytes_unchecked(
			"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
		)
		.encode(),
	);
	assert_eq!(
		call_in_wasm("test_sha2_256", &b"Hello world!".to_vec().encode(), wasm_method, &mut ext,)
			.unwrap(),
		array_bytes::hex2bytes_unchecked(
			"c0535e4be2b79ffd93291305436bf889314e4a3faec05ecffcbb7df31ad9e51a"
		)
		.encode(),
	);
}

test_wasm_execution!(twox_256_should_work);
fn twox_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm("test_twox_256", &[0], wasm_method, &mut ext,).unwrap(),
		array_bytes::hex2bytes_unchecked(
			"99e9d85137db46ef4bbea33613baafd56f963c64b1f3685a4eb4abd67ff6203a"
		)
		.encode(),
	);
	assert_eq!(
		call_in_wasm("test_twox_256", &b"Hello world!".to_vec().encode(), wasm_method, &mut ext,)
			.unwrap(),
		array_bytes::hex2bytes_unchecked(
			"b27dfd7f223f177f2a13647b533599af0c07f68bda23d96d059da2b451a35a74"
		)
		.encode(),
	);
}

test_wasm_execution!(twox_128_should_work);
fn twox_128_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm("test_twox_128", &[0], wasm_method, &mut ext,).unwrap(),
		array_bytes::hex2bytes_unchecked("99e9d85137db46ef4bbea33613baafd5").encode(),
	);
	assert_eq!(
		call_in_wasm("test_twox_128", &b"Hello world!".to_vec().encode(), wasm_method, &mut ext,)
			.unwrap(),
		array_bytes::hex2bytes_unchecked("b27dfd7f223f177f2a13647b533599af").encode(),
	);
}

test_wasm_execution!(ed25519_verify_should_work);
fn ed25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let key = ed25519::Pair::from_seed(&blake2_256(b"test"));
	let sig = key.sign(b"all ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(sig.as_ref());

	assert_eq!(
		call_in_wasm("test_ed25519_verify", &calldata.encode(), wasm_method, &mut ext,).unwrap(),
		true.encode(),
	);

	let other_sig = key.sign(b"all is not ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(other_sig.as_ref());

	assert_eq!(
		call_in_wasm("test_ed25519_verify", &calldata.encode(), wasm_method, &mut ext,).unwrap(),
		false.encode(),
	);
}

test_wasm_execution!(sr25519_verify_should_work);
fn sr25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let key = sr25519::Pair::from_seed(&blake2_256(b"test"));
	let sig = key.sign(b"all ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(sig.as_ref());

	assert_eq!(
		call_in_wasm("test_sr25519_verify", &calldata.encode(), wasm_method, &mut ext,).unwrap(),
		true.encode(),
	);

	let other_sig = key.sign(b"all is not ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(other_sig.as_ref());

	assert_eq!(
		call_in_wasm("test_sr25519_verify", &calldata.encode(), wasm_method, &mut ext,).unwrap(),
		false.encode(),
	);
}

test_wasm_execution!(ordered_trie_root_should_work);
fn ordered_trie_root_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let trie_input = vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()];
	assert_eq!(
		call_in_wasm("test_ordered_trie_root", &[0], wasm_method, &mut ext.ext(),).unwrap(),
		Layout::<BlakeTwo256>::ordered_trie_root(trie_input.iter()).as_bytes().encode(),
	);
}

test_wasm_execution!(offchain_index);
fn offchain_index(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let (offchain, _state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainWorkerExt::new(offchain));
	call_in_wasm("test_offchain_index_set", &[0], wasm_method, &mut ext.ext()).unwrap();

	use sp_core::offchain::OffchainOverlayedChange;
	let data = ext
		.overlayed_changes()
		.clone()
		.offchain_drain_committed()
		.find(|(k, _v)| k == &(sp_core::offchain::STORAGE_PREFIX.to_vec(), b"k".to_vec()));
	assert_eq!(data.map(|data| data.1), Some(OffchainOverlayedChange::SetValue(b"v".to_vec())));
}

test_wasm_execution!(offchain_local_storage_should_work);
fn offchain_local_storage_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let (offchain, state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainDbExt::new(offchain.clone()));
	ext.register_extension(OffchainWorkerExt::new(offchain));
	assert_eq!(
		call_in_wasm("test_offchain_local_storage", &[0], wasm_method, &mut ext.ext(),).unwrap(),
		true.encode(),
	);
	assert_eq!(state.read().persistent_storage.get(b"test"), Some(vec![]));
}

test_wasm_execution!(offchain_http_should_work);
fn offchain_http_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let (offchain, state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainWorkerExt::new(offchain));
	state.write().expect_request(testing::PendingRequest {
		method: "POST".into(),
		uri: "http://localhost:12345".into(),
		body: vec![1, 2, 3, 4],
		headers: vec![("X-Auth".to_owned(), "test".to_owned())],
		sent: true,
		response: Some(vec![1, 2, 3]),
		response_headers: vec![("X-Auth".to_owned(), "hello".to_owned())],
		..Default::default()
	});

	assert_eq!(
		call_in_wasm("test_offchain_http", &[0], wasm_method, &mut ext.ext(),).unwrap(),
		true.encode(),
	);
}

test_wasm_execution!(should_trap_when_heap_exhausted);
fn should_trap_when_heap_exhausted(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();

	let executor = crate::WasmExecutor::<HostFunctions>::builder()
		.with_execution_method(wasm_method)
		// `17` is the initial number of pages compiled into the binary.
		.with_onchain_heap_alloc_strategy(HeapAllocStrategy::Static { extra_pages: 17 })
		.build();

	let err = executor
		.uncached_call(
			RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
			&mut ext.ext(),
			true,
			"test_allocate_vec",
			&16777216_u32.encode(),
		)
		.unwrap_err();

	match err {
		Error::AbortedDueToTrap(error)
			if matches!(wasm_method, WasmExecutionMethod::Compiled { .. }) =>
		{
			assert_eq!(
				error.message,
				r#"host code panicked while being called by the runtime: Failed to allocate memory: "Allocator ran out of space""#
			);
		},
		Error::RuntimePanicked(error) if wasm_method == WasmExecutionMethod::Interpreted => {
			assert_eq!(error, r#"Failed to allocate memory: "Allocator ran out of space""#);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

fn mk_test_runtime(
	wasm_method: WasmExecutionMethod,
	pages: HeapAllocStrategy,
) -> Arc<dyn WasmModule> {
	let blob = RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap())
		.expect("failed to create a runtime blob out of test runtime");

	crate::wasm_runtime::create_wasm_runtime_with_code::<HostFunctions>(
		wasm_method,
		pages,
		blob,
		true,
		None,
	)
	.expect("failed to instantiate wasm runtime")
}

test_wasm_execution!(returns_mutable_static);
fn returns_mutable_static(wasm_method: WasmExecutionMethod) {
	let runtime =
		mk_test_runtime(wasm_method, HeapAllocStrategy::Dynamic { maximum_pages: Some(1024) });

	let mut instance = runtime.new_instance().unwrap();
	let res = instance.call_export("returns_mutable_static", &[0]).unwrap();
	assert_eq!(33, u64::decode(&mut &res[..]).unwrap());

	// We expect that every invocation will need to return the initial
	// value plus one. If the value increases more than that then it is
	// a sign that the wasm runtime preserves the memory content.
	let res = instance.call_export("returns_mutable_static", &[0]).unwrap();
	assert_eq!(33, u64::decode(&mut &res[..]).unwrap());
}

test_wasm_execution!(returns_mutable_static_bss);
fn returns_mutable_static_bss(wasm_method: WasmExecutionMethod) {
	let runtime =
		mk_test_runtime(wasm_method, HeapAllocStrategy::Dynamic { maximum_pages: Some(1024) });

	let mut instance = runtime.new_instance().unwrap();
	let res = instance.call_export("returns_mutable_static_bss", &[0]).unwrap();
	assert_eq!(1, u64::decode(&mut &res[..]).unwrap());

	// We expect that every invocation will need to return the initial
	// value plus one. If the value increases more than that then it is
	// a sign that the wasm runtime preserves the memory content.
	let res = instance.call_export("returns_mutable_static_bss", &[0]).unwrap();
	assert_eq!(1, u64::decode(&mut &res[..]).unwrap());
}

// If we didn't restore the wasm instance properly, on a trap the stack pointer would not be
// returned to its initial value and thus the stack space is going to be leaked.
//
// See https://github.com/paritytech/substrate/issues/2967 for details
test_wasm_execution!(restoration_of_globals);
fn restoration_of_globals(wasm_method: WasmExecutionMethod) {
	// Allocate 32 pages (of 65536 bytes) which gives the runtime 2048KB of heap to operate on
	// (plus some additional space unused from the initial pages requested by the wasm runtime
	// module).
	//
	// The fixture performs 2 allocations of 768KB and this theoretically gives 1536KB, however, due
	// to our allocator algorithm there are inefficiencies.
	const REQUIRED_MEMORY_PAGES: u32 = 32;

	let runtime = mk_test_runtime(
		wasm_method,
		HeapAllocStrategy::Static { extra_pages: REQUIRED_MEMORY_PAGES },
	);
	let mut instance = runtime.new_instance().unwrap();

	// On the first invocation we allocate approx. 768KB (75%) of stack and then trap.
	let res = instance.call_export("allocates_huge_stack_array", &true.encode());
	assert!(res.is_err());

	// On the second invocation we allocate yet another 768KB (75%) of stack
	let res = instance.call_export("allocates_huge_stack_array", &false.encode());
	assert!(res.is_ok());
}

test_wasm_execution!(interpreted_only heap_is_reset_between_calls);
fn heap_is_reset_between_calls(wasm_method: WasmExecutionMethod) {
	let runtime = mk_test_runtime(wasm_method, DEFAULT_HEAP_ALLOC_STRATEGY);
	let mut instance = runtime.new_instance().unwrap();

	let heap_base = instance
		.get_global_const("__heap_base")
		.expect("`__heap_base` is valid")
		.expect("`__heap_base` exists")
		.as_i32()
		.expect("`__heap_base` is an `i32`");

	let params = (heap_base as u32, 512u32 * 64 * 1024).encode();
	instance.call_export("check_and_set_in_heap", &params).unwrap();

	// Cal it a second time to check that the heap was freed.
	instance.call_export("check_and_set_in_heap", &params).unwrap();
}

test_wasm_execution!(parallel_execution);
fn parallel_execution(wasm_method: WasmExecutionMethod) {
	let executor = Arc::new(
		crate::WasmExecutor::<HostFunctions>::builder()
			.with_execution_method(wasm_method)
			.build(),
	);
	let threads: Vec<_> = (0..8)
		.map(|_| {
			let executor = executor.clone();
			std::thread::spawn(move || {
				let mut ext = TestExternalities::default();
				let mut ext = ext.ext();
				assert_eq!(
					executor
						.uncached_call(
							RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
							&mut ext,
							true,
							"test_twox_128",
							&[0],
						)
						.unwrap(),
					array_bytes::hex2bytes_unchecked("99e9d85137db46ef4bbea33613baafd5").encode()
				);
			})
		})
		.collect();

	for t in threads.into_iter() {
		t.join().unwrap();
	}
}

test_wasm_execution!(wasm_tracing_should_work);
fn wasm_tracing_should_work(wasm_method: WasmExecutionMethod) {
	use sc_tracing::{SpanDatum, TraceEvent};
	use std::sync::Mutex;

	struct TestTraceHandler(Arc<Mutex<Vec<SpanDatum>>>);

	impl sc_tracing::TraceHandler for TestTraceHandler {
		fn handle_span(&self, sd: &SpanDatum) {
			self.0.lock().unwrap().push(sd.clone());
		}

		fn handle_event(&self, _event: &TraceEvent) {}
	}

	let traces = Arc::new(Mutex::new(Vec::new()));
	let handler = TestTraceHandler(traces.clone());

	// Create subscriber with wasm_tracing disabled
	let test_subscriber = tracing_subscriber::fmt()
		.finish()
		.with(sc_tracing::ProfilingLayer::new_with_handler(Box::new(handler), "default"));

	let _guard = tracing::subscriber::set_default(test_subscriber);

	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	let span_id =
		call_in_wasm("test_enter_span", Default::default(), wasm_method, &mut ext).unwrap();

	let span_id = u64::decode(&mut &span_id[..]).unwrap();

	assert!(span_id > 0);

	call_in_wasm("test_exit_span", &span_id.encode(), wasm_method, &mut ext).unwrap();

	// Check there is only the single trace
	let len = traces.lock().unwrap().len();
	assert_eq!(len, 1);

	let span_datum = traces.lock().unwrap().pop().unwrap();
	let values = span_datum.values;
	assert_eq!(span_datum.target, "default");
	assert_eq!(span_datum.name, "");
	assert_eq!(values.bool_values.get("wasm").unwrap(), &true);

	call_in_wasm("test_nested_spans", Default::default(), wasm_method, &mut ext).unwrap();
	let len = traces.lock().unwrap().len();
	assert_eq!(len, 2);
}

test_wasm_execution!(allocate_two_gigabyte);
fn allocate_two_gigabyte(wasm_method: WasmExecutionMethod) {
	let runtime = mk_test_runtime(wasm_method, HeapAllocStrategy::Dynamic { maximum_pages: None });

	let mut instance = runtime.new_instance().unwrap();
	let res = instance.call_export("allocate_two_gigabyte", &[0]).unwrap();
	assert_eq!(10 * 1024 * 1024 * 205, u32::decode(&mut &res[..]).unwrap());
}

test_wasm_execution!(memory_is_cleared_between_invocations);
fn memory_is_cleared_between_invocations(wasm_method: WasmExecutionMethod) {
	// This is based on the code generated by compiling a runtime *without*
	// the `-C link-arg=--import-memory` using the following code and then
	// disassembling the resulting blob with `wasm-dis`:
	//
	// ```
	// #[no_mangle]
	// #[cfg(not(feature = "std"))]
	// pub fn returns_no_bss_mutable_static(_: *mut u8, _: usize) -> u64 {
	//     static mut COUNTER: usize = 0;
	//     let output = unsafe {
	//        COUNTER += 1;
	//        COUNTER as u64
	//     };
	//     sp_core::to_substrate_wasm_fn_return_value(&output)
	// }
	// ```
	//
	// This results in the BSS section to *not* be emitted, hence the executor has no way
	// of knowing about the `static` variable's existence, so this test will fail if the linear
	// memory is not properly cleared between invocations.
	let binary = wat::parse_str(r#"
	(module
	 (type $i32_=>_i32 (func (param i32) (result i32)))
	 (type $i32_i32_=>_i64 (func (param i32 i32) (result i64)))
	 (import "env" "ext_allocator_malloc_version_1" (func $ext_allocator_malloc_version_1 (param i32) (result i32)))
	 (global $__stack_pointer (mut i32) (i32.const 1048576))
	 (global $global$1 i32 (i32.const 1048580))
	 (global $global$2 i32 (i32.const 1048592))
	 (memory $0 17)
	 (export "memory" (memory $0))
	 (export "returns_no_bss_mutable_static" (func $returns_no_bss_mutable_static))
	 (export "__data_end" (global $global$1))
	 (export "__heap_base" (global $global$2))
	 (func $returns_no_bss_mutable_static (param $0 i32) (param $1 i32) (result i64)
	  (local $2 i32)
	  (local $3 i32)
	  (i32.store offset=1048576
	   (i32.const 0)
	   (local.tee $2
	    (i32.add
	     (i32.load offset=1048576 (i32.const 0))
	     (i32.const 1)
	    )
	   )
	  )
	  (i64.store
	   (local.tee $3
	    (call $ext_allocator_malloc_version_1 (i32.const 8))
	   )
	   (i64.extend_i32_u (local.get $2))
	  )
	  (i64.or
	   (i64.extend_i32_u (local.get $3))
	   (i64.const 34359738368)
	  )
	 )
	)"#).unwrap();

	let runtime = crate::wasm_runtime::create_wasm_runtime_with_code::<HostFunctions>(
		wasm_method,
		HeapAllocStrategy::Dynamic { maximum_pages: Some(1024) },
		RuntimeBlob::uncompress_if_needed(&binary[..]).unwrap(),
		true,
		None,
	)
	.unwrap();

	let mut instance = runtime.new_instance().unwrap();
	let res = instance.call_export("returns_no_bss_mutable_static", &[0]).unwrap();
	assert_eq!(1, u64::decode(&mut &res[..]).unwrap());

	let res = instance.call_export("returns_no_bss_mutable_static", &[0]).unwrap();
	assert_eq!(1, u64::decode(&mut &res[..]).unwrap());
}

test_wasm_execution!(return_i8);
fn return_i8(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	assert_eq!(
		call_in_wasm("test_return_i8", &[], wasm_method, &mut ext).unwrap(),
		(-66_i8).encode()
	);
}

test_wasm_execution!(take_i8);
fn take_i8(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	call_in_wasm("test_take_i8", &(-66_i8).encode(), wasm_method, &mut ext).unwrap();
}

test_wasm_execution!(abort_on_panic);
fn abort_on_panic(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_abort_on_panic", &[], wasm_method, &mut ext).unwrap_err() {
		Error::AbortedDueToPanic(error) => assert_eq!(error.message, "test_abort_on_panic called"),
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(unreachable_intrinsic);
fn unreachable_intrinsic(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_unreachable_intrinsic", &[], wasm_method, &mut ext).unwrap_err() {
		Error::AbortedDueToTrap(error) => {
			let expected = match wasm_method {
				WasmExecutionMethod::Interpreted => "unreachable",
				WasmExecutionMethod::Compiled { .. } =>
					"wasm trap: wasm `unreachable` instruction executed",
			};
			assert_eq!(error.message, expected);
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(return_value);
fn return_value(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	assert_eq!(
		call_in_wasm("test_return_value", &[], wasm_method, &mut ext).unwrap(),
		(1234u64).encode()
	);
}

test_wasm_execution!(return_huge_len);
fn return_huge_len(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_return_huge_len", &[], wasm_method, &mut ext).unwrap_err() {
		Error::Runtime => {
			assert_matches!(wasm_method, WasmExecutionMethod::Interpreted);
		},
		Error::OutputExceedsBounds => {
			assert_matches!(wasm_method, WasmExecutionMethod::Compiled { .. });
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(return_max_memory_offset);
fn return_max_memory_offset(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	assert_eq!(
		call_in_wasm("test_return_max_memory_offset", &[], wasm_method, &mut ext).unwrap(),
		(u8::MAX).encode()
	);
}

test_wasm_execution!(return_max_memory_offset_plus_one);
fn return_max_memory_offset_plus_one(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_return_max_memory_offset_plus_one", &[], wasm_method, &mut ext)
		.unwrap_err()
	{
		Error::Runtime => {
			assert_matches!(wasm_method, WasmExecutionMethod::Interpreted);
		},
		Error::OutputExceedsBounds => {
			assert_matches!(wasm_method, WasmExecutionMethod::Compiled { .. });
		},
		error => panic!("unexpected error: {:?}", error),
	}
}

test_wasm_execution!(return_overflow);
fn return_overflow(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm("test_return_overflow", &[], wasm_method, &mut ext).unwrap_err() {
		Error::Runtime => {
			assert_matches!(wasm_method, WasmExecutionMethod::Interpreted);
		},
		Error::OutputExceedsBounds => {
			assert_matches!(wasm_method, WasmExecutionMethod::Compiled { .. });
		},
		error => panic!("unexpected error: {:?}", error),
	}
}
