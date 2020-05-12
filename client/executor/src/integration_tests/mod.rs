// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

mod sandbox;

use codec::{Encode, Decode};
use hex_literal::hex;
use sp_core::{
	blake2_128, blake2_256, ed25519, sr25519, map, Pair,
	offchain::{OffchainExt, testing},
	traits::{Externalities, CallInWasm},
};
use sc_runtime_test::WASM_BINARY;
use sp_state_machine::TestExternalities as CoreTestExternalities;
use test_case::test_case;
use sp_trie::{TrieConfiguration, trie_types::Layout};
use sp_wasm_interface::HostFunctions as _;
use sp_runtime::traits::BlakeTwo256;

use crate::WasmExecutionMethod;

pub type TestExternalities = CoreTestExternalities<BlakeTwo256, u64>;
type HostFunctions = sp_io::SubstrateHostFunctions;

fn call_in_wasm<E: Externalities>(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut E,
) -> Result<Vec<u8>, String> {
	let executor = crate::WasmExecutor::new(
		execution_method,
		Some(1024),
		HostFunctions::host_functions(),
		8,
	);
	executor.call_in_wasm(
		&WASM_BINARY[..],
		None,
		function,
		call_data,
		ext,
		sp_core::traits::MissingHostFunctions::Allow,
	)
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn returning_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	let output = call_in_wasm(
		"test_empty_return",
		&[],
		wasm_method,
		&mut ext,
	).unwrap();
	assert_eq!(output, vec![0u8; 0]);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn call_not_existing_function(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm(
		"test_calling_missing_external",
		&[],
		wasm_method,
		&mut ext,
	) {
		Ok(_) => panic!("was expected an `Err`"),
		Err(e) => {
			match wasm_method {
				WasmExecutionMethod::Interpreted => assert_eq!(
					&format!("{:?}", e),
					"\"Trap: Trap { kind: Host(Other(\\\"Function `missing_external` is only a stub. Calling a stub is not allowed.\\\")) }\""
				),
				#[cfg(feature = "wasmtime")]
				WasmExecutionMethod::Compiled => assert!(
					format!("{:?}", e).contains("Wasm execution trapped: call to a missing function env:missing_external")
				),
			}
		}
	}
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn call_yet_another_not_existing_function(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	match call_in_wasm(
		"test_calling_yet_another_missing_external",
		&[],
		wasm_method,
		&mut ext,
	) {
		Ok(_) => panic!("was expected an `Err`"),
		Err(e) => {
			match wasm_method {
				WasmExecutionMethod::Interpreted => assert_eq!(
					&format!("{:?}", e),
					"\"Trap: Trap { kind: Host(Other(\\\"Function `yet_another_missing_external` is only a stub. Calling a stub is not allowed.\\\")) }\""
				),
				#[cfg(feature = "wasmtime")]
				WasmExecutionMethod::Compiled => assert!(
					format!("{:?}", e).contains("Wasm execution trapped: call to a missing function env:yet_another_missing_external")
				),
			}
		}
	}
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn panicking_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();

	let output = call_in_wasm(
		"test_panic",
		&[],
		wasm_method,
		&mut ext,
	);
	assert!(output.is_err());

	let output = call_in_wasm(
		"test_conditional_panic",
		&[0],
		wasm_method,
		&mut ext,
	);
	assert_eq!(Decode::decode(&mut &output.unwrap()[..]), Ok(Vec::<u8>::new()));

	let output = call_in_wasm(
		"test_conditional_panic",
		&vec![2].encode(),
		wasm_method,
		&mut ext,
	);
	assert!(output.is_err());
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn storage_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();

	{
		let mut ext = ext.ext();
		ext.set_storage(b"foo".to_vec(), b"bar".to_vec());

		let output = call_in_wasm(
			"test_data_in",
			&b"Hello world".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap();

		assert_eq!(output, b"all ok!".to_vec().encode());
	}

	let expected = TestExternalities::new(sp_core::storage::Storage {
		top: map![
			b"input".to_vec() => b"Hello world".to_vec(),
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		],
		children_default: map![],
	});
	assert_eq!(ext, expected);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
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
		let output = call_in_wasm(
			"test_clear_prefix",
			&b"ab".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap();

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

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn blake2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_blake2_256",
			&[0],
			wasm_method,
			&mut ext,
		).unwrap(),
		blake2_256(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_blake2_256",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		blake2_256(&b"Hello world!"[..]).to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn blake2_128_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_blake2_128",
			&[0],
			wasm_method,
			&mut ext,
		).unwrap(),
		blake2_128(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_blake2_128",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		blake2_128(&b"Hello world!"[..]).to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn sha2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_sha2_256",
			&[0],
			wasm_method,
			&mut ext,
		)
		.unwrap(),
		hex!("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
			.to_vec()
			.encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_sha2_256",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
		)
		.unwrap(),
		hex!("c0535e4be2b79ffd93291305436bf889314e4a3faec05ecffcbb7df31ad9e51a")
			.to_vec()
			.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn twox_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_twox_256",
			&[0],
			wasm_method,
			&mut ext,
		).unwrap(),
		hex!(
				"99e9d85137db46ef4bbea33613baafd56f963c64b1f3685a4eb4abd67ff6203a"
			).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_twox_256",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		hex!(
				"b27dfd7f223f177f2a13647b533599af0c07f68bda23d96d059da2b451a35a74"
			).to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn twox_128_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_twox_128",
			&[0],
			wasm_method,
			&mut ext,
		).unwrap(),
		hex!("99e9d85137db46ef4bbea33613baafd5").to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_twox_128",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		hex!("b27dfd7f223f177f2a13647b533599af").to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn ed25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let key = ed25519::Pair::from_seed(&blake2_256(b"test"));
	let sig = key.sign(b"all ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(sig.as_ref());

	assert_eq!(
		call_in_wasm(
			"test_ed25519_verify",
			&calldata.encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		true.encode(),
	);

	let other_sig = key.sign(b"all is not ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(other_sig.as_ref());

	assert_eq!(
		call_in_wasm(
			"test_ed25519_verify",
			&calldata.encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		false.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn sr25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let key = sr25519::Pair::from_seed(&blake2_256(b"test"));
	let sig = key.sign(b"all ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(sig.as_ref());

	assert_eq!(
		call_in_wasm(
			"test_sr25519_verify",
			&calldata.encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		true.encode(),
	);

	let other_sig = key.sign(b"all is not ok!");
	let mut calldata = vec![];
	calldata.extend_from_slice(key.public().as_ref());
	calldata.extend_from_slice(other_sig.as_ref());

	assert_eq!(
		call_in_wasm(
			"test_sr25519_verify",
			&calldata.encode(),
			wasm_method,
			&mut ext,
		).unwrap(),
		false.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn ordered_trie_root_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let trie_input = vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()];
	assert_eq!(
		call_in_wasm(
			"test_ordered_trie_root",
			&[0],
			wasm_method,
			&mut ext.ext(),
		).unwrap(),
		Layout::<BlakeTwo256>::ordered_trie_root(trie_input.iter()).as_bytes().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn offchain_index(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let (offchain, _state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainExt::new(offchain));
	call_in_wasm(
		"test_offchain_index_set",
		&[0],
		wasm_method,
		&mut ext.ext(),
	).unwrap();

	use sp_core::offchain::storage::OffchainOverlayedChange;
	assert_eq!(
		ext.ext()
			.get_offchain_storage_changes()
			.get(sp_core::offchain::STORAGE_PREFIX, b"k"),
		Some(OffchainOverlayedChange::SetValue(b"v".to_vec()))
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn offchain_local_storage_should_work(wasm_method: WasmExecutionMethod) {
	use sp_core::offchain::OffchainStorage;

	let mut ext = TestExternalities::default();
	let (offchain, state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainExt::new(offchain));
	assert_eq!(
		call_in_wasm(
			"test_offchain_local_storage",
			&[0],
			wasm_method,
			&mut ext.ext(),
		).unwrap(),
		true.encode(),
	);
	assert_eq!(state.read().persistent_storage.get(b"", b"test"), Some(vec![]));
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn offchain_http_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let (offchain, state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainExt::new(offchain));
	state.write().expect_request(
		0,
		testing::PendingRequest {
			method: "POST".into(),
			uri: "http://localhost:12345".into(),
			body: vec![1, 2, 3, 4],
			headers: vec![("X-Auth".to_owned(), "test".to_owned())],
			sent: true,
			response: Some(vec![1, 2, 3]),
			response_headers: vec![("X-Auth".to_owned(), "hello".to_owned())],
			..Default::default()
		},
	);

	assert_eq!(
		call_in_wasm(
			"test_offchain_http",
			&[0],
			wasm_method,
			&mut ext.ext(),
		).unwrap(),
		true.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
#[should_panic(expected = "Allocator ran out of space")]
fn should_trap_when_heap_exhausted(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();

	let executor = crate::WasmExecutor::new(
		wasm_method,
		Some(17),  // `17` is the initial number of pages compiled into the binary.
		HostFunctions::host_functions(),
		8,
	);
	executor.call_in_wasm(
		&WASM_BINARY[..],
		None,
		"test_exhaust_heap",
		&[0],
		&mut ext.ext(),
		sp_core::traits::MissingHostFunctions::Allow,
	).unwrap();
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn returns_mutable_static(wasm_method: WasmExecutionMethod) {
	let runtime = crate::wasm_runtime::create_wasm_runtime_with_code(
		wasm_method,
		1024,
		&WASM_BINARY[..],
		HostFunctions::host_functions(),
		true,
	).expect("Creates runtime");

	let instance = runtime.new_instance().unwrap();
	let res = instance.call("returns_mutable_static", &[0]).unwrap();
	assert_eq!(33, u64::decode(&mut &res[..]).unwrap());

	// We expect that every invocation will need to return the initial
	// value plus one. If the value increases more than that then it is
	// a sign that the wasm runtime preserves the memory content.
	let res = instance.call("returns_mutable_static", &[0]).unwrap();
	assert_eq!(33, u64::decode(&mut &res[..]).unwrap());
}

// If we didn't restore the wasm instance properly, on a trap the stack pointer would not be
// returned to its initial value and thus the stack space is going to be leaked.
//
// See https://github.com/paritytech/substrate/issues/2967 for details
#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn restoration_of_globals(wasm_method: WasmExecutionMethod) {
	// Allocate 32 pages (of 65536 bytes) which gives the runtime 2048KB of heap to operate on
	// (plus some additional space unused from the initial pages requested by the wasm runtime
	// module).
	//
	// The fixture performs 2 allocations of 768KB and this theoretically gives 1536KB, however, due
	// to our allocator algorithm there are inefficiencies.
	const REQUIRED_MEMORY_PAGES: u64 = 32;

	let runtime = crate::wasm_runtime::create_wasm_runtime_with_code(
		wasm_method,
		REQUIRED_MEMORY_PAGES,
		&WASM_BINARY[..],
		HostFunctions::host_functions(),
		true,
	).expect("Creates runtime");
	let instance = runtime.new_instance().unwrap();

	// On the first invocation we allocate approx. 768KB (75%) of stack and then trap.
	let res = instance.call("allocates_huge_stack_array", &true.encode());
	assert!(res.is_err());

	// On the second invocation we allocate yet another 768KB (75%) of stack
	let res = instance.call("allocates_huge_stack_array", &false.encode());
	assert!(res.is_ok());
}

#[test_case(WasmExecutionMethod::Interpreted)]
fn heap_is_reset_between_calls(wasm_method: WasmExecutionMethod) {
	let runtime = crate::wasm_runtime::create_wasm_runtime_with_code(
		wasm_method,
		1024,
		&WASM_BINARY[..],
		HostFunctions::host_functions(),
		true,
	).expect("Creates runtime");
	let instance = runtime.new_instance().unwrap();

	let heap_base = instance.get_global_const("__heap_base")
		.expect("`__heap_base` is valid")
		.expect("`__heap_base` exists")
		.as_i32()
		.expect("`__heap_base` is an `i32`");

	let params = (heap_base as u32, 512u32 * 64 * 1024).encode();
	instance.call("check_and_set_in_heap", &params).unwrap();

	// Cal it a second time to check that the heap was freed.
	instance.call("check_and_set_in_heap", &params).unwrap();
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn parallel_execution(wasm_method: WasmExecutionMethod) {
	let threads: Vec<_> = (0..8).map(|_| std::thread::spawn(move || {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		assert_eq!(
			call_in_wasm(
				"test_twox_128",
				&[0],
				wasm_method.clone(),
				&mut ext,
			).unwrap(),
			hex!("99e9d85137db46ef4bbea33613baafd5").to_vec().encode(),
		);
	})).collect();

	for t in threads.into_iter() {
		t.join().unwrap();
	}
}
