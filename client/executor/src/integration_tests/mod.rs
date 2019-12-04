// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use primitives::{
	Blake2Hasher, blake2_128, blake2_256, ed25519, sr25519, map, Pair,
	offchain::{OffchainExt, testing},
	traits::Externalities,
};
use runtime_test::WASM_BINARY;
use state_machine::TestExternalities as CoreTestExternalities;
use test_case::test_case;
use trie::{TrieConfiguration, trie_types::Layout};

use crate::WasmExecutionMethod;

pub type TestExternalities = CoreTestExternalities<Blake2Hasher, u64>;

fn call_in_wasm<E: Externalities>(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut E,
	code: &[u8],
	heap_pages: u64,
) -> crate::error::Result<Vec<u8>> {
	crate::call_in_wasm::<E, runtime_io::SubstrateHostFunctions>(
		function,
		call_data,
		execution_method,
		ext,
		code,
		heap_pages,
	)
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn returning_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;

	let output = call_in_wasm(
		"test_empty_return",
		&[],
		wasm_method,
		&mut ext,
		&test_code[..],
		8,
	).unwrap();
	assert_eq!(output, vec![0u8; 0]);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn panicking_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;

	let output = call_in_wasm(
		"test_panic",
		&[],
		wasm_method,
		&mut ext,
		&test_code[..],
		8,
	);
	assert!(output.is_err());

	let output = call_in_wasm(
		"test_conditional_panic",
		&[0],
		wasm_method,
		&mut ext,
		&test_code[..],
		8,
	);
	assert_eq!(Decode::decode(&mut &output.unwrap()[..]), Ok(Vec::<u8>::new()));

	let output = call_in_wasm(
		"test_conditional_panic",
		&vec![2].encode(),
		wasm_method,
		&mut ext,
		&test_code[..],
		8,
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
		let test_code = WASM_BINARY;

		let output = call_in_wasm(
			"test_data_in",
			&b"Hello world".to_vec().encode(),
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap();

		assert_eq!(output, b"all ok!".to_vec().encode());
	}

	let expected = TestExternalities::new((map![
			b"input".to_vec() => b"Hello world".to_vec(),
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		], map![]));
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
		let test_code = WASM_BINARY;

		// This will clear all entries which prefix is "ab".
		let output = call_in_wasm(
			"test_clear_prefix",
			&b"ab".to_vec().encode(),
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap();

		assert_eq!(output, b"all ok!".to_vec().encode());
	}

	let expected = TestExternalities::new((map![
			b"aaa".to_vec() => b"1".to_vec(),
			b"aab".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"5".to_vec()
		], map![]));
	assert_eq!(expected, ext);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn blake2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_blake2_256",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		blake2_256(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_blake2_256",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		blake2_256(&b"Hello world!"[..]).to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn blake2_128_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_blake2_128",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		blake2_128(&b""[..]).to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_blake2_128",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		blake2_128(&b"Hello world!"[..]).to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn sha2_256_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_sha2_256",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
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
			&test_code[..],
			8,
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
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_twox_256",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
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
			&test_code[..],
			8,
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
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_twox_128",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		hex!("99e9d85137db46ef4bbea33613baafd5").to_vec().encode(),
	);
	assert_eq!(
		call_in_wasm(
			"test_twox_128",
			&b"Hello world!".to_vec().encode(),
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		hex!("b27dfd7f223f177f2a13647b533599af").to_vec().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn ed25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;
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
			&test_code[..],
			8,
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
			&test_code[..],
			8,
		).unwrap(),
		false.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn sr25519_verify_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let test_code = WASM_BINARY;
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
			&test_code[..],
			8,
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
			&test_code[..],
			8,
		).unwrap(),
		false.encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn ordered_trie_root_should_work(wasm_method: WasmExecutionMethod) {
	let mut ext = TestExternalities::default();
	let mut ext = ext.ext();
	let trie_input = vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()];
	let test_code = WASM_BINARY;
	assert_eq!(
		call_in_wasm(
			"test_ordered_trie_root",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		Layout::<Blake2Hasher>::ordered_trie_root(trie_input.iter()).as_bytes().encode(),
	);
}

#[test_case(WasmExecutionMethod::Interpreted)]
#[cfg_attr(feature = "wasmtime", test_case(WasmExecutionMethod::Compiled))]
fn offchain_local_storage_should_work(wasm_method: WasmExecutionMethod) {
	use primitives::offchain::OffchainStorage;

	let mut ext = TestExternalities::default();
	let (offchain, state) = testing::TestOffchainExt::new();
	ext.register_extension(OffchainExt::new(offchain));
	let test_code = WASM_BINARY;
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_offchain_local_storage",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
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

	let test_code = WASM_BINARY;
	let mut ext = ext.ext();
	assert_eq!(
		call_in_wasm(
			"test_offchain_http",
			&[0],
			wasm_method,
			&mut ext,
			&test_code[..],
			8,
		).unwrap(),
		true.encode(),
	);
}

