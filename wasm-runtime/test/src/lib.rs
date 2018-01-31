#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate polkadot_runtime_std as runtime_std;
use runtime_std::{
	set_storage, storage, print, blake2_256,
	twox_128, twox_256, ed25519_verify, enumerated_trie_root
};

fn test_blake2_256(input: &[u8]) -> Vec<u8> {
	blake2_256(&input).to_vec()
}

fn test_twox_256(input: &[u8]) -> Vec<u8> {
	twox_256(&input).to_vec()
}

fn test_twox_128(input: &[u8]) -> Vec<u8> {
	twox_128(&input).to_vec()
}

fn test_ed25519_verify(input: &[u8]) -> Vec<u8> {
	let sig = &input[0..64];
	let pubkey = &input[64..96];
	let msg = b"all ok!";
	[ed25519_verify(sig, &msg[..], pubkey) as u8].to_vec()
}

fn test_enumerated_trie_root(_input: &[u8]) -> Vec<u8> {
	enumerated_trie_root(&[&b"zero"[..], &b"one"[..], &b"two"[..]]).to_vec()
}

fn test_data_in(input: &[u8]) -> Vec<u8> {
	print("set_storage");
	set_storage(b"input", &input);

	print("storage");
	let foo = storage(b"foo");

	print("set_storage");
	set_storage(b"baz", &foo);

	print("finished!");
	b"all ok!".to_vec()
}

fn test_empty_return(_input: &[u8]) -> Vec<u8> {
	Vec::new()
}

fn test_panic(_input: &[u8]) -> Vec<u8> {
	panic!("test panic");
}

fn test_conditional_panic(input: &[u8]) -> Vec<u8> {
	if input.len() > 0 {
		panic!("test panic");
	}
	input.to_vec()
}

impl_stubs!(test_data_in, test_empty_return, test_panic, test_conditional_panic,
	test_blake2_256, test_twox_256, test_twox_128, test_ed25519_verify, test_enumerated_trie_root);
