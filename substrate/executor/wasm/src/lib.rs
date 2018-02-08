#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate substrate_runtime_io as runtime_io;
use runtime_io::{
	set_storage, storage, print, blake2_256,
	twox_128, twox_256, ed25519_verify, enumerated_trie_root
};

impl_stubs!(
	test_data_in NO_DECODE => |input| {
		print("set_storage");
		set_storage(b"input", input);

		print("storage");
		let foo = storage(b"foo");

		print("set_storage");
		set_storage(b"baz", &foo);

		print("finished!");
		b"all ok!".to_vec()
	},
	test_empty_return NO_DECODE => |_| Vec::new(),
	test_panic NO_DECODE => |_| panic!("test panic"),
	test_conditional_panic NO_DECODE => |input: &[u8]| {
		if input.len() > 0 {
			panic!("test panic")
		}
		input.to_vec()
	},
	test_blake2_256 NO_DECODE => |input| blake2_256(input).to_vec(),
	test_twox_256 NO_DECODE => |input| twox_256(input).to_vec(),
	test_twox_128 NO_DECODE => |input| twox_128(input).to_vec(),
	test_ed25519_verify NO_DECODE => |input: &[u8]| {
		let mut pubkey = [0; 32];
		let mut sig = [0; 64];

		pubkey.copy_from_slice(&input[0..32]);
		sig.copy_from_slice(&input[32..96]);

		let msg = b"all ok!";
		[ed25519_verify(&sig, &msg[..], &pubkey) as u8].to_vec()
	},
	test_enumerated_trie_root NO_DECODE => |_| {
		enumerated_trie_root(&[&b"zero"[..], &b"one"[..], &b"two"[..]]).to_vec()
	}
);
