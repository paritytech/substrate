#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate runtime_support;
use runtime_support::{set_storage, storage, print, keccak256};

fn test_keccak256(input: Vec<u8>) -> Vec<u8> {
	keccak256(&input).to_vec()
}

fn test_data_in(input: Vec<u8>) -> Vec<u8> {
	print(b"set_storage" as &[u8]);
	set_storage(b"input", &input);

	print(b"storage" as &[u8]);
	let foo = storage(b"foo");

	print(b"set_storage" as &[u8]);
	set_storage(b"baz", &foo);

	print(b"finished!" as &[u8]);
	b"all ok!".to_vec()
}


impl_stubs!(test_data_in, test_keccak256);
