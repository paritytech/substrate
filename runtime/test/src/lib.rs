#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate runtime_support;
use runtime_support::{set_storage, code, set_code, storage, validators, set_validators, print};

impl_stub!(test_data_in);
fn test_data_in(input: Vec<u8>) -> Vec<u8> {
	print(b"set_storage" as &[u8]);
	set_storage(b"input", &input);

	print(b"code" as &[u8]);
	set_storage(b"code", &code());

	print(b"set_code" as &[u8]);
	set_code(&input);

	print(b"storage" as &[u8]);
	let copy = storage(b"input");

	print(b"validators" as &[u8]);
	let mut v = validators();
	v.push(copy);

	print(b"set_validators" as &[u8]);
	set_validators(&v.iter().map(Vec::as_slice).collect::<Vec<_>>());

	print(b"finished!" as &[u8]);
	b"all ok!".to_vec()
}
