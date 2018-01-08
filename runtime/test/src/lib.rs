#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::vec::Vec;

#[macro_use]
extern crate runtime_support;
use runtime_support::{set_storage, storage, print};

pub fn code() -> Vec<u8> {
	storage(b"\0code")
}

pub fn set_code(new: &[u8]) {
	set_storage(b"\0code", new)
}

fn value_vec(mut value: usize, initial: Vec<u8>) -> Vec<u8> {
	let mut acc = initial;
	while value > 0 {
		acc.push(value as u8);
		value /= 256;
	}
	acc
}

pub fn set_authority(index: usize, authority: &[u8]) {
	set_storage(&value_vec(index, b"\0authority".to_vec()), authority);
}

pub fn authority(index: usize) -> Vec<u8> {
	storage(&value_vec(index, b"\0authority".to_vec()))
}

pub fn set_authority_count(count: usize) {
	(count..authority_count()).for_each(|i| set_authority(i, &[]));
	set_storage(b"\0authority_count", &value_vec(count, Vec::new()));
}

pub fn authority_count() -> usize {
	storage(b"\0authority_count").into_iter().rev().fold(0, |acc, i| (acc << 8) + (i as usize))
}

pub fn authorities() -> Vec<Vec<u8>> {
	(0..authority_count()).into_iter().map(authority).collect()
}

pub fn set_authorities(authorities: &[&[u8]]) {
	set_authority_count(authorities.len());
	authorities.iter().enumerate().for_each(|(v, i)| set_authority(v, i));
}

impl_stubs!(test_data_in);
fn test_data_in(input: Vec<u8>) -> Vec<u8> {
	print(b"set_storage" as &[u8]);
	set_storage(b"input", &input);

	print(b"code" as &[u8]);
	set_storage(b"code", &code());

	print(b"set_code" as &[u8]);
	set_code(&input);

	print(b"storage" as &[u8]);
	let copy = storage(b"input");

	print(b"authorities" as &[u8]);
	let mut v = authorities();
	v.push(copy);

	print(b"set_authorities" as &[u8]);
	set_authorities(&v.iter().map(Vec::as_slice).collect::<Vec<_>>());

	print(b"finished!" as &[u8]);
	b"all ok!".to_vec()
}
