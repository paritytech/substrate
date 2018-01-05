#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]

extern crate alloc;
use alloc::boxed::Box;
use alloc::vec::Vec;

extern crate pwasm_libc;
extern crate pwasm_alloc;

#[lang = "panic_fmt"]
#[no_mangle]
pub fn panic_fmt() -> ! {
	  loop {}
}

extern "C" {
	fn imported(n: u64) -> u64;
	fn set_storage(key_data: *const u8, key_len: i32, value_data: *const u8, value_len: i32);
	fn get_allocated_storage(key_data: *const u8, key_len: i32, written_out: *mut i32) -> *mut u8;
	fn set_code(code_data: *const u8, code_len: i32);
	fn get_allocated_code(written_out: *mut i32) -> *mut u8;
}

mod state {
	use alloc::vec::Vec;
	use super::{get_allocated_storage, set_storage as super_set_storage, get_allocated_code,
		set_code as super_set_code};

	pub fn storage(key: &[u8]) -> Vec<u8> {
		let mut length: i32 = 0;
		unsafe {
			let ptr = get_allocated_storage(&key[0], key.len() as i32, &mut length);
			Vec::from_raw_parts(ptr, length as usize, length as usize)
		}
	}

	pub fn set_storage(key: &[u8], value: &[u8]) {
		unsafe { super_set_storage(&key[0] as *const u8, key.len() as i32, &value[0] as *const u8, value.len() as i32); }
	}

	pub fn code() -> Vec<u8> {
		let mut length: i32 = 0;
		unsafe {
			let ptr = get_allocated_code(&mut length);
			Vec::from_raw_parts(ptr, length as usize, length as usize)
		}
	}

	pub fn set_code(new: &[u8]) {
		unsafe { super_set_code(&new[0] as *const u8, new.len() as i32); }
	}
}

fn do_something(param: u64) -> u64 {
	param * 2
}

/// Test some execution.
#[no_mangle]
pub fn test(value: u64) -> u64 {
	let b = Box::new(unsafe { imported(value) });
	do_something(*b)
}

/// Test passing of data.
#[no_mangle]
pub fn test_data_in(input_data: *mut u8, input_len: usize) {
	let input = unsafe { Vec::from_raw_parts(input_data, input_len, input_len) };

	state::set_storage(b"input", &input);
	state::set_storage(b"code", &state::code());

	state::set_code(&input);
	let copy = state::storage(b"input");

	// Do some stuff.
	for b in &copy {
		unsafe { imported(*b as u64); }
	}
}
