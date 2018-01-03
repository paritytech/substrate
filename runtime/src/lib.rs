#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]

extern crate alloc;
use alloc::boxed::Box;

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
pub fn test_data_in(freeable_data: *mut u8, size: usize) {
	// Interpret data
	let slice = unsafe { core::slice::from_raw_parts(freeable_data, size) };
	let copy = slice.to_vec();

	unsafe { pwasm_libc::free(freeable_data); }

	let key = b"thekey";
	unsafe { set_storage(key as *const u8, key.len() as i32, &copy[0] as *const u8, copy.len() as i32); }

	// Do some stuff.
	for b in &copy {
		unsafe { imported(*b as u64); }
	}
}
