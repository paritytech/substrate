#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
extern crate alloc;
use alloc::boxed::Box;

extern crate pwasm_libc;
extern crate pwasm_alloc;

#[lang = "panic_fmt"]
fn panic_fmt() -> ! {
	  loop {}
}

extern "C" {
	fn imported(number: u64);
}

fn do_something(param: u64) -> u64 {
	param * 2
}

/// Test some execution.
#[no_mangle]
pub fn test(data_length: u64) -> u64 {
	unsafe { imported(data_length); }
	let b = Box::new(1);
	do_something(data_length)
}
