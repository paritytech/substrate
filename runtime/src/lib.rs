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
	fn imported(n: u64, m: u64);
}

fn do_something(param: u64) -> u64 {
	param * 2
}

/// Test some execution.
#[no_mangle]
pub fn test(data_length: u64) -> u64 {
	unsafe { imported(1, 2); }
	let b = Box::new(1);
	let c = Box::new(2);
	do_something(data_length)
}
