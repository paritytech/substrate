#![no_std]
#![feature(lang_items)]

#[lang = "panic_fmt"]
fn panic_fmt() -> ! {
	  loop {}
}

#[no_mangle]
pub fn main(data_length: u64) -> u64 {
	do_something(data_length)
}

fn do_something(param: u64) -> u64 {
	param * 2
}
