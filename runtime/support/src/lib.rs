#![no_std]
#![feature(lang_items)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]

extern crate alloc;
use alloc::vec::Vec;

extern crate pwasm_libc;
extern crate pwasm_alloc;

#[lang = "panic_fmt"]
#[no_mangle]
pub fn panic_fmt() -> ! {
	  loop {}
}

extern "C" {
	fn ext_print(utf8_data: *const u8, utf8_len: u32);
	fn ext_print_num(value: u64);
	fn ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32);
	fn ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8;
	fn ext_get_storage_into(key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32) -> u32;
	fn ext_deposit_log(log_data: *const u8, log_len: u32);
}

pub fn storage(key: &[u8]) -> Vec<u8> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_get_allocated_storage(&key[0], key.len() as u32, &mut length);
		Vec::from_raw_parts(ptr, length as usize, length as usize)
	}
}

pub trait IsValue {
	const value: usize;
}

pub struct Value20; impl IsValue for Value20 { const value = 20usize; }
pub struct Value32; impl IsValue for Value32 { const value = 32usize; }
pub struct Value64; impl IsValue for Value64 { const value = 64usize; }
pub struct Value65; impl IsValue for Value65 { const value = 65usize; }

pub fn storage_into<T: IsValue>(key: &[u8]) -> Option<[u8; T::value]> {
	let mut result = [0u8; T::value];
	let written = unsafe {
		ext_get_storage_into(&key[0], key.len() as u32, &result[0], result.len())
	};
	match written {
		T::value => Some(result),
		_ => None,
	}
}

pub fn set_storage(key: &[u8], value: &[u8]) {
	unsafe {
		ext_set_storage(
			&key[0] as *const u8, key.len() as u32,
			&value[0] as *const u8, value.len() as u32
		);
	}
}

pub fn deposit_log(log: &[u8]) {
	unsafe {
		ext_deposit_log(
			&log[0] as *const u8, log.len() as u32,
		)
	}
}

pub trait Printable {
	fn print(self);
}

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		unsafe {
			ext_print(&self[0] as *const u8, self.len() as u32);
		}
	}
}

impl Printable for u64 {
	fn print(self) {
		unsafe { ext_print_num(self); }
	}
}

pub fn print<T: Printable + Sized>(value: T) {
	value.print();
}

#[macro_export]
macro_rules! impl_stub {
	($name:ident) => {
		pub mod _internal {
			#[no_mangle]
			pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
				let input = unsafe {
					super::alloc::vec::Vec::from_raw_parts(input_data, input_len, input_len)
				};

				let output = super::$name(input);
				&output[0] as *const u8 as u64 + ((output.len() as u64) << 32)
			}
		}
	}
}
