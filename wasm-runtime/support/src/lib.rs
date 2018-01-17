#![no_std]
#![feature(lang_items)]
#![feature(alloc)]
#![cfg_attr(feature = "strict", deny(warnings))]

#![feature(alloc)]
//#[macro_use]
extern crate alloc;
pub use alloc::vec::Vec;
pub use alloc::boxed::Box;
pub use alloc::rc::Rc;
pub use core::mem::{transmute, size_of, uninitialized, swap};
pub use core::slice;
pub use core::cell::{RefCell, Ref, RefMut};

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
	fn ext_chain_id() -> u64;
	fn ext_keccak256(data: *const u8, len: u32, out: *mut u8);
}

pub fn storage(key: &[u8]) -> Vec<u8> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_get_allocated_storage(&key[0], key.len() as u32, &mut length);
		Vec::from_raw_parts(ptr, length as usize, length as usize)
	}
}

pub fn storage_into<T: Sized>(key: &[u8]) -> Option<T> {
	let mut result: T;
	let size = size_of::<T>();
	let written;
	unsafe {
		result = uninitialized();
		let result_as_byte_blob = transmute::<*mut T, *mut u8>(&mut result);
		written = ext_get_storage_into(&key[0], key.len() as u32, result_as_byte_blob, size as u32) as usize;
	}
	// Only return a fully written value.
	if written == size {
		Some(result)
	} else {
		None
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

pub fn read_storage(key: &[u8], value_out: &mut [u8]) -> usize {
	unsafe {
		ext_get_storage_into(&key[0], key.len() as u32, &mut value_out[0], value_out.len() as u32) as usize
	}
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	unsafe {
		ext_chain_id()
	}
}

/// Conduct a keccak256 hash.
pub fn keccak256(data: &[u8]) -> [u8; 32] {
	unsafe {
		let mut result: [u8; 32] = uninitialized();
		// guaranteed to write into result.
		ext_keccak256(&data[0], data.len() as u32, &mut result[0]);
		result
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
macro_rules! impl_stubs {
	( $( $name:ident ),* ) => {
		pub mod _internal {
			$(
				#[no_mangle]
				pub fn $name(input_data: *mut u8, input_len: usize) -> u64 {
					let input = unsafe {
						$crate::Vec::from_raw_parts(input_data, input_len, input_len)
					};

					let output = super::$name(input);
					&output[0] as *const u8 as u64 + ((output.len() as u64) << 32)
				}
			)*
		}
	}
}
