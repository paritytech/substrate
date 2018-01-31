#[cfg(feature = "nightly")]
extern crate alloc;

#[cfg(feature = "nightly")]
extern crate pwasm_libc;
#[cfg(feature = "nightly")]
extern crate pwasm_alloc;

pub use alloc::vec;
pub use alloc::boxed;
pub use alloc::rc;
pub use core::mem;
pub use core::slice;
pub use core::cell;

use alloc::vec::Vec;

#[lang = "panic_fmt"]
#[no_mangle]
pub extern fn panic_fmt(_fmt: ::core::fmt::Arguments, _file: &'static str, _line: u32, _col: u32) {
	unsafe {
		ext_print_utf8(_file.as_ptr() as *const u8, _file.len() as u32);
		ext_print_num(_line as u64);
		ext_print_num(_col as u64);
		::core::intrinsics::abort()
	}
}

extern "C" {
	fn ext_print_utf8(utf8_data: *const u8, utf8_len: u32);
	fn ext_print_hex(data: *const u8, len: u32);
	fn ext_print_num(value: u64);
	fn ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32);
	fn ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8;
	fn ext_get_storage_into(key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32;
	fn ext_storage_root(result: *mut u8);
	fn ext_enumerated_trie_root(values_data: *const u8, values_len: u32, lens_data: *const u32, lens_len: u32, result: *mut u8);
	fn ext_chain_id() -> u64;
	fn ext_blake2_256(data: *const u8, len: u32, out: *mut u8);
	fn ext_twox_128(data: *const u8, len: u32, out: *mut u8);
	fn ext_twox_256(data: *const u8, len: u32, out: *mut u8);
	fn ext_ed25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32;
}

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Vec<u8> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_get_allocated_storage(key.as_ptr(), key.len() as u32, &mut length);
		Vec::from_raw_parts(ptr, length as usize, length as usize)
	}
}

/// Set the storage to some particular key.
pub fn set_storage(key: &[u8], value: &[u8]) {
	unsafe {
		ext_set_storage(
			key.as_ptr(), key.len() as u32,
			value.as_ptr(), value.len() as u32
		);
	}
}

/// Get `key` from storage, placing the value into `value_out` (as much as possible) and return
/// the number of bytes that the key in storage was.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> usize {
	unsafe {
		ext_get_storage_into(key.as_ptr(), key.len() as u32, value_out.as_mut_ptr(), value_out.len() as u32, value_offset as u32) as usize
	}
}

/// The current storage's root.
pub fn storage_root() -> [u8; 32] {
	let mut result: [u8; 32] = Default::default();
	unsafe {
		ext_storage_root(result.as_mut_ptr());
	}
	result
}

/// A trie root calculated from enumerated values.
pub fn enumerated_trie_root(values: &[&[u8]]) -> [u8; 32] {
	let lens = values.iter().map(|v| (v.len() as u32).to_le()).collect::<Vec<_>>();
	let values = values.iter().fold(Vec::new(), |mut acc, sl| { acc.extend_from_slice(sl); acc });
	let mut result: [u8; 32] = Default::default();
	unsafe {
		ext_enumerated_trie_root(
			values.as_ptr(), values.len() as u32,
			lens.as_ptr(), lens.len() as u32,
			result.as_mut_ptr()
		);
	}
	result
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	unsafe {
		ext_chain_id()
	}
}

/// Conduct a 256-bit Blake2 hash.
pub fn blake2_256(data: &[u8]) -> [u8; 32] {
	let mut result: [u8; 32] = Default::default();
	unsafe {
		ext_blake2_256(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
	}
	result
}

/// Conduct four XX hashes to give a 256-bit result.
pub fn twox_256(data: &[u8]) -> [u8; 32] {
	let mut result: [u8; 32] = Default::default();
	unsafe {
		ext_twox_256(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
	}
	result
}

/// Conduct two XX hashes to give a 128-bit result.
pub fn twox_128(data: &[u8]) -> [u8; 16] {
	let mut result: [u8; 16] = Default::default();
	unsafe {
		ext_twox_128(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
	}
	result
}

/// Verify a ed25519 signature.
pub fn ed25519_verify(sig: &[u8], msg: &[u8], pubkey: &[u8]) -> bool {
	sig.len() == 64 && pubkey.len() == 32 && unsafe {
		ext_ed25519_verify(msg.as_ptr(), msg.len() as u32, sig.as_ptr(), pubkey.as_ptr())
	} == 0
}

/// Trait for things which can be printed.
pub trait Printable {
	fn print(self);
}

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		unsafe {
			ext_print_hex(self.as_ptr(), self.len() as u32);
		}
	}
}

impl<'a> Printable for &'a str {
	fn print(self) {
		unsafe {
			ext_print_utf8(self.as_ptr() as *const u8, self.len() as u32);
		}
	}
}

impl Printable for u64 {
	fn print(self) {
		unsafe { ext_print_num(self); }
	}
}

/// Print a printable value.
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
					let input = if input_len == 0 {
						&[0u8; 0]
					} else {
						unsafe {
							$crate::slice::from_raw_parts(input_data, input_len)
						}
					};

					let output = super::$name(input);
					output.as_ptr() as u64 + ((output.len() as u64) << 32)
				}
			)*
		}
	}
}
