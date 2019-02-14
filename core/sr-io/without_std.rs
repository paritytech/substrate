// Copyright 2017-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

#[doc(hidden)]
pub use parity_codec as codec;
#[doc(hidden)]
pub use rstd;
pub use rstd::{mem, slice};

use core::intrinsics;
use rstd::vec::Vec;
use hash_db::Hasher;
use primitives::Blake2Hasher;

#[panic_handler]
#[no_mangle]
pub fn panic(info: &::core::panic::PanicInfo) -> ! {
	unsafe {
		if let Some(loc) = info.location() {
			ext_print_utf8(loc.file().as_ptr() as *const u8, loc.file().len() as u32);
			ext_print_num(loc.line() as u64);
			ext_print_num(loc.column() as u64);
		}
		intrinsics::abort()
	}
}

#[alloc_error_handler]
pub extern fn oom(_: ::core::alloc::Layout) -> ! {
	static OOM_MSG: &str = "Runtime memory exhausted. Aborting";

	unsafe {
		ext_print_utf8(OOM_MSG.as_ptr(), OOM_MSG.len() as u32);
		intrinsics::abort();
	}
}

/// Host functions, provided by the executor.
/// A WebAssembly runtime module would "import" these to access the execution environment
/// (most importantly, storage) or perform heavy hash calculations.
/// See also "ext_" functions in sr-sandbox and sr-std
extern "C" {
	/// Printing, useful for debugging
	fn ext_print_utf8(utf8_data: *const u8, utf8_len: u32);
	fn ext_print_hex(data: *const u8, len: u32);
	fn ext_print_num(value: u64);

	/// Set value for key in storage.
	fn ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32);
	/// Remove key and value from storage.
	fn ext_clear_storage(key_data: *const u8, key_len: u32);
	/// Checks if the given key exists in the storage.
	///
	/// # Returns
	///
	/// - `1` if the value exists.
	/// - `0` if the value does not exists.
	fn ext_exists_storage(key_data: *const u8, key_len: u32) -> u32;
	/// Remove storage entries which key starts with given prefix.
	fn ext_clear_prefix(prefix_data: *const u8, prefix_len: u32);
	/// Gets the value of the given key from storage.
	///
	/// The host allocates the memory for storing the value.
	///
	/// # Returns
	///
	/// - `0` if no value exists to the given key. `written_out` is set to `u32::max_value()`.
	///
	/// - Otherwise, pointer to the value in memory. `written_out` contains the length of the value.
	fn ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8;
	/// Gets the value of the given key from storage.
	///
	/// The value is written into `value` starting at `value_offset`.
	///
	/// If the value length is greater than `value_len - value_offset`, the value is written partially.
	///
	/// # Returns
	///
	/// - `u32::max_value()` if the value does not exists.
	///
	/// - Otherwise, the number of bytes written for value.
	fn ext_get_storage_into(key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32;
	/// Gets the trie root of the storage.
	fn ext_storage_root(result: *mut u8);
	/// Get the change trie root of the current storage overlay at a block with given parent.
	///
	/// # Returns
	///
	/// - `0` if the change trie root was found.
	/// - `1` if the change trie root was not found.
	fn ext_storage_changes_root(parent_hash_data: *const u8, parent_hash_len: u32, parent_num: u64, result: *mut u8) -> u32;

	/// A child storage function.
	///
	/// See [`ext_set_storage`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_set_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32);
	/// A child storage function.
	///
	/// See [`ext_clear_storage`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_clear_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32);
	/// A child storage function.
	///
	/// See [`ext_exists_storage`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_exists_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32) -> u32;
	/// A child storage function.
	///
	/// See [`ext_kill_storage`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_kill_child_storage(storage_key_data: *const u8, storage_key_len: u32);
	/// A child storage function.
	///
	/// See [`ext_get_allocated_storage`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_get_allocated_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8;
	/// A child storage function.
	///
	/// See [`ext_get_storage_into`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_get_child_storage_into(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32;
	/// A child storage function.
	///
	/// See [`ext_storage_root`] for details.
	///
	/// A child storage is used e.g. by a contract.
	fn ext_child_storage_root(storage_key_data: *const u8, storage_key_len: u32, written_out: *mut u32) -> *mut u8;

	/// The current relay chain identifier.
	fn ext_chain_id() -> u64;

	/// Hash calculation and verification
	fn ext_blake2_256_enumerated_trie_root(values_data: *const u8, lens_data: *const u32, lens_len: u32, result: *mut u8);
	fn ext_blake2_256(data: *const u8, len: u32, out: *mut u8);
	fn ext_twox_128(data: *const u8, len: u32, out: *mut u8);
	fn ext_twox_256(data: *const u8, len: u32, out: *mut u8);
	fn ext_keccak_256(data: *const u8, len: u32, out: *mut u8);
	/// Note: ext_ed25519_verify returns 0 if the signature is correct, nonzero otherwise.
	fn ext_ed25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32;
	/// Note: ext_sr25519_verify returns 0 if the signature is correct, nonzero otherwise.
	fn ext_sr25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32;
	/// Note: ext_secp256k1_ecdsa_recover returns 0 if the signature is correct, nonzero otherwise.
	fn ext_secp256k1_ecdsa_recover(msg_data: *const u8, sig_data: *const u8, pubkey_data: *mut u8) -> u32;
}

/// Ensures we use the right crypto when calling into native
pub trait ExternTrieCrypto {
	fn enumerated_trie_root(values: &[&[u8]]) -> [u8; 32];
}

// Ensures we use a Blake2_256-flavoured Hasher when calling into native
impl ExternTrieCrypto for Blake2Hasher {
	fn enumerated_trie_root(values: &[&[u8]]) -> [u8; 32] {
		let lengths = values.iter().map(|v| (v.len() as u32).to_le()).collect::<Vec<_>>();
		let values = values.iter().fold(Vec::new(), |mut acc, sl| { acc.extend_from_slice(sl); acc });
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_blake2_256_enumerated_trie_root(
				values.as_ptr(),
				lengths.as_ptr(),
				lengths.len() as u32,
				result.as_mut_ptr()
			);
		}
		result
	}
}

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Option<Vec<u8>> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_get_allocated_storage(key.as_ptr(), key.len() as u32, &mut length);
		if length == u32::max_value() {
			None
		} else {
			// Invariants required by Vec::from_raw_parts are not formally fulfilled.
			// We don't allocate via String/Vec<T>, but use a custom allocator instead.
			// See #300 for more details.
			Some(<Vec<u8>>::from_raw_parts(ptr, length as usize, length as usize))
		}
	}
}

/// Get `key` from child storage and return a `Vec`, empty if there's a problem.
pub fn child_storage(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_get_allocated_child_storage(storage_key.as_ptr(), storage_key.len() as u32, key.as_ptr(), key.len() as u32, &mut length);
		if length == u32::max_value() {
			None
		} else {
			// Invariants required by Vec::from_raw_parts are not formally fulfilled.
			// We don't allocate via String/Vec<T>, but use a custom allocator instead.
			// See #300 for more details.
			Some(<Vec<u8>>::from_raw_parts(ptr, length as usize, length as usize))
		}
	}
}

/// Set the storage of some particular key to Some value.
pub fn set_storage(key: &[u8], value: &[u8]) {
	unsafe {
		ext_set_storage(
			key.as_ptr(), key.len() as u32,
			value.as_ptr(), value.len() as u32
		);
	}
}

/// Set the child storage of some particular key to Some value.
pub fn set_child_storage(storage_key: &[u8], key: &[u8], value: &[u8]) {
	unsafe {
		ext_set_child_storage(
			storage_key.as_ptr(), key.len() as u32,
			key.as_ptr(), key.len() as u32,
			value.as_ptr(), value.len() as u32
		);
	}
}

/// Clear the storage of some particular key.
pub fn clear_storage(key: &[u8]) {
	unsafe {
		ext_clear_storage(
			key.as_ptr(), key.len() as u32
		);
	}
}

/// Clear the storage of some particular key.
pub fn clear_child_storage(storage_key: &[u8], key: &[u8]) {
	unsafe {
		ext_clear_child_storage(
			storage_key.as_ptr(), storage_key.len() as u32,
			key.as_ptr(), key.len() as u32
		);
	}
}

/// Determine whether a particular key exists in storage.
pub fn exists_storage(key: &[u8]) -> bool {
	unsafe {
		ext_exists_storage(
			key.as_ptr(), key.len() as u32
		) != 0
	}
}

/// Determine whether a particular key exists in storage.
pub fn exists_child_storage(storage_key: &[u8], key: &[u8]) -> bool {
	unsafe {
		ext_exists_child_storage(
			storage_key.as_ptr(), storage_key.len() as u32,
			key.as_ptr(), key.len() as u32
		) != 0
	}
}

/// Clear the storage entries key of which starts with the given prefix.
pub fn clear_prefix(prefix: &[u8]) {
	unsafe {
		ext_clear_prefix(
			prefix.as_ptr(),
			prefix.len() as u32
		);
	}
}

/// Clear an entire child storage.
pub fn kill_child_storage(storage_key: &[u8]) {
	unsafe {
		ext_kill_child_storage(
			storage_key.as_ptr(),
			storage_key.len() as u32
		);
	}
}

/// Get `key` from storage, placing the value into `value_out` (as much as possible) and return
/// the number of bytes that the key in storage was beyond the offset.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	unsafe {
		match ext_get_storage_into(
			key.as_ptr(), key.len() as u32,
			value_out.as_mut_ptr(), value_out.len() as u32,
			value_offset as u32
		) {
			none if none == u32::max_value() => None,
			length => Some(length as usize),
		}
	}
}

/// Get `key` from child storage, placing the value into `value_out` (as much as possible) and return
/// the number of bytes that the key in storage was beyond the offset.
pub fn read_child_storage(storage_key: &[u8], key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	unsafe {
		match ext_get_child_storage_into(
			storage_key.as_ptr(), storage_key.len() as u32,
			key.as_ptr(), key.len() as u32,
			value_out.as_mut_ptr(), value_out.len() as u32,
			value_offset as u32
		) {
			none if none == u32::max_value() => None,
			length => Some(length as usize),
		}
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

/// "Commit" all existing operations and compute the resultant child storage root.
pub fn child_storage_root(storage_key: &[u8]) -> Option<Vec<u8>> {
	let mut length: u32 = 0;
	unsafe {
		let ptr = ext_child_storage_root(storage_key.as_ptr(), storage_key.len() as u32, &mut length);
		if length == u32::max_value() {
			None
		} else {
			// Invariants required by Vec::from_raw_parts are not formally fulfilled.
			// We don't allocate via String/Vec<T>, but use a custom allocator instead.
			// See #300 for more details.
			Some(<Vec<u8>>::from_raw_parts(ptr, length as usize, length as usize))
		}
	}
}

/// The current storage' changes root.
pub fn storage_changes_root(parent_hash: [u8; 32], parent_num: u64) -> Option<[u8; 32]> {
	let mut result: [u8; 32] = Default::default();
	let is_set = unsafe {
		ext_storage_changes_root(parent_hash.as_ptr(), parent_hash.len() as u32, parent_num, result.as_mut_ptr())
	};

	if is_set != 0 {
		Some(result)
	} else {
		None
	}
}

/// A trie root calculated from enumerated values.
pub fn enumerated_trie_root<H: Hasher + ExternTrieCrypto>(values: &[&[u8]]) -> [u8; 32] {
	H::enumerated_trie_root(values)
}

/// A trie root formed from the iterated items.
pub fn trie_root<
	H: Hasher + ExternTrieCrypto,
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
>(_input: I) -> [u8; 32] {
	unimplemented!()
}

/// A trie root formed from the enumerated items.
pub fn ordered_trie_root<
	H: Hasher + ExternTrieCrypto,
	I: IntoIterator<Item = A>,
	A: AsRef<[u8]>
>(_input: I) -> [u8; 32] {
	unimplemented!()
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

/// Conduct a 256-bit Keccak hash.
pub fn keccak_256(data: &[u8]) -> [u8; 32] {
	let mut result: [u8; 32] = Default::default();
	unsafe {
		ext_keccak_256(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
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
pub fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	unsafe {
		ext_ed25519_verify(msg.as_ptr(), msg.len() as u32, sig.as_ptr(), pubkey.as_ref().as_ptr()) == 0
	}
}

/// Verify a sr25519 signature.
pub fn sr25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	unsafe {
		ext_sr25519_verify(msg.as_ptr(), msg.len() as u32, sig.as_ptr(), pubkey.as_ref().as_ptr()) == 0
	}
}

/// Verify and recover a SECP256k1 ECDSA signature.
/// - `sig` is passed in RSV format. V should be either 0/1 or 27/28.
/// - returns `None` if the signatue is bad, the 64-byte pubkey (doesn't include the 0x04 prefix).
pub fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError> {
	let mut pubkey = [0u8; 64];
	match unsafe {
		ext_secp256k1_ecdsa_recover(msg.as_ptr(), sig.as_ptr(), pubkey.as_mut_ptr())
	} {
		0 => Ok(pubkey),
		1 => Err(EcdsaVerifyError::BadRS),
		2 => Err(EcdsaVerifyError::BadV),
		3 => Err(EcdsaVerifyError::BadSignature),
		_ => unreachable!("`ext_secp256k1_ecdsa_recover` only returns 0, 1, 2 or 3; qed"),
	}
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
