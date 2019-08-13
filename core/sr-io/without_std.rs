// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
pub use rstd;
pub use rstd::{mem, slice};

use core::{intrinsics, panic::PanicInfo};
use rstd::{vec::Vec, cell::Cell, convert::TryInto};
use primitives::{offchain, Blake2Hasher};
use codec::Decode;

#[cfg(not(feature = "no_panic_handler"))]
#[panic_handler]
#[no_mangle]
pub fn panic(info: &PanicInfo) -> ! {
	unsafe {
		#[cfg(feature = "wasm-nice-panic-message")]
		{
			let message = rstd::alloc::format!("{}", info);
			extern_functions_host_impl::ext_print_utf8(message.as_ptr() as *const u8, message.len() as u32);
		}
		#[cfg(not(feature = "wasm-nice-panic-message"))]
		{
			if let Some(loc) = info.location() {
				extern_functions_host_impl::ext_print_utf8(loc.file().as_ptr() as *const u8, loc.file().len() as u32);
				extern_functions_host_impl::ext_print_num(loc.line() as u64);
				extern_functions_host_impl::ext_print_num(loc.column() as u64);
			}
		}
		intrinsics::abort()
	}
}

#[cfg(not(feature = "no_oom"))]
#[alloc_error_handler]
pub extern fn oom(_: ::core::alloc::Layout) -> ! {
	static OOM_MSG: &str = "Runtime memory exhausted. Aborting";

	unsafe {
		extern_functions_host_impl::ext_print_utf8(OOM_MSG.as_ptr(), OOM_MSG.len() as u32);
		intrinsics::abort();
	}
}

/// External (Host) APIs
pub mod ext {
	use super::*;

	/// The state of an exchangeable function.
	#[derive(Clone, Copy)]
	enum ExchangeableFunctionState {
		/// Original function is present
		Original,
		/// The function has been replaced.
		Replaced,
	}

	/// A function which implementation can be exchanged.
	///
	/// Internally this works by swapping function pointers.
	pub struct ExchangeableFunction<T>(Cell<(T, ExchangeableFunctionState)>);

	impl<T> ExchangeableFunction<T> {
		/// Create a new instance of `ExchangeableFunction`.
		pub const fn new(impl_: T) -> Self {
			Self(Cell::new((impl_, ExchangeableFunctionState::Original)))
		}
	}

	impl<T: Copy> ExchangeableFunction<T> {
		/// Replace the implementation with `new_impl`.
		///
		/// # Panics
		///
		/// Panics when trying to replace an already replaced implementation.
		///
		/// # Returns
		///
		/// Returns the original implementation wrapped in [`RestoreImplementation`].
		pub fn replace_implementation(&'static self, new_impl: T)  -> RestoreImplementation<T> {
			if let ExchangeableFunctionState::Replaced = self.0.get().1 {
				panic!("Trying to replace an already replaced implementation!")
			}

			let old = self.0.replace((new_impl, ExchangeableFunctionState::Replaced));

			RestoreImplementation(self, Some(old.0))
		}

		/// Restore the original implementation.
		fn restore_orig_implementation(&self, orig: T) {
			self.0.set((orig, ExchangeableFunctionState::Original));
		}

		/// Returns the internal function pointer.
		pub fn get(&self) -> T {
			self.0.get().0
		}
	}

	// WASM does not support threads, so this is safe; qed.
	unsafe impl<T> Sync for ExchangeableFunction<T> {}

	/// Restores a function implementation on drop.
	///
	/// Stores a static reference to the function object and the original implementation.
	pub struct RestoreImplementation<T: 'static + Copy>(&'static ExchangeableFunction<T>, Option<T>);

	impl<T: Copy> Drop for RestoreImplementation<T> {
		fn drop(&mut self) {
			self.0.restore_orig_implementation(self.1.take().expect("Value is only taken on drop; qed"));
		}
	}

	/// Ensures we use the right crypto when calling into native
	pub trait ExternTrieCrypto: Hasher {
		/// A trie root formed from the enumerated items.
		fn ordered_trie_root<
			A: AsRef<[u8]>,
			I: IntoIterator<Item = A>
		>(values: I) -> Self::Out;
	}

	/// Additional bounds for Hasher trait for without_std.
	pub trait HasherBounds: ExternTrieCrypto {}
	impl<T: ExternTrieCrypto + Hasher> HasherBounds for T {}

	// Ensures we use a Blake2_256-flavored Hasher when calling into native
	impl ExternTrieCrypto for Blake2Hasher {
		fn ordered_trie_root<
			A: AsRef<[u8]>,
			I: IntoIterator<Item = A>
		>(items: I) -> Self::Out {
			let mut values = Vec::new();
			let mut lengths = Vec::new();
			for v in items.into_iter() {
				values.extend_from_slice(v.as_ref());
				lengths.push((v.as_ref().len() as u32).to_le());
			}
			let mut result: [u8; 32] = Default::default();
			unsafe {
				ext_blake2_256_enumerated_trie_root.get()(
					values.as_ptr(),
					lengths.as_ptr(),
					lengths.len() as u32,
					result.as_mut_ptr()
				);
			}
			result.into()
		}
	}

	/// Declare extern functions
	macro_rules! extern_functions {
		(
			$(
				$( #[$attr:meta] )*
				fn $name:ident ( $( $arg:ident : $arg_ty:ty ),* $(,)? ) $( -> $ret:ty )?;
			)*
		) => {
			$(
				$( #[$attr] )*
				#[allow(non_upper_case_globals)]
				pub static $name: ExchangeableFunction<unsafe fn ( $( $arg_ty ),* ) $( -> $ret )?> =
					ExchangeableFunction::new(extern_functions_host_impl::$name);
			)*

			/// The exchangeable extern functions host implementations.
			pub(crate) mod extern_functions_host_impl {
				$(
					pub unsafe fn $name ( $( $arg : $arg_ty ),* ) $( -> $ret )? {
						implementation::$name ( $( $arg ),* )
					}
				)*

				mod implementation {
					extern "C" {
						$(
							pub fn $name ( $( $arg : $arg_ty ),* ) $( -> $ret )?;
						)*
					}
				}
			}
		};
	}

	/// Host functions, provided by the executor.
	/// A WebAssembly runtime module would "import" these to access the execution environment
	/// (most importantly, storage) or perform heavy hash calculations.
	/// See also "ext_" functions in sr-sandbox and sr-std
	extern_functions! {
		/// Host functions for printing, useful for debugging.
		fn ext_print_utf8(utf8_data: *const u8, utf8_len: u32);
		/// Print data as hex.
		fn ext_print_hex(data: *const u8, len: u32);
		/// Print a number
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
		/// Remove child storage entries which key starts with given prefix.
		fn ext_clear_child_prefix(
			storage_key_data: *const u8,
			storage_key_len: u32,
			prefix_data: *const u8,
			prefix_len: u32
		);
		/// Gets the value of the given key from storage.
		///
		/// The host allocates the memory for storing the value.
		///
		/// # Returns
		///
		/// - `0` if no value exists to the given key. `written_out` is set to `u32::max_value()`.
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
		fn ext_get_storage_into(
			key_data: *const u8,
			key_len: u32,
			value_data: *mut u8,
			value_len: u32,
			value_offset: u32
		) -> u32;
		/// Gets the trie root of the storage.
		fn ext_storage_root(result: *mut u8);
		/// Get the change trie root of the current storage overlay at a block with given parent.
		///
		/// # Returns
		///
		/// - `1` if the change trie root was found.
		/// - `0` if the change trie root was not found.
		fn ext_storage_changes_root(
			parent_hash_data: *const u8, parent_hash_len: u32, result: *mut u8) -> u32;

		/// A child storage function.
		///
		/// See [`ext_set_storage`] for details.
		///
		/// A child storage is used e.g. by a contract.
		fn ext_set_child_storage(
			storage_key_data: *const u8,
			storage_key_len: u32,
			key_data: *const u8,
			key_len: u32,
			value_data: *const u8,
			value_len: u32
		);
		/// A child storage function.
		///
		/// See [`ext_clear_storage`] for details.
		///
		/// A child storage is used e.g. by a contract.
		fn ext_clear_child_storage(
			storage_key_data: *const u8,
			storage_key_len: u32,
			key_data: *const u8,
			key_len: u32
		);
		/// A child storage function.
		///
		/// See [`ext_exists_storage`] for details.
		///
		/// A child storage is used e.g. by a contract.
		fn ext_exists_child_storage(
			storage_key_data: *const u8,
			storage_key_len: u32,
			key_data: *const u8,
			key_len: u32
		) -> u32;
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
		fn ext_get_allocated_child_storage(
			storage_key_data: *const u8,
			storage_key_len: u32,
			key_data: *const u8,
			key_len: u32,
			written_out: *mut u32
		) -> *mut u8;
		/// A child storage function.
		///
		/// See [`ext_get_storage_into`] for details.
		///
		/// A child storage is used e.g. by a contract.
		fn ext_get_child_storage_into(
			storage_key_data: *const u8,
			storage_key_len: u32,
			key_data: *const u8,
			key_len: u32,
			value_data: *mut u8,
			value_len: u32,
			value_offset: u32
		) -> u32;
		/// Commits all changes and calculates the child-storage root.
		///
		/// A child storage is used e.g. by a contract.
		///
		/// # Returns
		///
		/// - The pointer to the result vector and `written_out` contains its length.
		fn ext_child_storage_root(
			storage_key_data: *const u8,
			storage_key_len: u32,
			written_out: *mut u32
		) -> *mut u8;

		/// The current relay chain identifier.
		fn ext_chain_id() -> u64;

		/// Calculate a blake2_256 merkle trie root.
		fn ext_blake2_256_enumerated_trie_root(
			values_data: *const u8,
			lens_data: *const u32,
			lens_len: u32,
			result: *mut u8
		);
		/// BLAKE2_128 hash
		fn ext_blake2_128(data: *const u8, len: u32, out: *mut u8);
		/// BLAKE2_256 hash
		fn ext_blake2_256(data: *const u8, len: u32, out: *mut u8);
		/// XX64 hash
		fn ext_twox_64(data: *const u8, len: u32, out: *mut u8);
		/// XX128 hash
		fn ext_twox_128(data: *const u8, len: u32, out: *mut u8);
		/// XX256 hash
		fn ext_twox_256(data: *const u8, len: u32, out: *mut u8);
		/// Keccak256 hash
		fn ext_keccak_256(data: *const u8, len: u32, out: *mut u8);

		/// Returns all `ed25519` public keys for the given key type from the keystore.
		fn ext_ed25519_public_keys(id: *const u8, result_len: *mut u32) -> *mut u8;

		/// Note: `ext_ed25519_verify` returns `0` if the signature is correct, nonzero otherwise.
		fn ext_ed25519_verify(
			msg_data: *const u8,
			msg_len: u32,
			sig_data: *const u8,
			pubkey_data: *const u8,
		) -> u32;

		/// Generate an `ed25519` key pair for the given key type id and store the public key
		/// in `out`.
		fn ext_ed25519_generate(id: *const u8, seed: *const u8, seed_len: u32, out: *mut u8);

		/// Sign the given `msg` with the `ed25519` key pair that corresponds to then given key
		/// type id and public key. The raw signature is stored in `out`.
		///
		/// # Returns
		///
		/// - `0` on success
		/// - nonezero if something failed, e.g. retrieving of the key.
		fn ext_ed25519_sign(
			id: *const u8,
			pubkey: *const u8,
			msg: *const u8,
			msg_len: u32,
			out: *mut u8,
		) -> u32;

		/// Returns all `sr25519` public keys for the given key type from the keystore.
		fn ext_sr25519_public_keys(id: *const u8, result_len: *mut u32) -> *mut u8;

		/// Note: `ext_sr25519_verify` returns 0 if the signature is correct, nonzero otherwise.
		fn ext_sr25519_verify(
			msg_data: *const u8,
			msg_len: u32,
			sig_data: *const u8,
			pubkey_data: *const u8,
		) -> u32;

		/// Generate an `sr25519` key pair for the given key type id and store the public
		/// key in `out`.
		fn ext_sr25519_generate(id: *const u8, seed: *const u8, seed_len: u32, out: *mut u8);

		/// Sign the given `msg` with the `sr25519` key pair that corresponds to then given key
		/// type id and public key. The raw signature is stored in `out`.
		///
		/// # Returns
		///
		/// - `0` on success
		/// - nonezero if something failed, e.g. retrieving of the key.
		fn ext_sr25519_sign(
			id: *const u8,
			pubkey: *const u8,
			msg: *const u8,
			msg_len: u32,
			out: *mut u8,
		) -> u32;

		/// Note: ext_secp256k1_ecdsa_recover returns 0 if the signature is correct, nonzero otherwise.
		fn ext_secp256k1_ecdsa_recover(
			msg_data: *const u8,
			sig_data: *const u8,
			pubkey_data: *mut u8,
		) -> u32;

		//================================
		// Offchain-worker Context
		//================================

		/// Returns if the local node is a potential validator.
		///
		/// - `1` == `true`
		/// - `0` == `false`
		fn ext_is_validator() -> u32;

		/// Submit transaction.
		///
		/// # Returns
		///
		/// - 0 if it was successfuly added to the pool
		/// - nonzero otherwise.
		fn ext_submit_transaction(data: *const u8, len: u32) -> u32;

		/// Returns information about the local node's network state.
		///
		/// # Returns
		///
		/// The encoded `Result<offchain::OpaqueNetworkState, ()>`.
		/// `written_out` contains the length of the message.
		///
		/// The ownership of the returned buffer is transferred to the runtime
		/// code and the runtime is responsible for freeing it. This is always
		/// a properly allocated pointer (which cannot be NULL), hence the
		/// runtime code can always rely on it.
		fn ext_network_state(written_out: *mut u32) -> *mut u8;

		/// Returns current UNIX timestamp (milliseconds)
		fn ext_timestamp() -> u64;

		/// Pause execution until given timestamp (milliseconds; `deadline`) is reached.
		///
		/// The deadline is obtained by querying the current timestamp via `ext_timestamp`
		/// and then adding some time to it.
		fn ext_sleep_until(deadline: u64);

		/// Generate a random seed
		///
		/// `data` has to be a pointer to a slice of 32 bytes.
		fn ext_random_seed(data: *mut u8);

		/// Write a value to local storage.
		fn ext_local_storage_set(kind: u32, key: *const u8, key_len: u32, value: *const u8, value_len: u32);

		/// Write a value to local storage in atomic fashion.
		///
		/// # Returns
		/// - `0` in case the value has been set
		/// - `1` if the `old_value` didn't match
		fn ext_local_storage_compare_and_set(
			kind: u32,
			key: *const u8,
			key_len: u32,
			old_value: *const u8,
			old_value_len: u32,
			new_value: *const u8,
			new_value_len: u32
		) -> u32;

		/// Read a value from local storage.
		///
		///
		/// # Returns
		///
		/// - 0 if the value has not been found, the `value_len` is set to `u32::max_value`.
		/// - Otherwise, pointer to the value in memory. `value_len` contains the length of the value.
		fn ext_local_storage_get(kind: u32, key: *const u8, key_len: u32, value_len: *mut u32) -> *mut u8;

		/// Initiates a http request.
		///
		/// `meta` is parity-scale-codec encoded additional parameters to the request (like redirection policy,
		/// timeouts, certificates policy, etc). The format is not yet specified and the field is currently
		/// only reserved for future use.
		///
		/// # Returns
		///
		///	`RequestId(u16)` of initiated request, any value beyond `u16::max_value`
		/// signifies an error.
		fn ext_http_request_start(
			method: *const u8,
			method_len: u32,
			url: *const u8,
			url_len: u32,
			meta: *const u8,
			meta_len: u32
		) -> u32;

		/// Add a header to the request.
		///
		/// # Returns
		///
		/// - `0` if successful (and the request id exists)
		/// - nonzero otherwise
		fn ext_http_request_add_header(
			request_id: u32,
			name: *const u8,
			name_len: u32,
			value: *const u8,
			value_len: u32
		) -> u32;

		/// Write a chunk of request body.
		///
		/// Writing an empty chunks finalises the request.
		/// Passing `0` as deadline blocks forever.
		///
		/// # Returns
		///
		/// - `0` if successful,
		/// - nonzero otherwise (see HttpError for the codes)
		fn ext_http_request_write_body(
			request_id: u32,
			chunk: *const u8,
			chunk_len: u32,
			deadline: u64
		) -> u32;

		/// Block and wait for the responses for given requests.
		///
		/// Note that if deadline is 0 the method will block indefinitely,
		/// otherwise unready responses will produce `DeadlineReached` status.
		/// (see #primitives::offchain::HttpRequestStatus)
		///
		/// Make sure that `statuses` have the same length as ids.
		fn ext_http_response_wait(
			ids: *const u32,
			ids_len: u32,
			statuses: *mut u32,
			deadline: u64
		);

		/// Read all response headers.
		///
		/// Note the headers are only available before response body is fully consumed.
		///
		/// # Returns
		///
		/// - A pointer to parity-scale-codec encoded vector of pairs `(HeaderKey, HeaderValue)`.
		/// - In case invalid `id` is passed it returns a pointer to parity-encoded empty vector.
		fn ext_http_response_headers(
			id: u32,
			written_out: *mut u32
		) -> *mut u8;

		/// Read a chunk of body response to given buffer.
		///
		/// Passing `0` as deadline blocks forever.
		///
		/// # Returns
		///
		/// The number of bytes written if successful,
		/// - if it's `0` it means response has been fully consumed,
		/// - if it's greater than `u32::max_value() - 255` it means reading body failed.
		///
		/// In case of failure, the error code should be mapped to `HttpError`
		/// in a following manner:
		/// - `u32::max_value()` HttpError code 1 (DeadlineReached)
		/// - `u32::max_value() - 1` HttpError code 2 (IoError)
		/// The rest is reserved for potential future errors.
		fn ext_http_response_read_body(
			id: u32,
			buffer: *mut u8,
			buffer_len: u32,
			deadline: u64
		) -> u32;
	}
}

pub use self::ext::*;

impl StorageApi for () {
	fn storage(key: &[u8]) -> Option<Vec<u8>> {
		let mut length: u32 = 0;
		unsafe {
			let ptr = ext_get_allocated_storage.get()(key.as_ptr(), key.len() as u32, &mut length);
			from_raw_parts(ptr, length)
		}
	}

	fn child_storage(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let mut length: u32 = 0;
		unsafe {
			let ptr = ext_get_allocated_child_storage.get()(
				storage_key.as_ptr(),
				storage_key.len() as u32,
				key.as_ptr(),
				key.len() as u32,
				&mut length
			);
			from_raw_parts(ptr, length)
		}
	}

	fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
		unsafe {
			match ext_get_storage_into.get()(
				key.as_ptr(),
				key.len() as u32,
				value_out.as_mut_ptr(),
				value_out.len() as u32,
				value_offset as u32,
			) {
				none if none == u32::max_value() => None,
				length => Some(length as usize),
			}
		}
	}

	fn read_child_storage(storage_key: &[u8], key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
		unsafe {
			match ext_get_child_storage_into.get()(
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

	fn set_storage(key: &[u8], value: &[u8]) {
		unsafe {
			ext_set_storage.get()(
				key.as_ptr(), key.len() as u32,
				value.as_ptr(), value.len() as u32
			);
		}
	}

	fn set_child_storage(storage_key: &[u8], key: &[u8], value: &[u8]) {
		unsafe {
			ext_set_child_storage.get()(
				storage_key.as_ptr(), storage_key.len() as u32,
				key.as_ptr(), key.len() as u32,
				value.as_ptr(), value.len() as u32
			);
		}
	}

	fn clear_storage(key: &[u8]) {
		unsafe {
			ext_clear_storage.get()(
				key.as_ptr(), key.len() as u32
			);
		}
	}

	fn clear_child_storage(storage_key: &[u8], key: &[u8]) {
		unsafe {
			ext_clear_child_storage.get()(
				storage_key.as_ptr(), storage_key.len() as u32,
				key.as_ptr(), key.len() as u32
			);
		}
	}

	fn exists_storage(key: &[u8]) -> bool {
		unsafe {
			ext_exists_storage.get()(
				key.as_ptr(), key.len() as u32
			) != 0
		}
	}

	fn exists_child_storage(storage_key: &[u8], key: &[u8]) -> bool {
		unsafe {
			ext_exists_child_storage.get()(
				storage_key.as_ptr(), storage_key.len() as u32,
				key.as_ptr(), key.len() as u32
			) != 0
		}
	}

	fn clear_prefix(prefix: &[u8]) {
		unsafe {
			ext_clear_prefix.get()(
				prefix.as_ptr(),
				prefix.len() as u32
			);
		}
	}

	fn clear_child_prefix(storage_key: &[u8], prefix: &[u8]) {
		unsafe {
			ext_clear_child_prefix.get()(
				storage_key.as_ptr(), storage_key.len() as u32,
				prefix.as_ptr(), prefix.len() as u32
			);
		}
	}

	fn kill_child_storage(storage_key: &[u8]) {
		unsafe {
			ext_kill_child_storage.get()(
				storage_key.as_ptr(),
				storage_key.len() as u32
			);
		}
	}

	fn storage_root() -> [u8; 32] {
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_storage_root.get()(result.as_mut_ptr());
		}
		result
	}

	fn child_storage_root(storage_key: &[u8]) -> Vec<u8> {
		let mut length: u32 = 0;
		unsafe {
			let ptr = ext_child_storage_root.get()(
				storage_key.as_ptr(),
				storage_key.len() as u32,
				&mut length
			);
			from_raw_parts(ptr, length).expect("ext_child_storage_root never returns u32::max_value; qed")
		}
	}

	fn storage_changes_root(parent_hash: [u8; 32]) -> Option<[u8; 32]> {
		let mut result: [u8; 32] = Default::default();
		let is_set = unsafe {
			ext_storage_changes_root.get()(parent_hash.as_ptr(), parent_hash.len() as u32, result.as_mut_ptr())
		};

		if is_set != 0 {
			Some(result)
		} else {
			None
		}
	}

	fn trie_root<
		H: Hasher + ExternTrieCrypto,
		I: IntoIterator<Item = (A, B)>,
		A: AsRef<[u8]> + Ord,
		B: AsRef<[u8]>,
	>(_input: I) -> H::Out {
		unimplemented!()
	}

	fn ordered_trie_root<
		H: Hasher + ExternTrieCrypto,
		I: IntoIterator<Item = A>,
		A: AsRef<[u8]>
	>(values: I) -> H::Out {
		H::ordered_trie_root(values)
	}
}

impl OtherApi for () {
	fn chain_id() -> u64 {
		unsafe {
			ext_chain_id.get()()
		}
	}

	fn print<T: Printable + Sized>(value: T) {
		value.print()
	}

}

impl HashingApi for () {
	fn keccak_256(data: &[u8]) -> [u8; 32] {
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_keccak_256.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	fn blake2_128(data: &[u8]) -> [u8; 16] {
		let mut result: [u8; 16] = Default::default();
		unsafe {
			ext_blake2_128.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	fn blake2_256(data: &[u8]) -> [u8; 32] {
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_blake2_256.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	fn twox_256(data: &[u8]) -> [u8; 32] {
		let mut result: [u8; 32] = Default::default();
		unsafe {
			ext_twox_256.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	fn twox_128(data: &[u8]) -> [u8; 16] {
		let mut result: [u8; 16] = Default::default();
		unsafe {
			ext_twox_128.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}

	fn twox_64(data: &[u8]) -> [u8; 8] {
		let mut result: [u8; 8] = Default::default();
		unsafe {
			ext_twox_64.get()(data.as_ptr(), data.len() as u32, result.as_mut_ptr());
		}
		result
	}
}

impl CryptoApi for () {
	fn ed25519_public_keys(id: KeyTypeId) -> Vec<ed25519::Public> {
		let mut res_len = 0u32;
		unsafe {
			let res_ptr = ext_ed25519_public_keys.get()(id.0.as_ptr(), &mut res_len);
			Vec::decode(&mut rstd::slice::from_raw_parts(res_ptr, res_len as usize)).unwrap_or_default()
		}
	}

	fn ed25519_generate(id: KeyTypeId, seed: Option<&str>) -> ed25519::Public {
		let mut res = [0u8; 32];
		let seed = seed.as_ref().map(|s| s.as_bytes()).unwrap_or(&[]);
		unsafe {
			ext_ed25519_generate.get()(id.0.as_ptr(), seed.as_ptr(), seed.len() as u32, res.as_mut_ptr())
		};
		ed25519::Public(res)
	}

	fn ed25519_sign<M: AsRef<[u8]>>(
		id: KeyTypeId,
		pubkey: &ed25519::Public,
		msg: &M,
	) -> Option<ed25519::Signature> {
		let mut res = [0u8; 64];
		let success = unsafe {
			ext_ed25519_sign.get()(
				id.0.as_ptr(),
				pubkey.0.as_ptr(),
				msg.as_ref().as_ptr(),
				msg.as_ref().len() as u32,
				res.as_mut_ptr(),
			) == 0
		};

		if success {
			Some(ed25519::Signature(res))
		} else {
			None
		}
	}

	fn ed25519_verify(sig: &ed25519::Signature, msg: &[u8], pubkey: &ed25519::Public) -> bool {
		unsafe {
			ext_ed25519_verify.get()(
				msg.as_ptr(),
				msg.len() as u32,
				sig.0.as_ptr(),
				pubkey.0.as_ptr(),
			) == 0
		}
	}

	fn sr25519_public_keys(id: KeyTypeId) -> Vec<sr25519::Public> {
		let mut res_len = 0u32;
		unsafe {
			let res_ptr = ext_sr25519_public_keys.get()(id.0.as_ptr(), &mut res_len);
			Vec::decode(&mut rstd::slice::from_raw_parts(res_ptr, res_len as usize)).unwrap_or_default()
		}
	}

	fn sr25519_generate(id: KeyTypeId, seed: Option<&str>) -> sr25519::Public {
		let mut res = [0u8;32];
		let seed = seed.as_ref().map(|s| s.as_bytes()).unwrap_or(&[]);
		unsafe {
			ext_sr25519_generate.get()(id.0.as_ptr(), seed.as_ptr(), seed.len() as u32, res.as_mut_ptr())
		};
		sr25519::Public(res)
	}

	fn sr25519_sign<M: AsRef<[u8]>>(
		id: KeyTypeId,
		pubkey: &sr25519::Public,
		msg: &M,
	) -> Option<sr25519::Signature> {
		let mut res = [0u8; 64];
		let success = unsafe {
			ext_sr25519_sign.get()(
				id.0.as_ptr(),
				pubkey.0.as_ptr(),
				msg.as_ref().as_ptr(),
				msg.as_ref().len() as u32,
				res.as_mut_ptr(),
			) == 0
		};

		if success {
			Some(sr25519::Signature(res))
		} else {
			None
		}
	}

	fn sr25519_verify(sig: &sr25519::Signature, msg: &[u8], pubkey: &sr25519::Public) -> bool {
		unsafe {
			ext_sr25519_verify.get()(
				msg.as_ptr(),
				msg.len() as u32,
				sig.0.as_ptr(),
				pubkey.0.as_ptr(),
			) == 0
		}
	}

	fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError> {
		let mut pubkey = [0u8; 64];
		match unsafe {
			ext_secp256k1_ecdsa_recover.get()(msg.as_ptr(), sig.as_ptr(), pubkey.as_mut_ptr())
		} {
			0 => Ok(pubkey),
			1 => Err(EcdsaVerifyError::BadRS),
			2 => Err(EcdsaVerifyError::BadV),
			3 => Err(EcdsaVerifyError::BadSignature),
			_ => unreachable!("`ext_secp256k1_ecdsa_recover` only returns 0, 1, 2 or 3; qed"),
		}
	}
}

impl OffchainApi for () {
	fn is_validator() -> bool {
		unsafe { ext_is_validator.get()() == 1 }
	}

	fn submit_transaction<T: codec::Encode>(data: &T) -> Result<(), ()> {
		let encoded_data = codec::Encode::encode(data);
		let ret = unsafe {
			ext_submit_transaction.get()(encoded_data.as_ptr(), encoded_data.len() as u32)
		};

		if ret == 0 {
			Ok(())
		} else {
			Err(())
		}
	}

	fn network_state() -> Result<offchain::OpaqueNetworkState, ()> {
		let mut len = 0_u32;
		let raw_result = unsafe {
			let ptr = ext_network_state.get()(&mut len);

			from_raw_parts(ptr, len)
		};

		match raw_result {
			Some(raw_result) => codec::Decode::decode(&mut &*raw_result).unwrap_or(Err(())),
			None => Err(())
		}
	}

	fn timestamp() -> offchain::Timestamp {
		offchain::Timestamp::from_unix_millis(unsafe {
			ext_timestamp.get()()
		})
	}

	fn sleep_until(deadline: offchain::Timestamp) {
		unsafe {
			ext_sleep_until.get()(deadline.unix_millis())
		}
	}

	fn random_seed() -> [u8; 32] {
		let mut result = [0_u8; 32];
		unsafe {
			ext_random_seed.get()(result.as_mut_ptr())
		}
		result
	}

	fn local_storage_set(kind: offchain::StorageKind, key: &[u8], value: &[u8]) {
		unsafe {
			ext_local_storage_set.get()(
				kind.into(),
				key.as_ptr(),
				key.len() as u32,
				value.as_ptr(),
				value.len() as u32,
			)
		}
	}

	fn local_storage_compare_and_set(
		kind: offchain::StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let (ptr, len) = match old_value {
			Some(old_value) => (
				old_value.as_ptr(),
				old_value.len() as u32,
			),
			None => (0 as *const u8, u32::max_value()),
		};

		unsafe {
			ext_local_storage_compare_and_set.get()(
				kind.into(),
				key.as_ptr(),
				key.len() as u32,
				ptr,
				len,
				new_value.as_ptr(),
				new_value.len() as u32,
			) == 0
		}
	}

	fn local_storage_get(kind: offchain::StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		let mut len = 0u32;
		unsafe {
			let ptr = ext_local_storage_get.get()(
				kind.into(),
				key.as_ptr(),
				key.len() as u32,
				&mut len,
			);

			from_raw_parts(ptr, len)
		}
	}

	fn http_request_start(method: &str, url: &str, meta: &[u8]) -> Result<offchain::HttpRequestId, ()> {
		let method = method.as_bytes();
		let url = url.as_bytes();

		let result = unsafe {
			ext_http_request_start.get()(
				method.as_ptr(),
				method.len() as u32,
				url.as_ptr(),
				url.len() as u32,
				meta.as_ptr(),
				meta.len() as u32,
			)
		};

		if result > u16::max_value() as u32 {
			Err(())
		} else {
			Ok(offchain::HttpRequestId(result as u16))
		}
	}

	fn http_request_add_header(request_id: offchain::HttpRequestId, name: &str, value: &str) -> Result<(), ()> {
		let name = name.as_bytes();
		let value = value.as_bytes();

		let result = unsafe {
			ext_http_request_add_header.get()(
				request_id.into(),
				name.as_ptr(),
				name.len() as u32,
				value.as_ptr(),
				value.len() as u32,
			)
		};

		if result == 0 {
			Ok(())
		} else {
			Err(())
		}
	}

	fn http_request_write_body(
		request_id: offchain::HttpRequestId,
		chunk: &[u8],
		deadline: Option<offchain::Timestamp>
	) -> Result<(), offchain::HttpError> {
		let res = unsafe {
			ext_http_request_write_body.get()(
				request_id.into(),
				chunk.as_ptr(),
				chunk.len() as u32,
				deadline.map_or(0, |x| x.unix_millis()),
			)
		};

		if res == 0 {
			Ok(())
		} else {
			Err(res.try_into().unwrap_or(offchain::HttpError::IoError))
		}
	}

	fn http_response_wait(
		ids: &[offchain::HttpRequestId],
		deadline: Option<offchain::Timestamp>
	) -> Vec<offchain::HttpRequestStatus> {
		let ids = ids.iter().map(|x| x.0 as u32).collect::<Vec<_>>();
		let mut statuses = Vec::new();
		statuses.resize(ids.len(), 0u32);

		unsafe {
			ext_http_response_wait.get()(
				ids.as_ptr(),
				ids.len() as u32,
				statuses.as_mut_ptr(),
				deadline.map_or(0, |x| x.unix_millis()),
			)
		}

		statuses
			.into_iter()
			.map(|status| status.try_into().unwrap_or(offchain::HttpRequestStatus::Unknown))
			.collect()
	}

	fn http_response_headers(
		request_id: offchain::HttpRequestId,
	) -> Vec<(Vec<u8>, Vec<u8>)> {
		let mut len = 0u32;
		let raw_result = unsafe {
			let ptr = ext_http_response_headers.get()(
				request_id.into(),
				&mut len,
			);

			from_raw_parts(ptr, len).expect("ext_http_response_headers never return u32::max_value; qed")
		};

		codec::Decode::decode(&mut &*raw_result).unwrap_or_default()
	}

	fn http_response_read_body(
		request_id: offchain::HttpRequestId,
		buffer: &mut [u8],
		deadline: Option<offchain::Timestamp>,
	) -> Result<usize, offchain::HttpError> {
		let res = unsafe {
			ext_http_response_read_body.get()(
				request_id.into(),
				buffer.as_mut_ptr(),
				buffer.len() as u32,
				deadline.map_or(0, |x| x.unix_millis()),
			)
		};

		if res >= u32::max_value() - 255 {
			let code = (u32::max_value() - res) + 1;
			code.try_into().map_err(|_| offchain::HttpError::IoError)
		} else {
			Ok(res as usize)
		}
	}
}

unsafe fn from_raw_parts(ptr: *mut u8, len: u32) -> Option<Vec<u8>> {
	if len == u32::max_value() {
		None
	} else {
		// Invariants required by Vec::from_raw_parts are not formally fulfilled.
		// We don't allocate via String/Vec<T>, but use a custom allocator instead.
		// See #300 for more details.
		Some(<Vec<u8>>::from_raw_parts(ptr, len as usize, len as usize))
	}
}

impl Api for () {}

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		unsafe {
			ext_print_hex.get()(self.as_ptr(), self.len() as u32);
		}
	}
}

impl<'a> Printable for &'a str {
	fn print(self) {
		unsafe {
			ext_print_utf8.get()(self.as_ptr() as *const u8, self.len() as u32);
		}
	}
}

impl Printable for u64 {
	fn print(self) {
		unsafe { ext_print_num.get()(self); }
	}
}
