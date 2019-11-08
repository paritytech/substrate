// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Tests for the runtime interface traits and proc macros.

#![cfg_attr(not(feature = "std"), no_std)]

use runtime_interface::runtime_interface;

#[cfg(not(feature = "std"))]
use rstd::{vec, vec::Vec, mem, convert::TryFrom};

use primitives::{sr25519::Public, wasm_export_functions};

// Inlucde the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

/// Used in the `test_array_as_mutable_reference` test.
const TEST_ARRAY: [u8; 16] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

#[runtime_interface]
pub trait TestApi {
	/// Returns the input data as result.
	fn return_input(data: Vec<u8>) -> Vec<u8> {
		data
	}

	/// Set the storage at key with value.
	fn set_storage(&mut self, key: &[u8], data: &[u8]) {
		self.place_storage(key.to_vec(), Some(data.to_vec()));
	}

	/// Copy `hello` into the given mutable reference
	fn return_value_into_mutable_reference(&self, data: &mut [u8]) {
		let res = "hello";
		data[..res.as_bytes().len()].copy_from_slice(res.as_bytes());
	}

	/// Returns the input data wrapped in an `Option` as result.
	fn return_option_input(data: Vec<u8>) -> Option<Vec<u8>> {
		Some(data)
	}

	/// Get an array as input and returns a subset of this array.
	fn get_and_return_array(data: [u8; 34]) -> [u8; 16] {
		let mut res = [0u8; 16];
		res.copy_from_slice(&data[..16]);
		res
	}

	/// Take and fill mutable array.
	fn array_as_mutable_reference(data: &mut [u8; 16]) {
		data.copy_from_slice(&TEST_ARRAY);
	}

	/// Returns the given public key as result.
	fn return_input_public_key(key: Public) -> Public {
		key
	}

	/// A function that is called with invalid utf8 data from the runtime.
	///
	/// This also checks that we accept `_` (wild card) argument names.
	fn invalid_utf8_data(_: &str) {}

	/// Overwrite the native implementation in wasm. The native implementation always returns
	/// `false` and the replacement function will return always `true`.
	fn overwrite_native_function_implementation() -> bool {
		false
	}
}

/// Two random external functions from the old runtime interface.
/// This ensures that we still inherently export these functions from the host and that we are still
/// compatible with old wasm runtimes.
extern "C" {
	pub fn ext_clear_storage(key_data: *const u8, key_len: u32);
	pub fn ext_keccak_256(data: *const u8, len: u32, out: *mut u8);
}

/// Make sure the old runtime interface needs to be imported.
#[no_mangle]
pub fn force_old_runtime_interface_import() {
	unsafe { ext_clear_storage(rstd::ptr::null(), 0); }
	unsafe { ext_keccak_256(rstd::ptr::null(), 0, rstd::ptr::null_mut()); }
}

/// This function is not used, but we require it for the compiler to include `runtime-io`.
/// `runtime-io` is required for its panic and oom handler.
#[no_mangle]
pub fn import_runtime_io() {
	runtime_io::misc::print_utf8(&[]);
}

wasm_export_functions! {
	fn test_return_data() {
		let input = vec![1, 2, 3, 4, 5, 6];
		let res = test_api::return_input(input.clone());

		assert_eq!(input, res);
	}

	fn test_return_option_data() {
		let input = vec![1, 2, 3, 4, 5, 6];
		let res = test_api::return_option_input(input.clone());

		assert_eq!(Some(input), res);
	}

	fn test_set_storage() {
		let key = "hello";
		let value = "world";

		test_api::set_storage(key.as_bytes(), value.as_bytes());
	}

	fn test_return_value_into_mutable_reference() {
		let mut data = vec![1, 2, 3, 4, 5, 6];

		test_api::return_value_into_mutable_reference(&mut data);

		let expected = "hello";
		assert_eq!(expected.as_bytes(), &data[..expected.len()]);
	}

	fn test_get_and_return_array() {
		let mut input = unsafe { mem::MaybeUninit::<[u8; 34]>::zeroed().assume_init() };
		input.copy_from_slice(&[
			24, 3, 23, 20, 2, 16, 32, 1, 12, 26, 27, 8, 29, 31, 6, 5, 4, 19, 10, 28, 34, 21, 18, 33, 9,
			13, 22, 25, 15, 11, 30, 7, 14, 17,
		]);

		let res = test_api::get_and_return_array(input);

		assert_eq!(&res, &input[..16]);
	}

	fn test_array_as_mutable_reference() {
		let mut array = [0u8; 16];
		test_api::array_as_mutable_reference(&mut array);

		assert_eq!(array, TEST_ARRAY);
	}

	fn test_return_input_public_key() {
		let key = Public::try_from(
			&[
				1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
				25, 26, 27, 28, 29, 30, 31, 32,
			][..],
		).unwrap();
		let ret_key = test_api::return_input_public_key(key.clone());

		let key_data: &[u8] = key.as_ref();
		let ret_key_data: &[u8] = ret_key.as_ref();
		assert_eq!(key_data, ret_key_data);
	}

	fn test_invalid_utf8_data_should_return_an_error() {
		let data = vec![0, 159, 146, 150];
		// I'm an evil hacker, trying to hack!
		let data_str = unsafe { rstd::str::from_utf8_unchecked(&data) };

		test_api::invalid_utf8_data(data_str);
	}

	fn test_overwrite_native_function_implementation() {
		fn new_implementation() -> bool {
			true
		}

		// Check native implementation
		assert!(!test_api::overwrite_native_function_implementation());

		let _guard = test_api::host_overwrite_native_function_implementation
			.replace_implementation(new_implementation);

		assert!(test_api::overwrite_native_function_implementation());
	}
}
