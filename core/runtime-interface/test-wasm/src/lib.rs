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

#![cfg_attr(not(feature = "std"), no_std)]

use runtime_interface::runtime_interface;

use rstd::{vec, vec::Vec};

// Inlucde the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

#[runtime_interface]
trait TestApi {
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
}

#[no_mangle]
pub fn test_return_data() {
	let input = vec![1, 2, 3, 4, 5, 6];
	let res = test_api::return_input(input.clone());

	assert_eq!(input, res);
}

#[no_mangle]
pub fn test_set_storage() {
	let key = "hello";
	let value = "world";

	test_api::set_storage(key.as_bytes(), value.as_bytes());
}
