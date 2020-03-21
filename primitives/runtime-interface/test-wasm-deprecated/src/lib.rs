// Copyright 2020 Parity Technologies (UK) Ltd.
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

use sp_core::wasm_export_functions;
use sp_runtime_interface::runtime_interface;

// Include the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

/// This function is not used, but we require it for the compiler to include `sp-io`.
/// `sp-io` is required for its panic and oom handler.
#[no_mangle]
pub fn import_sp_io() {
	sp_io::misc::print_utf8(&[]);
}

#[runtime_interface]
pub trait TestApi {
	fn verify_input(&self, data: u32) -> bool {
		data == 42 || data == 50
	}
}

wasm_export_functions! {
	fn test_verification_of_input_old() {
		// old api allows 42 and 50, which is incorrect (42 is a true answer only)
		// but it is how old runtime works!
		assert!(test_api::verify_input(42));
		assert!(test_api::verify_input(50));

		assert!(!test_api::verify_input(142));
		assert!(!test_api::verify_input(0));
	}
}