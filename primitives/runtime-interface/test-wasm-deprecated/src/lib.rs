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
	fn test_versionning(&self, _data: u32) -> bool {
		// should not be called
		unimplemented!()
	}
}

wasm_export_functions! {
	fn test_versionning_works() {
		// old api allows only 42 and 50
		assert!(test_api::test_versionning(42));
		assert!(test_api::test_versionning(50));

		assert!(!test_api::test_versionning(142));
		assert!(!test_api::test_versionning(0));
	}
}