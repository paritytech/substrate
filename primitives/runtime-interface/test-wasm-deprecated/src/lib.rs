// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for the runtime interface traits and proc macros.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_core::wasm_export_functions;
use sp_runtime_interface::runtime_interface;

// Include the WASM binary
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_unwrap() -> &'static [u8] {
	WASM_BINARY.expect("Development wasm binary is not available. Testing is only \
						supported with the flag disabled.")
}

/// This function is not used, but we require it for the compiler to include `sp-io`.
/// `sp-io` is required for its panic and oom handler.
#[cfg(not(feature = "std"))]
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
