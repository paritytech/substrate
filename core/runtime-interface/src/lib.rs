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

//! Traits and macros for creating interfaces between the runtime and the node.
//!
//! To make the communication between wasm and the host as fast as possible, we use a two-way
//! conversion strategy. First, we convert the value into a [`WrappedFFIValue`].
//! This value stores a reference or an owned value that are convertible into the actual ffi value.
//! So, for values like `Vec<u8>` we just store a reference to the underlying slice and don't need
//! to allocate any memory. In the second step we get the actual ffi value from this
//! [`WrappedFFIValue`] to call into the host. The created [`WrappedFFIValue`] will remain on
//! the stack while we call into the host.

#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
#[cfg(feature = "std")]
pub use wasm_interface;

pub use substrate_runtime_interface_proc_macro::runtime_interface;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use externalities::{
	set_and_run_with_externalities, with_externalities, Externalities, ExternalitiesExt, ExtensionStore,
};

#[doc(hidden)]
pub use codec;

pub(crate) mod impls;
#[cfg(feature = "std")]
pub mod host;
#[cfg(not(feature = "std"))]
pub mod wasm;
pub mod pass_by;

/// Something that can be used by the runtime interface as type to communicate between wasm and the
/// host.
///
/// Every type that should be used in a runtime interface function signature needs to implement
/// this trait.
pub trait RIType {
	/// The ffi type that is used to represent `Self`.
	#[cfg(feature = "std")]
	type FFIType: wasm_interface::IntoValue + wasm_interface::TryFromValue;
	#[cfg(not(feature = "std"))]
	type FFIType;
}

#[cfg(not(feature = "std"))]
pub type Pointer<T> = *mut T;

#[cfg(feature = "std")]
pub type Pointer<T> = wasm_interface::Pointer<T>;

#[cfg(test)]
mod tests {
	use super::*;
	use test_wasm::{WASM_BINARY, test_api::HostFunctions};
	use wasm_interface::HostFunctions as HostFunctionsT;

	type TestExternalities = state_machine::TestExternalities<primitives::Blake2Hasher, u64>;

	fn call_wasm_method<HF: HostFunctionsT>(method: &str) -> TestExternalities {
		let mut ext = TestExternalities::default();
		let mut ext_ext = ext.ext();

		executor::call_in_wasm::<_, (HF, runtime_io::SubstrateHostFunctions)>(
			method,
			&[],
			executor::WasmExecutionMethod::Interpreted,
			&mut ext_ext,
			&WASM_BINARY[..],
			8,
		).expect(&format!("Executes `{}`", method));

		ext
	}

	#[test]
	fn test_return_data() {
		call_wasm_method::<HostFunctions>("test_return_data");
	}

	#[test]
	fn test_return_option_data() {
		call_wasm_method::<HostFunctions>("test_return_option_data");
	}

	#[test]
	fn test_set_storage() {
		let mut ext = call_wasm_method::<HostFunctions>("test_set_storage");

		let expected = "world";
		assert_eq!(expected.as_bytes(), &ext.ext().storage("hello".as_bytes()).unwrap()[..]);
	}

	#[test]
	fn test_return_value_into_mutable_reference() {
		call_wasm_method::<HostFunctions>("test_return_value_into_mutable_reference");
	}

	#[test]
	fn test_get_and_return_array() {
		call_wasm_method::<HostFunctions>("test_get_and_return_array");
	}

	#[test]
	fn test_array_as_mutable_reference() {
		call_wasm_method::<HostFunctions>("test_array_as_mutable_reference");
	}

	#[test]
	fn test_return_input_public_key() {
		call_wasm_method::<HostFunctions>("test_return_input_public_key");
	}

	#[test]
	#[should_panic(expected = "Other(\"Instantiation: Export ext_test_api_return_input not found\")")]
	fn host_function_not_found() {
		call_wasm_method::<()>("test_return_data");
	}
}
