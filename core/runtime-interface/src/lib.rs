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

#[doc(hidden)]
pub use primitives::Blake2Hasher;

use codec::Codec;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use primitives::traits::Externalities;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use wasm_interface;

pub use substrate_runtime_interface_proc_macro::runtime_interface;

#[cfg(feature = "std")]
pub use externalities::{set_and_run_with_externalities, with_externalities};

#[cfg(feature = "std")]
mod externalities;
mod impls;
#[cfg(feature = "std")]
pub mod host;
#[cfg(not(feature = "std"))]
pub mod wasm;

/// Something that can be used by the runtime interface as type to communicate between wasm and the host.
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


impl<T> RIType for Vec<T> {
	type FFIType = u64;
}

impl<T> RIType for [T] {
	type FFIType = u64;
}

/// Marker trait for types that should be passed between wasm and the host by using SCALE codec.
///
/// # Example
/// ```
/// # use substrate_runtime_interface::PassByCodec;
/// #[derive(codec::Encode, codec::Decode)]
/// struct Test;
///
/// // It is sufficient to implement the trait for the desired type and it will be usable with
/// // the runtime interface.
/// impl PassByCodec for Test {}
/// ```
pub trait PassByCodec: Codec {}

impl<T: PassByCodec> RIType for T {
	type FFIType = u64;
}

impl<T: Codec> PassByCodec for Option<T> {}

impl<T: Codec, E: Codec> PassByCodec for Result<T, E> {}

#[cfg(test)]
mod tests {
	use super::*;
	use test_wasm::{WASM_BINARY, test_api::HostFunctions};
	use executor::WasmExecutor;
	use wasm_interface::HostFunctions as HostFunctionsT;

	type TestExternalities<H> = state_machine::TestExternalities<H, u64>;

	fn call_wasm_method<HF: HostFunctionsT>(method: &str) -> TestExternalities<Blake2Hasher> {
		let mut ext = TestExternalities::default();
		let executor = WasmExecutor::<HF>::new();

		executor.call_with_custom_signature::<_, _, _, ()>(
			&mut ext,
			8,
			&WASM_BINARY[..],
			method,
			|_| Ok(Vec::new()),
			|res, _| if res.is_none() { Ok(Some(())) } else { Err("Invalid return value!".into()) },
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
		let ext = call_wasm_method::<HostFunctions>("test_set_storage");

		let expected = "world";
		assert_eq!(expected.as_bytes(), &ext.storage("hello".as_bytes()).unwrap()[..]);
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
	#[should_panic(expected = "Wasmi(Instantiation(\"Export ext_test_api_return_input not found\"))")]
	fn host_function_not_found() {
		call_wasm_method::<()>("test_return_data");
	}
}
