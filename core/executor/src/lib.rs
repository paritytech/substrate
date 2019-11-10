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

//! A crate that provides means of executing/dispatching calls into the runtime.
//!
//! There are a few responsibilities of this crate at the moment:
//!
//! - It provides an implementation of a common entrypoint for calling into the runtime, both
//! wasm and compiled.
//! - It defines the environment for the wasm execution, namely the host functions that are to be
//! provided into the wasm runtime module.
//! - It also provides the required infrastructure for executing the current wasm runtime (specified
//! by the current value of `:code` in the provided externalities), i.e. interfacing with
//! wasm engine used, instance cache.

#![warn(missing_docs)]
#![recursion_limit="128"]

#[macro_use]
mod wasm_utils;
mod wasmi_execution;
#[macro_use]
mod native_executor;
mod sandbox;
mod allocator;
pub mod deprecated_host_interface;
mod wasm_runtime;
#[cfg(feature = "wasmtime")]
mod wasmtime;
#[cfg(test)]
mod integration_tests;

pub mod error;
pub use wasmi;
pub use native_executor::{with_native_environment, NativeExecutor, NativeExecutionDispatch};
pub use runtime_version::{RuntimeVersion, NativeVersion};
pub use codec::Codec;
#[doc(hidden)]
pub use primitives::traits::Externalities;
#[doc(hidden)]
pub use wasm_interface;
pub use wasm_runtime::WasmExecutionMethod;

/// Call the given `function` in the given wasm `code`.
///
/// The signature of `function` needs to follow the default Substrate function signature.
///
/// - `call_data`: Will be given as input parameters to `function`
/// - `execution_method`: The execution method to use.
/// - `ext`: The externalities that should be set while executing the wasm function.
/// - `heap_pages`: The number of heap pages to allocate.
///
/// Returns the `Vec<u8>` that contains the return value of the function.
pub fn call_in_wasm<E: Externalities, HF: wasm_interface::HostFunctions>(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut E,
	code: &[u8],
	heap_pages: u64,
) -> error::Result<Vec<u8>> {
	let mut instance = wasm_runtime::create_wasm_runtime_with_code(
		execution_method,
		heap_pages,
		code,
		HF::host_functions(),
	)?;
	instance.call(ext, function, call_data)
}

/// Provides runtime information.
pub trait RuntimeInfo {
	/// Native runtime information.
	fn native_version(&self) -> &NativeVersion;

	/// Extract RuntimeVersion of given :code block
	fn runtime_version<E: Externalities> (
		&self,
		ext: &mut E,
	) -> Option<RuntimeVersion>;
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_test::WASM_BINARY;
	use runtime_io::TestExternalities;

	#[test]
	fn call_in_interpreted_wasm_works() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let res = call_in_wasm::<_, runtime_io::SubstrateHostFunctions>(
			"test_empty_return",
			&[],
			WasmExecutionMethod::Interpreted,
			&mut ext,
			&WASM_BINARY,
			8,
		).unwrap();
		assert_eq!(res, vec![0u8; 0]);
	}
}
