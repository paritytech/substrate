// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
#[macro_use]
mod native_executor;
pub mod deprecated_host_interface;
mod wasm_runtime;
#[cfg(test)]
mod integration_tests;

pub use wasmi;
pub use native_executor::{with_externalities_safe, NativeExecutor, NativeExecutionDispatch};
pub use sp_version::{RuntimeVersion, NativeVersion};
pub use codec::Codec;
#[doc(hidden)]
pub use sp_core::traits::Externalities;
#[doc(hidden)]
pub use sp_wasm_interface;
pub use wasm_runtime::WasmExecutionMethod;

pub use sc_executor_common::{error, sandbox};

/// Call the given `function` in the given wasm `code`.
///
/// The signature of `function` needs to follow the default Substrate function signature.
///
/// - `call_data`: Will be given as input parameters to `function`
/// - `execution_method`: The execution method to use.
/// - `ext`: The externalities that should be set while executing the wasm function.
///          If `None` is given, no externalities will be set.
/// - `heap_pages`: The number of heap pages to allocate.
///
/// Returns the `Vec<u8>` that contains the return value of the function.
pub fn call_in_wasm<HF: sp_wasm_interface::HostFunctions>(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut dyn Externalities,
	code: &[u8],
	heap_pages: u64,
	allow_missing_func_imports: bool,
) -> error::Result<Vec<u8>> {
	call_in_wasm_with_host_functions(
		function,
		call_data,
		execution_method,
		ext,
		code,
		heap_pages,
		HF::host_functions(),
		allow_missing_func_imports,
	)
}

/// Non-generic version of [`call_in_wasm`] that takes the `host_functions` as parameter.
/// For more information please see [`call_in_wasm`].
pub fn call_in_wasm_with_host_functions(
	function: &str,
	call_data: &[u8],
	execution_method: WasmExecutionMethod,
	ext: &mut dyn Externalities,
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn sp_wasm_interface::Function>,
	allow_missing_func_imports: bool,
) -> error::Result<Vec<u8>> {
	let instance = wasm_runtime::create_wasm_runtime_with_code(
		execution_method,
		heap_pages,
		code,
		host_functions,
		allow_missing_func_imports,
	)?;

	// It is safe, as we delete the instance afterwards.
	let mut instance = std::panic::AssertUnwindSafe(instance);

	with_externalities_safe(ext, move || instance.call(function, call_data)).and_then(|r| r)
}

/// Provides runtime information.
pub trait RuntimeInfo {
	/// Native runtime information.
	fn native_version(&self) -> &NativeVersion;

	/// Extract RuntimeVersion of given :code block
	fn runtime_version<E: Externalities> (&self, ext: &mut E) -> error::Result<RuntimeVersion>;
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_runtime_test::WASM_BINARY;
	use sp_io::TestExternalities;

	#[test]
	fn call_in_interpreted_wasm_works() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let res = call_in_wasm::<sp_io::SubstrateHostFunctions>(
			"test_empty_return",
			&[],
			WasmExecutionMethod::Interpreted,
			&mut ext,
			&WASM_BINARY,
			8,
			true,
		).unwrap();
		assert_eq!(res, vec![0u8; 0]);
	}
}
