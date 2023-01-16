// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

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
#![recursion_limit = "128"]

#[macro_use]
mod native_executor;
#[cfg(test)]
mod integration_tests;
mod wasm_runtime;

pub use codec::Codec;
pub use native_executor::{
	with_externalities_safe, NativeElseWasmExecutor, NativeExecutionDispatch, WasmExecutor,
};
#[doc(hidden)]
pub use sp_core::traits::Externalities;
pub use sp_version::{NativeVersion, RuntimeVersion};
#[doc(hidden)]
pub use sp_wasm_interface;
pub use wasm_runtime::{read_embedded_version, WasmExecutionMethod};
pub use wasmi;

pub use sc_executor_common::error;
pub use sc_executor_wasmtime::InstantiationStrategy as WasmtimeInstantiationStrategy;

/// Extracts the runtime version of a given runtime code.
pub trait RuntimeVersionOf {
	/// Extract [`RuntimeVersion`](sp_version::RuntimeVersion) of the given `runtime_code`.
	fn runtime_version(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &sp_core::traits::RuntimeCode,
	) -> error::Result<RuntimeVersion>;
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_executor_common::runtime_blob::RuntimeBlob;
	use sc_runtime_test::wasm_binary_unwrap;
	use sp_io::TestExternalities;

	#[test]
	fn call_in_interpreted_wasm_works() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();

		let executor = WasmExecutor::<sp_io::SubstrateHostFunctions>::new(
			WasmExecutionMethod::Interpreted,
			Some(8),
			8,
			None,
			2,
		);
		let res = executor
			.uncached_call(
				RuntimeBlob::uncompress_if_needed(wasm_binary_unwrap()).unwrap(),
				&mut ext,
				true,
				"test_empty_return",
				&[],
			)
			.unwrap();
		assert_eq!(res, vec![0u8; 0]);
	}
}
