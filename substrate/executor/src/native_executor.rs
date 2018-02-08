// Copyright 2017 Parity Technologies (UK) Ltd.
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

use error::{Error, Result};
use state_machine::{Externalities, CodeExecutor};
use wasm_executor::WasmExecutor;

/// Delegate for dispatching a CodeExecutor call to native code.
pub trait NativeExecutionDispatch {
	/// Get the wasm code that the native dispatch will be equivalent to.
	fn native_equivalent() -> &'static [u8];

	/// Dispatch a method and input data to be executed natively. Returns `Some` result or `None`
	/// if the `method` is unknown. Panics if there's an unrecoverable error.
	fn dispatch(ext: &mut Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>>;
}

/// A generic `CodeExecutor` implementation that uses a delegate to determine wasm code equivalence
/// and dispatch to native code when possible, falling back on `WasmExecutor` when not.
pub struct NativeExecutor<D: NativeExecutionDispatch + Sync + Send> {
	/// Dummy field to avoid the compiler complaining about us not using `D`.
	pub _dummy: ::std::marker::PhantomData<D>,
}

impl<D: NativeExecutionDispatch + Sync + Send> CodeExecutor for NativeExecutor<D> {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &[u8],
	) -> Result<Vec<u8>> {
		if code == D::native_equivalent() {
			// call native
			D::dispatch(ext, method, data)
		} else {
			// call into wasm.
			WasmExecutor.call(ext, code, method, data)
		}
	}
}
