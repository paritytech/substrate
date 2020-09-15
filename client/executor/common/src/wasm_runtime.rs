// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Definitions for a wasm runtime.

use crate::error::Error;
use sp_wasm_interface::Value;

/// Call site.
///
/// Contains variants on how to resolve wasm function that will be invoked.
pub enum CallSite<'a> {
	/// Call function exported with this name.
	///
	/// Located function should have (u32, u32) -> u64 signature.
	Export(&'a str),
	/// Call function by reference from table.
	///
	/// Located function should have (u32, u32) -> u64 signature.
	Table(u32),
	/// Call function by reference from table through a wrapper.
	///
	/// Located function should have (u32, u32, u32) -> u64 signature.
	///
	/// `func` will be passed to the
	TableWithWrapper {
		/// Wrapper for call.
		dispatcher_ref: u32,
		/// Actual function index that should be invoked.
		func: u32,
	},
}

impl<'a> From<&'a str> for CallSite<'a> {
	fn from(val: &'a str) -> CallSite<'a> {
		CallSite::Export(val)
	}
}

/// A trait that defines an abstract WASM runtime module.
///
/// This can be implemented by an execution engine.
pub trait WasmModule: Sync + Send {
	/// Create a new instance.
	fn new_instance(&self) -> Result<Box<dyn WasmInstance>, Error>;
}

/// A trait that defines an abstract wasm module instance.
///
/// This can be implemented by an execution engine.
pub trait WasmInstance: Send {
	/// Call a method on this WASM instance.
	///
	/// Before execution, instance is reset.
	///
	/// Returns the encoded result on success.
	fn call(&self, call_site: CallSite, data: &[u8]) -> Result<Vec<u8>, Error>;

	/// Call an exported method on this WASM instance.
	///
	/// Before execution, instance is reset.
	///
	/// Returns the encoded result on success.
	fn call_export(&self, method: &str, data: &[u8]) -> Result<Vec<u8>, Error> {
		self.call(method.into(), data)
	}

	/// Get the value from a global with the given `name`.
	///
	/// This method is only suitable for getting immutable globals.
	fn get_global_const(&self, name: &str) -> Result<Option<Value>, Error>;
}
