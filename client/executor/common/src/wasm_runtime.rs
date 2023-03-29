// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Definitions for a wasm runtime.

use crate::error::Error;
use sp_wasm_interface::Value;

pub use sc_allocator::AllocationStats;

/// Default heap allocation strategy.
pub const DEFAULT_HEAP_ALLOC_STRATEGY: HeapAllocStrategy =
	HeapAllocStrategy::Static { extra_pages: DEFAULT_HEAP_ALLOC_PAGES };

/// Default heap allocation pages.
pub const DEFAULT_HEAP_ALLOC_PAGES: u32 = 2048;

/// A method to be used to find the entrypoint when calling into the runtime
///
/// Contains variants on how to resolve wasm function that will be invoked.
pub enum InvokeMethod<'a> {
	/// Call function exported with this name.
	///
	/// Located function should have (u32, u32) -> u64 signature.
	Export(&'a str),
	/// Call a function found in the exported table found under the given index.
	///
	/// Located function should have (u32, u32) -> u64 signature.
	Table(u32),
	/// Call function by reference from table through a wrapper.
	///
	/// Invoked function (`dispatcher_ref`) function
	/// should have (u32, u32, u32) -> u64 signature.
	///
	/// `func` will be passed to the invoked function as a first argument.
	TableWithWrapper {
		/// Wrapper for the call.
		///
		/// Function pointer, index into runtime exported table.
		dispatcher_ref: u32,
		/// Extra argument for dispatch.
		///
		/// Common usage would be to use it as an actual wasm function pointer
		/// that should be invoked, but can be used as any extra argument on the
		/// callee side.
		///
		/// This is typically generated and invoked by the runtime itself.
		func: u32,
	},
}

impl<'a> From<&'a str> for InvokeMethod<'a> {
	fn from(val: &'a str) -> InvokeMethod<'a> {
		InvokeMethod::Export(val)
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
	fn call(&mut self, method: InvokeMethod, data: &[u8]) -> Result<Vec<u8>, Error> {
		self.call_with_allocation_stats(method, data).0
	}

	/// Call a method on this WASM instance.
	///
	/// Before execution, instance is reset.
	///
	/// Returns the encoded result on success.
	fn call_with_allocation_stats(
		&mut self,
		method: InvokeMethod,
		data: &[u8],
	) -> (Result<Vec<u8>, Error>, Option<AllocationStats>);

	/// Call an exported method on this WASM instance.
	///
	/// Before execution, instance is reset.
	///
	/// Returns the encoded result on success.
	fn call_export(&mut self, method: &str, data: &[u8]) -> Result<Vec<u8>, Error> {
		self.call(method.into(), data)
	}

	/// Get the value from a global with the given `name`.
	///
	/// This method is only suitable for getting immutable globals.
	fn get_global_const(&mut self, name: &str) -> Result<Option<Value>, Error>;

	/// **Testing Only**. This function returns the base address of the linear memory.
	///
	/// This is meant to be the starting address of the memory mapped area for the linear memory.
	///
	/// This function is intended only for a specific test that measures physical memory
	/// consumption.
	fn linear_memory_base_ptr(&self) -> Option<*const u8> {
		None
	}
}

/// Defines the heap pages allocation strategy the wasm runtime should use.
///
/// A heap page is defined as 64KiB of memory.
#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum HeapAllocStrategy {
	/// Allocate a static number of heap pages.
	///
	/// The total number of allocated heap pages is the initial number of heap pages requested by
	/// the wasm file plus the `extra_pages`.
	Static {
		/// The number of pages that will be added on top of the initial heap pages requested by
		/// the wasm file.
		extra_pages: u32,
	},
	/// Allocate the initial heap pages as requested by the wasm file and then allow it to grow
	/// dynamically.
	Dynamic {
		/// The absolute maximum size of the linear memory (in pages).
		///
		/// When `Some(_)` the linear memory will be allowed to grow up to this limit.
		/// When `None` the linear memory will be allowed to grow up to the maximum limit supported
		/// by WASM (4GB).
		maximum_pages: Option<u32>,
	},
}
