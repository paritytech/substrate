// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Rust executor possible errors.

use sp_serializer;
use wasmi;

#[cfg(feature = "std")]
pub type ErrorInfo = String;

#[cfg(not(feature = "std"))]
pub type ErrorInfo = ();

/// Result type alias.
pub type Result<T> = sp_std::result::Result<T, Error>;

/// Error type.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(derive_more::Display, derive_more::From))]
pub enum Error {
	/// Unserializable Data
	InvalidData(sp_serializer::Error),
	/// Trap occurred during execution
	Trap(wasmi::Trap),
	/// Wasmi loading/instantiating error
	Wasmi(wasmi::Error),
	/// Error in the API. Parameter is an error message.
	#[cfg_attr(feature = "std", from(ignore))]
	ApiError(ErrorInfo),
	/// Method is not found
	#[cfg_attr(feature = "std", display(fmt="Method not found: '{}'", _0))]
	#[cfg_attr(feature = "std", from(ignore))]
	MethodNotFound(ErrorInfo),
	/// Code is invalid (expected single byte)
	#[cfg_attr(feature = "std", display(fmt="Invalid Code: {}", _0))]
	#[cfg_attr(feature = "std", from(ignore))]
	InvalidCode(ErrorInfo),
	/// Could not get runtime version.
	#[cfg_attr(feature = "std", display(fmt="On-chain runtime does not specify version"))]
	VersionInvalid,
	/// Externalities have failed.
	#[cfg_attr(feature = "std", display(fmt="Externalities error"))]
	Externalities,
	/// Invalid index.
	#[cfg_attr(feature = "std", display(fmt="Invalid index provided"))]
	InvalidIndex,
	/// Invalid return type.
	#[cfg_attr(feature = "std", display(fmt="Invalid type returned (should be u64)"))]
	InvalidReturn,
	/// Runtime failed.
	#[cfg_attr(feature = "std", display(fmt="Runtime error"))]
	Runtime,
	/// Runtime panicked.
	#[display(fmt="Runtime panicked: {}", _0)]
	#[from(ignore)]
	RuntimePanicked(ErrorInfo),
	/// Invalid memory reference.
	#[display(fmt="Invalid memory reference")]
	InvalidMemoryReference,
	/// The runtime must provide a global named `__heap_base` of type i32 for specifying where the
	/// allocator is allowed to place its data.
	#[display(fmt="The runtime doesn't provide a global named `__heap_base`")]
	HeapBaseNotFoundOrInvalid,
	/// The runtime WebAssembly module is not allowed to have the `start` function.
	#[display(fmt="The runtime has the `start` function")]
	RuntimeHasStartFn,
	/// Some other error occurred
	Other(ErrorInfo),
	/// Some error occurred in the allocator
	#[cfg_attr(feature = "std", display(fmt="Error in allocator: {}", _0))]
	Allocator(AllocatorError),
	/// Execution of a host function failed.
	#[display(fmt="Host function {} execution failed with: {}", _0, _1)]
	FunctionExecution(ErrorInfo, ErrorInfo),
	/// No table is present.
	///
	/// Call was requested that requires table but none was present in the instance.
	#[display(fmt="No table exported by wasm blob")]
	NoTable,
	/// No table entry is present.
	///
	/// Call was requested that requires specific entry in the table to be present.
	#[display(fmt="No table entry with index {} in wasm blob exported table", _0)]
	#[from(ignore)]
	NoTableEntryWithIndex(u32),
	/// Table entry is not a function.
	#[display(fmt="Table element with index {} is not a function in wasm blob exported table", _0)]
	#[from(ignore)]
	TableElementIsNotAFunction(u32),
	/// Function in table is null and thus cannot be called.
	#[display(fmt="Table entry with index {} in wasm blob is null", _0)]
	#[from(ignore)]
	FunctionRefIsNull(u32),
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			Error::InvalidData(ref err) => Some(err),
			Error::Trap(ref err) => Some(err),
			Error::Wasmi(ref err) => Some(err),
			_ => None,
		}
	}
}

#[cfg(feature = "std")]
impl wasmi::HostError for Error {}

#[cfg(feature = "std")]
impl From<&'static str> for Error {
	fn from(err: &'static str) -> Error {
		Error::Other(err.into())
	}
}

#[cfg(feature = "std")]
impl From<WasmError> for Error {
	fn from(err: WasmError) -> Error {
		Error::Other(err.to_string())
	}
}

/// Type for errors occurring during Wasm runtime construction.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(derive_more::Display))]
pub enum WasmError {
	/// Code could not be read from the state.
	CodeNotFound,
	/// Failure to reinitialize runtime instance from snapshot.
	ApplySnapshotFailed,
	/// Failure to erase the wasm memory.
	///
	/// Depending on the implementation might mean failure of allocating memory.
	ErasingFailed(ErrorInfo),
	/// Wasm code failed validation.
	InvalidModule,
	/// Wasm code could not be deserialized.
	CantDeserializeWasm,
	/// The module does not export a linear memory named `memory`.
	InvalidMemory,
	/// The number of heap pages requested is disallowed by the module.
	InvalidHeapPages,
	/// Instantiation error.
	Instantiation(ErrorInfo),
	/// Other error happenend.
	Other(ErrorInfo),
}

/// The error type used by the allocators.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(derive_more::Display))]
pub enum AllocatorError {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[cfg_attr(feature = "std", display(fmt="Requested allocation size is too large"))]
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	#[cfg_attr(feature = "std", display(fmt="Allocator ran out of space"))]
	AllocatorOutOfSpace,
	/// Some other error occurred.
	Other(&'static str)
}

#[cfg(feature = "std")]
impl std::error::Error for AllocatorError {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			_ => None,
		}
	}
}
