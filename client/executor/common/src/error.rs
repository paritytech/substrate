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

//! Rust executor possible errors.

use sp_serializer;
use wasmi;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Unserializable Data
	InvalidData(sp_serializer::Error),
	/// Trap occurred during execution
	Trap(wasmi::Trap),
	/// Wasmi loading/instantiating error
	Wasmi(wasmi::Error),
	/// Error in the API. Parameter is an error message.
	#[from(ignore)]
	ApiError(String),
	/// Method is not found
	#[display(fmt="Method not found: '{}'", _0)]
	#[from(ignore)]
	MethodNotFound(String),
	/// Code is invalid (expected single byte)
	#[display(fmt="Invalid Code: {}", _0)]
	#[from(ignore)]
	InvalidCode(String),
	/// Could not get runtime version.
	#[display(fmt="On-chain runtime does not specify version")]
	VersionInvalid,
	/// Externalities have failed.
	#[display(fmt="Externalities error")]
	Externalities,
	/// Invalid index.
	#[display(fmt="Invalid index provided")]
	InvalidIndex,
	/// Invalid return type.
	#[display(fmt="Invalid type returned (should be u64)")]
	InvalidReturn,
	/// Runtime failed.
	#[display(fmt="Runtime error")]
	Runtime,
	/// Runtime panicked.
	#[display(fmt="Runtime panicked: {}", _0)]
	#[from(ignore)]
	RuntimePanicked(String),
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
	Other(String),
	/// Some error occurred in the allocator
	#[display(fmt="Error in allocator: {}", _0)]
	Allocator(sp_allocator::Error),
	/// Execution of a host function failed.
	#[display(fmt="Host function {} execution failed with: {}", _0, _1)]
	FunctionExecution(String, String),
}

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

impl wasmi::HostError for Error {}

impl From<&'static str> for Error {
	fn from(err: &'static str) -> Error {
		Error::Other(err.into())
	}
}

impl From<WasmError> for Error {
	fn from(err: WasmError) -> Error {
		Error::Other(err.to_string())
	}
}

/// Type for errors occurring during Wasm runtime construction.
#[derive(Debug, derive_more::Display)]
pub enum WasmError {
	/// Code could not be read from the state.
	CodeNotFound,
	/// Failure to reinitialize runtime instance from snapshot.
	ApplySnapshotFailed,
	/// Failure to erase the wasm memory.
	///
	/// Depending on the implementation might mean failure of allocating memory.
	ErasingFailed(String),
	/// Wasm code failed validation.
	InvalidModule,
	/// Wasm code could not be deserialized.
	CantDeserializeWasm,
	/// The module does not export a linear memory named `memory`.
	InvalidMemory,
	/// The number of heap pages requested is disallowed by the module.
	InvalidHeapPages,
	/// Instantiation error.
	Instantiation(String),
	/// Other error happenend.
	Other(String),
}
