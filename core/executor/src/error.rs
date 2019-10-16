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

//! Rust executor possible errors.

use serializer;
use wasmi;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Unserializable Data
	InvalidData(serializer::Error),
	/// Trap occured during execution
	Trap(wasmi::Trap),
	/// Wasmi loading/instantiating error
	Wasmi(wasmi::Error),
	/// Error in the API. Parameter is an error message.
	ApiError(String),
	/// Method is not found
	#[display(fmt="Method not found: '{}'", _0)]
	MethodNotFound(String),
	/// Code is invalid (expected single byte)
	#[display(fmt="Invalid Code: {}", _0)]
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
	Allocator(&'static str),
	/// The allocator ran out of space.
	#[display(fmt="Allocator ran out of space")]
	AllocatorOutOfSpace,
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[display(fmt="Requested allocation size is too large")]
	RequestedAllocationTooLarge,
	/// Executing the given function failed with the given error.
	#[display(fmt="Function execution failed with: {}", _0)]
	FunctionExecution(String),
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

impl From<String> for Error {
	fn from(err: String) -> Error {
		Error::Other(err)
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
	/// Wasm code failed validation.
	InvalidModule,
	/// Wasm code could not be deserialized.
	CantDeserializeWasm,
	/// Instantiation error.
	Instantiation(Error),
}
