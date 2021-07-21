// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error("Unserializable data encountered")]
	InvalidData(#[from] sp_serializer::Error),

	#[error(transparent)]
	Trap(#[from] wasmi::Trap),

	#[error(transparent)]
	Wasmi(#[from] wasmi::Error),

	#[error("Error calling api function: {0}")]
	ApiError(Box<dyn std::error::Error + Send + Sync>),

	#[error("Method not found: '{0}'")]
	MethodNotFound(String),

	#[error("Invalid Code (expected single byte): '{0}'")]
	InvalidCode(String),

	#[error("On-chain runtime does not specify version")]
	VersionInvalid,

	#[error("Externalities error")]
	Externalities,

	#[error("Invalid index provided")]
	InvalidIndex,

	#[error("Invalid type returned (should be u64)")]
	InvalidReturn,

	#[error("Runtime error")]
	Runtime,

	#[error("Runtime panicked: {0}")]
	RuntimePanicked(String),

	#[error("Invalid memory reference")]
	InvalidMemoryReference,

	#[error("The runtime doesn't provide a global named `__heap_base` of type `i32`")]
	HeapBaseNotFoundOrInvalid,

	#[error("The runtime must not have the `start` function defined")]
	RuntimeHasStartFn,

	#[error("Other: {0}")]
	Other(String),

	#[error(transparent)]
	Allocator(#[from] sc_allocator::Error),

	#[error("Host function {0} execution failed with: {1}")]
	FunctionExecution(String, String),

	#[error("No table exported by wasm blob")]
	NoTable,

	#[error("No table entry with index {0} in wasm blob exported table")]
	NoTableEntryWithIndex(u32),

	#[error("Table element with index {0} is not a function in wasm blob exported table")]
	TableElementIsNotAFunction(u32),

	#[error("Table entry with index {0} in wasm blob is null")]
	FunctionRefIsNull(u32),

	#[error(transparent)]
	RuntimeConstruction(#[from] WasmError),

	#[error("Shared memory is not supported")]
	SharedMemUnsupported,

	#[error("Imported globals are not supported yet")]
	ImportedGlobalsUnsupported,

	#[error("initializer expression can have only up to 2 expressions in wasm 1.0")]
	InitializerHasTooManyExpressions,

	#[error("Invalid initializer expression provided {0}")]
	InvalidInitializerExpression(String),
}

impl wasmi::HostError for Error {}

impl From<&'static str> for Error {
	fn from(err: &'static str) -> Error {
		Error::Other(err.into())
	}
}

impl From<String> for Error {
	fn from(err: String) -> Error {
		Error::Other(err)
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

impl std::error::Error for WasmError {}
