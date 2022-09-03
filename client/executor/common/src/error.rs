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

//! Rust executor possible errors.

use wasmi;

/// Result type alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error(transparent)]
	Wasmi(#[from] wasmi::Error),

	#[error("Sandbox error: {0}")]
	Sandbox(String),

	#[error("Error calling api function: {0}")]
	ApiError(Box<dyn std::error::Error + Send + Sync>),

	#[error("Method not found: '{0}'")]
	MethodNotFound(String),

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

	#[error("Execution aborted due to panic: {0}")]
	AbortedDueToPanic(MessageWithBacktrace),

	#[error("Execution aborted due to trap: {0}")]
	AbortedDueToTrap(MessageWithBacktrace),
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
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum WasmError {
	#[error("Code could not be read from the state.")]
	CodeNotFound,

	#[error("Failure to reinitialize runtime instance from snapshot.")]
	ApplySnapshotFailed,

	/// Failure to erase the wasm memory.
	///
	/// Depending on the implementation might mean failure of allocating memory.
	#[error("Failure to erase the wasm memory: {0}")]
	ErasingFailed(String),

	#[error("Wasm code failed validation.")]
	InvalidModule,

	#[error("Wasm code could not be deserialized.")]
	CantDeserializeWasm,

	#[error("The module does not export a linear memory named `memory`.")]
	InvalidMemory,

	#[error("The number of heap pages requested is disallowed by the module.")]
	InvalidHeapPages,

	/// Instantiation error.
	#[error("{0}")]
	Instantiation(String),

	/// Other error happenend.
	#[error("{0}")]
	Other(String),
}

/// An error message with an attached backtrace.
#[derive(Debug)]
pub struct MessageWithBacktrace {
	/// The error message.
	pub message: String,

	/// The backtrace associated with the error message.
	pub backtrace: Option<Backtrace>,
}

impl std::fmt::Display for MessageWithBacktrace {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.write_str(&self.message)?;
		if let Some(ref backtrace) = self.backtrace {
			fmt.write_str("\nWASM backtrace:\n")?;
			backtrace.backtrace_string.fmt(fmt)?;
		}

		Ok(())
	}
}

/// A WASM backtrace.
#[derive(Debug)]
pub struct Backtrace {
	/// The string containing the backtrace.
	pub backtrace_string: String,
}

impl std::fmt::Display for Backtrace {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.write_str(&self.backtrace_string)
	}
}
