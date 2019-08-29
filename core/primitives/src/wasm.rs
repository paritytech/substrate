// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Common traits and types for working with Wasm in Substrate.

use std::borrow::Cow;

/// Value types supported by Substrate on the boundary between host/Wasm.
#[derive(Copy, Clone, PartialEq)]
pub enum ValueType {
	/// An `i32` value type.
	I32,
	/// An `i64` value type.
	I64,
}

/// Values supported by Substrate on the boundary between host/Wasm.
pub enum Value {
	/// An `i32` value.
	I32(i32),
	/// An `i64` value.
	I64(i64),
}

/// The Signature of a function
pub struct Signature {
	/// The arguments of a function.
	pub args: Cow<'static, [ValueType]>,
	/// The optional return value of a function.
	pub return_value: Option<ValueType>,
}

impl Signature {
	/// Create a new instance of `Signature`.
	pub fn new<T: Into<Cow<'static, [ValueType]>>>(args: T, return_value: Option<ValueType>) -> Self {
		Self {
			args: args.into(),
			return_value,
		}
	}

	/// Create a new instance of `Signature` with the given `args` and without any return value.
	pub fn new_with_args<T: Into<Cow<'static, [ValueType]>>>(args: T) -> Self {
		Self {
			args: args.into(),
			return_value: None,
		}
	}

}

/// A reference to a host function.
pub struct FunctionRef {
	/// The signature of the function.
	pub signature: Signature,
	/// The index of the function at the host.
	pub index: usize,
}

impl FunctionRef {
	/// Create a new instance of `FunctionRef`.
	pub fn new(signature: Signature, index: usize) -> Self {
		Self {
			signature,
			index,
		}
	}
}

/// Something that has access to the Wasm memory with read/write access.
pub trait Memory {
	/// Read memory from `address` into a vector.
	fn read(&self, address: usize, size: usize) -> Result<Vec<u8>, String>;
	/// Write the given data at `address` into the memory.
	fn write(&mut self, address: usize, data: &[u8]) -> Result<(), String>;
	/// Allocate a memory instance of `size` bytes.
	fn alloc(&mut self, size: usize) -> Result<usize, String>;
}

/// Something that provides implementations for host functions.
pub trait Externals {
	/// Try to resolve the function with the given name and signature.
	fn resolve_function(name: &str, signature: &Signature) -> Option<FunctionRef>;

	/// Execute the function at the given index.
	///
	/// - `index` - Is equal to the index given to `FunctionRef`.
	/// - `args` - The arguments given to the function.
	/// - `memory` - Provides access to the Wasm memory.
	fn execute_function(index: usize, args: &[()], memory: &mut dyn Memory) -> Result<Option<Value>, String>;
}