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

//! Types and traits for interfacing between the host and the wasm runtime.

use std::borrow::Cow;

mod wasmi_impl;

/// Value types supported by Substrate on the boundary between host/Wasm.
#[derive(Copy, Clone, PartialEq, Debug, Eq)]
pub enum ValueType {
	/// An `i32` value type.
	I32,
	/// An `i64` value type.
	I64,
}

/// Values supported by Substrate on the boundary between host/Wasm.
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum Value {
	/// An `i32` value.
	I32(i32),
	/// An `i64` value.
	I64(i64),
}

/// The Signature of a function
#[derive(Eq, PartialEq, Debug)]
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
#[derive(Eq, PartialEq, Debug)]
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

/// Context used by `Externals` to interact with the allocator and the memory of the wasm instance.
pub trait ExternalsContext {
	/// Read memory from `address` into a vector.
	fn read_memory(&self, address: *const u8, size: u32) -> Result<Vec<u8>, String> {
		let mut vec = Vec::with_capacity(size as usize);
		self.read_memory_into(address, &mut vec)?;
		Ok(vec)
	}
	/// Read memory into the given `dest` buffer from `address`.
	fn read_memory_into(&self, address: *const u8, dest: &mut [u8]) -> Result<(), String>;
	/// Write the given data at `address` into the memory.
	fn write_memory(&mut self, address: *const u8, data: &[u8]) -> Result<(), String>;
	/// Allocate a memory instance of `size` bytes.
	fn allocate_memory(&mut self, size: u32) -> Result<*mut u8, String>;
	/// Deallocate a given memory instance.
	fn deallocate_memory(&mut self, ptr: *const u8) -> Result<(), String>;
}

/// Something that provides implementations for host functions.
pub trait Externals {
	/// Try to resolve the function with the given name and signature.
	fn resolve_function(name: &str, signature: &Signature) -> Result<Option<FunctionRef>, String>;

	/// Returns the number of host functions this type provides.
	fn function_count() -> usize;

	/// Execute the function at the given index.
	///
	/// - `index` - Is equal to the index given to `FunctionRef`.
	/// - `args` - The arguments given to the function.
	/// - `context` - Provides access to the allocator and memory of the memory wasm instance.
	fn execute_function<A: Iterator<Item=Value>>(
		index: usize,
		args: A,
		context: &mut dyn ExternalsContext,
	) -> Result<Option<Value>, String>;
}

/// Something that provides implementations for inherent host functions.
///
/// Will be used interanlly by Substrate to provide functions like `malloc`, `free` etc.
pub trait InherentExternals {
	/// Try to resolve the function with the given name and signature.
	fn resolve_function(name: &str, signature: &Signature) -> Result<Option<FunctionRef>, String>;

	/// Returns the number of host functions this type provides.
	fn function_count() -> usize;

	/// Execute the function at the given index.
	///
	/// - `index` - Is equal to the index given to `FunctionRef`.
	/// - `args` - The arguments given to the function.
	/// - `context` - Provides access to the allocator and memory of the memory wasm instance.
	fn execute_function<A: Iterator<Item=Value>>(
		&mut self,
		index: usize,
		args: A,
	) -> Result<Option<Value>, String>;
}

/// Something that can be converted into a wasm compatible `Value`.
pub trait IntoValue {
	/// The type of the value in wasm.
	const VALUE_TYPE: ValueType;

	/// Convert `self` into a wasm `Value`.
	fn into_value(self) -> Value;
}

/// Something that can may be created from a wasm `Value`.
pub trait TryFromValue: Sized {
	/// Try to convert the given `Value` into `Self`.
	fn try_from_value(val: Value) -> Option<Self>;
}

macro_rules! impl_into_and_from_value {
	(
		$(
			$type:ty, $( < $gen:ident >, )? $value_variant:ident,
		)*
	) => {
		$(
			impl $( <$gen> )? IntoValue for $type {
				const VALUE_TYPE: ValueType = ValueType::$value_variant;
				fn into_value(self) -> Value { Value::$value_variant(self as _) }
			}

			impl $( <$gen> )? TryFromValue for $type {
				fn try_from_value(val: Value) -> Option<Self> {
					match val {
						Value::$value_variant(val) => Some(val as _),
						_ => None,
					}
				}
			}
		)*
	}
}

impl_into_and_from_value! {
	u32, I32,
	i32, I32,
	u64, I64,
	i64, I64,
	*const T, <T>, I32,
	*mut T, <T>, I32,
}
