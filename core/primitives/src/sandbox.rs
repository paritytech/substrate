// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Definition of a sandbox environment.

use parity_codec::{Encode, Decode};
use rstd::vec::Vec;

/// Error error that can be returned from host function.
#[derive(Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct HostError;

/// Representation of a typed wasm value.
#[derive(Clone, Copy, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum TypedValue {
	/// Value of 32-bit signed or unsigned integer.
	#[codec(index = "1")]
	I32(i32),

	/// Value of 64-bit signed or unsigned integer.
	#[codec(index = "2")]
	I64(i64),

	/// Value of 32-bit IEEE 754-2008 floating point number represented as a bit pattern.
	#[codec(index = "3")]
	F32(i32),

	/// Value of 64-bit IEEE 754-2008 floating point number represented as a bit pattern.
	#[codec(index = "4")]
	F64(i64),
}

impl TypedValue {
	/// Returns `Some` if this value of type `I32`.
	pub fn as_i32(&self) -> Option<i32> {
		match *self {
			TypedValue::I32(v) => Some(v),
			_ => None,
		}
	}
}

#[cfg(feature = "std")]
impl From<::wasmi::RuntimeValue> for TypedValue {
	fn from(val: ::wasmi::RuntimeValue) -> TypedValue {
		use ::wasmi::RuntimeValue;
		match val {
			RuntimeValue::I32(v) => TypedValue::I32(v),
			RuntimeValue::I64(v) => TypedValue::I64(v),
			RuntimeValue::F32(v) => TypedValue::F32(v.to_bits() as i32),
			RuntimeValue::F64(v) => TypedValue::F64(v.to_bits() as i64),
		}
	}
}

#[cfg(feature = "std")]
impl From<TypedValue> for ::wasmi::RuntimeValue {
	fn from(val: TypedValue) -> ::wasmi::RuntimeValue {
		use ::wasmi::RuntimeValue;
		use ::wasmi::nan_preserving_float::{F32, F64};
		match val {
			TypedValue::I32(v) => RuntimeValue::I32(v),
			TypedValue::I64(v) => RuntimeValue::I64(v),
			TypedValue::F32(v_bits) => RuntimeValue::F32(F32::from_bits(v_bits as u32)),
			TypedValue::F64(v_bits) => RuntimeValue::F64(F64::from_bits(v_bits as u64)),
		}
	}
}

/// Typed value that can be returned from a function.
///
/// Basically a `TypedValue` plus `Unit`, for functions which return nothing.
#[derive(Clone, Copy, PartialEq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum ReturnValue {
	/// For returning nothing.
	Unit,
	/// For returning some concrete value.
	Value(TypedValue),
}

impl From<TypedValue> for ReturnValue {
	fn from(v: TypedValue) -> ReturnValue {
		ReturnValue::Value(v)
	}
}

impl ReturnValue {
	/// Maximum number of bytes `ReturnValue` might occupy when serialized with
	/// `Codec`.
	///
	/// Breakdown:
	///  1 byte for encoding unit/value variant
	///  1 byte for encoding value type
	///  8 bytes for encoding the biggest value types available in wasm: f64, i64.
	pub const ENCODED_MAX_SIZE: usize = 10;
}

#[test]
fn return_value_encoded_max_size() {
	let encoded = ReturnValue::Value(TypedValue::I64(-1)).encode();
	assert_eq!(encoded.len(), ReturnValue::ENCODED_MAX_SIZE);
}

/// Describes an entity to define or import into the environment.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum ExternEntity {
	/// Function that is specified by an index in a default table of
	/// a module that creates the sandbox.
	#[codec(index = "1")]
	Function(u32),

	/// Linear memory that is specified by some identifier returned by sandbox
	/// module upon creation new sandboxed memory.
	#[codec(index = "2")]
	Memory(u32),
}

/// An entry in a environment definition table.
///
/// Each entry has a two-level name and description of an entity
/// being defined.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Entry {
	/// Module name of which corresponding entity being defined.
	pub module_name: Vec<u8>,
	/// Field name in which corresponding entity being defined.
	pub field_name: Vec<u8>,
	/// External entity being defined.
	pub entity: ExternEntity,
}

/// Definition of runtime that could be used by sandboxed code.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct EnvironmentDefinition {
	/// Vector of all entries in the environment definition.
	pub entries: Vec<Entry>,
}

/// Constant for specifying no limit when creating a sandboxed
/// memory instance. For FFI purposes.
pub const MEM_UNLIMITED: u32 = -1i32 as u32;

/// No error happened.
///
/// For FFI purposes.
pub const ERR_OK: u32 = 0;

/// Validation or instantiation error occurred when creating new
/// sandboxed module instance.
///
/// For FFI purposes.
pub const ERR_MODULE: u32 = -1i32 as u32;

/// Out-of-bounds access attempted with memory or table.
///
/// For FFI purposes.
pub const ERR_OUT_OF_BOUNDS: u32 = -2i32 as u32;

/// Execution error occurred (typically trap).
///
/// For FFI purposes.
pub const ERR_EXECUTION: u32 = -3i32 as u32;

#[cfg(test)]
mod tests {
	use super::*;
	use std::fmt;
	use parity_codec::Codec;

	fn roundtrip<S: Codec + PartialEq + fmt::Debug>(s: S) {
		let encoded = s.encode();
		assert_eq!(S::decode(&mut &encoded[..]).unwrap(), s);
	}

	#[test]
	fn env_def_roundtrip() {
		roundtrip(EnvironmentDefinition {
			entries: vec![],
		});

		roundtrip(EnvironmentDefinition {
			entries: vec![
				Entry {
					module_name: b"kernel"[..].into(),
					field_name: b"memory"[..].into(),
					entity: ExternEntity::Memory(1337),
				},
			],
		});

		roundtrip(EnvironmentDefinition {
			entries: vec![
				Entry {
					module_name: b"env"[..].into(),
					field_name: b"abort"[..].into(),
					entity: ExternEntity::Function(228),
				},
			],
		});
	}
}
