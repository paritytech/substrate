// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use super::Runtime;
use crate::exec::Ext;

use sp_sandbox::Value;
use parity_wasm::elements::{FunctionType, ValueType};

#[macro_use]
pub(crate) mod macros;

pub trait ConvertibleToWasm: Sized {
	const VALUE_TYPE: ValueType;
	type NativeType;
	fn to_typed_value(self) -> Value;
	fn from_typed_value(_: Value) -> Option<Self>;
}
impl ConvertibleToWasm for i32 {
	type NativeType = i32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> Value {
		Value::I32(self)
	}
	fn from_typed_value(v: Value) -> Option<Self> {
		v.as_i32()
	}
}
impl ConvertibleToWasm for u32 {
	type NativeType = u32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> Value {
		Value::I32(self as i32)
	}
	fn from_typed_value(v: Value) -> Option<Self> {
		match v {
			Value::I32(v) => Some(v as u32),
			_ => None,
		}
	}
}
impl ConvertibleToWasm for u64 {
	type NativeType = u64;
	const VALUE_TYPE: ValueType = ValueType::I64;
	fn to_typed_value(self) -> Value {
		Value::I64(self as i64)
	}
	fn from_typed_value(v: Value) -> Option<Self> {
		match v {
			Value::I64(v) => Some(v as u64),
			_ => None,
		}
	}
}

pub(crate) type HostFunc<E> =
	fn(
		&mut Runtime<E>,
		&[sp_sandbox::Value]
	) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError>;

pub(crate) trait FunctionImplProvider<E: Ext> {
	fn impls<F: FnMut(&[u8], HostFunc<E>)>(f: &mut F);
}

/// This trait can be used to check whether the host environment can satisfy
/// a requested function import.
pub trait ImportSatisfyCheck {
	/// Returns `true` if the host environment contains a function with
	/// the specified name and its type matches to the given type, or `false`
	/// otherwise.
	fn can_satisfy(name: &[u8], func_type: &FunctionType) -> bool;
}
