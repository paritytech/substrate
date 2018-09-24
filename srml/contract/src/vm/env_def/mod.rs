// Copyright 2018 Parity Technologies (UK) Ltd.
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

use super::{Ext, Runtime};
use parity_wasm::elements::{FunctionType, ValueType};
use rstd::prelude::*;
use rstd::collections::btree_map::BTreeMap;
use sandbox::{self, TypedValue};

#[macro_use]
pub(crate) mod macros;

pub trait ConvertibleToWasm: Sized {
	const VALUE_TYPE: ValueType;
	type NativeType;
	fn to_typed_value(self) -> TypedValue;
	fn from_typed_value(TypedValue) -> Option<Self>;
}
impl ConvertibleToWasm for i32 {
	type NativeType = i32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I32(self)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		v.as_i32()
	}
}
impl ConvertibleToWasm for u32 {
	type NativeType = u32;
	const VALUE_TYPE: ValueType = ValueType::I32;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I32(self as i32)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		match v {
			TypedValue::I32(v) => Some(v as u32),
			_ => None,
		}
	}
}
impl ConvertibleToWasm for u64 {
	type NativeType = u64;
	const VALUE_TYPE: ValueType = ValueType::I64;
	fn to_typed_value(self) -> TypedValue {
		TypedValue::I64(self as i64)
	}
	fn from_typed_value(v: TypedValue) -> Option<Self> {
		match v {
			TypedValue::I64(v) => Some(v as u64),
			_ => None,
		}
	}
}

/// Represents a set of function that defined in this particular environment and
/// which can be imported and called by the module.
pub(crate) struct HostFunctionSet<E: Ext> {
	/// Functions which defined in the environment.
	pub funcs: BTreeMap<Vec<u8>, HostFunction<E>>,
}
impl<E: Ext> HostFunctionSet<E> {
	pub fn new() -> Self {
		HostFunctionSet {
			funcs: BTreeMap::new(),
		}
	}
}

pub(crate) struct HostFunction<E: Ext> {
	pub(crate) f: fn(&mut Runtime<E>, &[sandbox::TypedValue])
		-> Result<sandbox::ReturnValue, sandbox::HostError>,
	func_type: FunctionType,
}
impl<E: Ext> HostFunction<E> {
	/// Create a new instance of a host function.
	pub fn new(
		func_type: FunctionType,
		f: fn(&mut Runtime<E>, &[sandbox::TypedValue])
			-> Result<sandbox::ReturnValue, sandbox::HostError>,
	) -> Self {
		HostFunction { func_type, f }
	}

	/// Returns a function pointer of this host function.
	pub fn raw_fn_ptr(
		&self,
	) -> fn(&mut Runtime<E>, &[sandbox::TypedValue])
		-> Result<sandbox::ReturnValue, sandbox::HostError> {
		self.f
	}

	/// Check if the this function could be invoked with the given function signature.
	pub fn func_type_matches(&self, func_type: &FunctionType) -> bool {
		&self.func_type == func_type
	}
}
