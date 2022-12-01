// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::Runtime;
use crate::exec::Ext;

use pwasm_utils::parity_wasm::elements::{FunctionType, ValueType};
use sp_sandbox::Value;

#[macro_use]
pub mod macros;

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

pub type HostFunc<E> = fn(
	&mut Runtime<E>,
	&[sp_sandbox::Value],
) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError>;

pub trait FunctionImplProvider<E: Ext> {
	fn impls<F: FnMut(&[u8], &[u8], HostFunc<E>)>(f: &mut F);
}

/// This trait can be used to check whether the host environment can satisfy
/// a requested function import.
pub trait ImportSatisfyCheck {
	/// Returns `true` if the host environment contains a function with
	/// the specified name and its type matches to the given type, or `false`
	/// otherwise.
	fn can_satisfy(module: &[u8], name: &[u8], func_type: &FunctionType) -> bool;
}
