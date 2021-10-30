// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Implementation of conversions between Substrate and wasmi types.

use crate::{Signature, Value, ValueType};

impl From<Value> for wasmi::RuntimeValue {
	fn from(value: Value) -> Self {
		match value {
			Value::I32(val) => Self::I32(val),
			Value::I64(val) => Self::I64(val),
			Value::F32(val) => Self::F32(val.into()),
			Value::F64(val) => Self::F64(val.into()),
		}
	}
}

impl From<wasmi::RuntimeValue> for Value {
	fn from(value: wasmi::RuntimeValue) -> Self {
		match value {
			wasmi::RuntimeValue::I32(val) => Self::I32(val),
			wasmi::RuntimeValue::I64(val) => Self::I64(val),
			wasmi::RuntimeValue::F32(val) => Self::F32(val.into()),
			wasmi::RuntimeValue::F64(val) => Self::F64(val.into()),
		}
	}
}

impl From<ValueType> for wasmi::ValueType {
	fn from(value: ValueType) -> Self {
		match value {
			ValueType::I32 => Self::I32,
			ValueType::I64 => Self::I64,
			ValueType::F32 => Self::F32,
			ValueType::F64 => Self::F64,
		}
	}
}

impl From<wasmi::ValueType> for ValueType {
	fn from(value: wasmi::ValueType) -> Self {
		match value {
			wasmi::ValueType::I32 => Self::I32,
			wasmi::ValueType::I64 => Self::I64,
			wasmi::ValueType::F32 => Self::F32,
			wasmi::ValueType::F64 => Self::F64,
		}
	}
}

impl From<Signature> for wasmi::Signature {
	fn from(sig: Signature) -> Self {
		let args = sig.args.iter().map(|a| (*a).into()).collect::<Vec<_>>();
		wasmi::Signature::new(args, sig.return_value.map(Into::into))
	}
}

impl From<&wasmi::Signature> for Signature {
	fn from(sig: &wasmi::Signature) -> Self {
		Signature::new(
			sig.params().into_iter().copied().map(Into::into).collect::<Vec<_>>(),
			sig.return_type().map(Into::into),
		)
	}
}
