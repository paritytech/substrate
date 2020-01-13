// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Implementation of conversions between Substrate and wasmi types.

use crate::{Value, ValueType, Signature};

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
