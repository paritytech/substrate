// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use std::ops::Range;

use sp_wasm_interface::Value;
use wasmtime::Val;

/// Construct a range from an offset to a data length after the offset.
/// Returns None if the end of the range would exceed some maximum offset.
pub fn checked_range(offset: usize, len: usize, max: usize) -> Option<Range<usize>> {
	let end = offset.checked_add(len)?;
	if end <= max {
		Some(offset..end)
	} else {
		None
	}
}

/// Converts a `Val` into a substrate runtime interface `Value`.
///
/// Panics if the given value doesn't have a corresponding variant in `Value`.
pub fn from_wasmtime_val(val: Val) -> Value {
	match val {
		Val::I32(v) => Value::I32(v),
		Val::I64(v) => Value::I64(v),
		Val::F32(f_bits) => Value::F32(f_bits),
		Val::F64(f_bits) => Value::F64(f_bits),
		_ => panic!("Given value type is unsupported by substrate"),
	}
}

/// Converts a sp_wasm_interface's [`Value`] into the corresponding variant in wasmtime's [`Val`].
pub fn into_wasmtime_val(value: Value) -> wasmtime::Val {
	match value {
		Value::I32(v) => Val::I32(v),
		Value::I64(v) => Val::I64(v),
		Value::F32(f_bits) => Val::F32(f_bits),
		Value::F64(f_bits) => Val::F64(f_bits),
	}
}
