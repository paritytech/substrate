// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::runtime::StoreData;
use sc_executor_common::{
	error::{Error, Result},
	util::checked_range,
};
use sp_wasm_interface::{Pointer, Value};
use wasmtime::{AsContext, AsContextMut};

/// Converts a [`wasmtime::Val`] into a substrate runtime interface [`Value`].
///
/// Panics if the given value doesn't have a corresponding variant in `Value`.
pub fn from_wasmtime_val(val: wasmtime::Val) -> Value {
	match val {
		wasmtime::Val::I32(v) => Value::I32(v),
		wasmtime::Val::I64(v) => Value::I64(v),
		wasmtime::Val::F32(f_bits) => Value::F32(f_bits),
		wasmtime::Val::F64(f_bits) => Value::F64(f_bits),
		v => panic!("Given value type is unsupported by Substrate: {:?}", v),
	}
}

/// Converts a sp_wasm_interface's [`Value`] into the corresponding variant in wasmtime's
/// [`wasmtime::Val`].
pub fn into_wasmtime_val(value: Value) -> wasmtime::Val {
	match value {
		Value::I32(v) => wasmtime::Val::I32(v),
		Value::I64(v) => wasmtime::Val::I64(v),
		Value::F32(f_bits) => wasmtime::Val::F32(f_bits),
		Value::F64(f_bits) => wasmtime::Val::F64(f_bits),
	}
}

/// Read data from a slice of memory into a newly allocated buffer.
///
/// Returns an error if the read would go out of the memory bounds.
pub(crate) fn read_memory(
	ctx: impl AsContext<Data = StoreData>,
	source_addr: Pointer<u8>,
	size: usize,
) -> Result<Vec<u8>> {
	let range =
		checked_range(source_addr.into(), size, ctx.as_context().data().memory().data_size(&ctx))
			.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;

	let mut buffer = vec![0; range.len()];
	read_memory_into(ctx, source_addr, &mut buffer)?;

	Ok(buffer)
}

/// Read data from the instance memory into a slice.
///
/// Returns an error if the read would go out of the memory bounds.
pub(crate) fn read_memory_into(
	ctx: impl AsContext<Data = StoreData>,
	address: Pointer<u8>,
	dest: &mut [u8],
) -> Result<()> {
	let memory = ctx.as_context().data().memory().data(&ctx);

	let range = checked_range(address.into(), dest.len(), memory.len())
		.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;
	dest.copy_from_slice(&memory[range]);
	Ok(())
}

/// Write data to the instance memory from a slice.
///
/// Returns an error if the write would go out of the memory bounds.
pub(crate) fn write_memory_from(
	mut ctx: impl AsContextMut<Data = StoreData>,
	address: Pointer<u8>,
	data: &[u8],
) -> Result<()> {
	let memory = ctx.as_context().data().memory();
	let memory = memory.data_mut(&mut ctx);

	let range = checked_range(address.into(), data.len(), memory.len())
		.ok_or_else(|| Error::Other("memory write is out of bounds".into()))?;
	memory[range].copy_from_slice(data);
	Ok(())
}
