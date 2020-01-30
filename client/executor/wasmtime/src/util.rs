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

use sc_executor_common::error::{Error, Result};

use cranelift_codegen::{ir, isa};
use std::ops::Range;
use sp_wasm_interface::{Pointer, Signature, ValueType};

/// Read data from a slice of memory into a destination buffer.
///
/// Returns an error if the read would go out of the memory bounds.
pub fn read_memory_into(memory: &[u8], address: Pointer<u8>, dest: &mut [u8]) -> Result<()> {
	let range = checked_range(address.into(), dest.len(), memory.len())
		.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;
	dest.copy_from_slice(&memory[range]);
	Ok(())
}

/// Write data to a slice of memory.
///
/// Returns an error if the write would go out of the memory bounds.
pub fn write_memory_from(memory: &mut [u8], address: Pointer<u8>, data: &[u8]) -> Result<()> {
	let range = checked_range(address.into(), data.len(), memory.len())
		.ok_or_else(|| Error::Other("memory write is out of bounds".into()))?;
	&mut memory[range].copy_from_slice(data);
	Ok(())
}

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

/// Convert from a parity wasm FunctionType to wasm interface's Signature.
pub fn convert_parity_wasm_signature(func_ty: &parity_wasm::elements::FunctionType) -> Signature {
	fn convert_value_type(val_ty: parity_wasm::elements::ValueType) -> ValueType {
		use parity_wasm::elements::ValueType::*;
		match val_ty {
			I32 => ValueType::I32,
			I64 => ValueType::I64,
			F32 => ValueType::F32,
			F64 => ValueType::F64,
		}
	}

	Signature::new(
		func_ty.params().iter().cloned().map(convert_value_type).collect::<Vec<_>>(),
		func_ty.return_type().map(convert_value_type),
	)
}

/// Convert a wasm_interface Signature into a cranelift_codegen Signature.
pub fn cranelift_ir_signature(signature: Signature, call_conv: &isa::CallConv) -> ir::Signature {
	ir::Signature {
		params: signature.args.iter()
			.map(cranelift_ir_type)
			.map(ir::AbiParam::new)
			.collect(),
		returns: signature.return_value.iter()
			.map(cranelift_ir_type)
			.map(ir::AbiParam::new)
			.collect(),
		call_conv: call_conv.clone(),
	}
}

/// Convert a wasm_interface ValueType into a cranelift_codegen Type.
pub fn cranelift_ir_type(value_type: &ValueType) -> ir::types::Type {
	match value_type {
		ValueType::I32 => ir::types::I32,
		ValueType::I64 => ir::types::I64,
		ValueType::F32 => ir::types::F32,
		ValueType::F64 => ir::types::F64,
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use assert_matches::assert_matches;

	#[test]
	fn test_read_memory_into() {
		let mut memory = [0; 20];
		let mut dest = [0; 5];

		&mut memory[15..20].copy_from_slice(b"hello");

		read_memory_into(&memory[..], Pointer::new(15), &mut dest[..]).unwrap();

		// Test that out of bounds read fails.
		assert_matches!(
			read_memory_into(&memory[..], Pointer::new(16), &mut dest[..]),
			Err(Error::Other(_))
		)
	}

	#[test]
	fn test_write_memory_from() {
		let mut memory = [0; 20];
		let data = b"hello";

		write_memory_from(&mut memory[..], Pointer::new(15), data).unwrap();

		// Test that out of bounds write fails.
		assert_matches!(
			write_memory_from(&mut memory[..], Pointer::new(16), data),
			Err(Error::Other(_))
		)
	}
}
