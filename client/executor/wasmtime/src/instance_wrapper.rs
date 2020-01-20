// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Defines data and logic needed for interaction with an WebAssembly instance of a substrate
//! runtime module.

use std::ops::Range;
use std::slice;
use sc_executor_common::{
	error::{Error, Result},
};
use sp_wasm_interface::{Pointer, WordSize};
use wasmtime::{Instance, Memory, Table};

// TODO: Why do we need this?
pub struct InstanceWrapper {
	instance: Instance,
	memory: Memory,
	table: Option<Table>,
}

impl InstanceWrapper {
	pub unsafe fn new(instance: Instance) -> Result<Self> {
		Ok(Self {
			table: get_table(&instance),
			memory: get_linear_memory(&instance)?,
			instance,
		})
	}

	/// Increases the size of the linear memory attached to this instance.
	pub fn grow_memory(&self, pages: u32) -> Result<()> {
		if self.memory.grow(pages).is_ok() {
			Ok(())
		} else {
			return Err("failed top increase the linear memory size".into());
		}
	}

	/// Resolves a substrate entrypoint by the given name.
	///
	/// An entrypoint must have a signature `(i32, i32) -> i64`, otherwise this function will return
	/// an error.
	pub fn resolve_entrypoint(&self, name: &str) -> Result<wasmtime::Func> {
		// Resolve the requested method and verify that it has a proper signature.
		let export = self
			.instance
			.get_export(name)
			.ok_or_else(|| {
				Error::from(format!("Exported method {} is not found", name))
			})?;
		let entrypoint_func = export
			.func()
			.ok_or_else(|| Error::from(format!("Export {} is not a function", name)))?;
		// TODO: Check the signature
		Ok(entrypoint_func.clone())
	}

	/// Returns an indirect function table of this instance.
	pub fn table(&self) -> Option<&Table> {
		self.table.as_ref()
	}

	/// Returns the byte size of the linear memory instance attached to this instance.
	pub fn memory_size(&self) -> u32 {
		self.memory.data_size() as u32
	}

	/// Reads `__heap_base: i32` global variable and returns it.
	///
	/// If it doesn't exist, not a global or of not i32 type returns an error.
	pub fn extract_heap_base(&self) -> Result<u32> {
		let heap_base_export = self
			.instance
			.get_export("__heap_base")
			.ok_or_else(|| Error::from("__heap_base is not found"))?;

		let heap_base_global = heap_base_export
			.global()
			.ok_or_else(|| Error::from("__heap_base is not a global"))?;

		let heap_base = heap_base_global
			.get()
			.i32()
			.ok_or_else(|| Error::from("__heap_base is not a i32"))?;

		Ok(heap_base as u32)
	}
}

fn get_table(instance: &Instance) -> Option<Table> {
	instance
		.get_export("__indirect_function_table")
		.and_then(|export| export.table())
		.cloned()
}

fn get_linear_memory(instance: &Instance) -> Result<Memory> {
	let memory_export = instance
		.get_export("memory")
		.ok_or_else(|| Error::from("memory is not exported under `memory` name"))?;

	let memory = memory_export
		.memory()
		.ok_or_else(|| Error::from("the `memory` export should have memory type"))?
		.clone();

	Ok(memory)
}

/// Functions realted to memory.
impl InstanceWrapper {
	/// Read data from a slice of memory into a destination buffer.
	///
	/// Returns an error if the read would go out of the memory bounds.
	pub fn read_memory_into(&self, address: Pointer<u8>, dest: &mut [u8]) -> Result<()> {
		unsafe {
			// TODO: Proof
			let memory = self.memory_as_slice();
			let range = checked_range(address.into(), dest.len(), memory.len())
				.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;
			dest.copy_from_slice(&memory[range]);
			Ok(())
		}
	}

	/// Write data to a slice of memory.
	///
	/// Returns an error if the write would go out of the memory bounds.
	pub fn write_memory_from(&self, address: Pointer<u8>, data: &[u8]) -> Result<()> {
		unsafe {
			// TODO: Proof
			let memory = self.memory_as_slice_mut();
			let range = checked_range(address.into(), data.len(), memory.len())
				.ok_or_else(|| Error::Other("memory write is out of bounds".into()))?;
			&mut memory[range].copy_from_slice(data);
			Ok(())
		}
	}

	pub fn allocate(
		&self,
		allocator: &mut sc_executor_common::allocator::FreeingBumpHeapAllocator,
		size: WordSize,
	) -> Result<Pointer<u8>> {
		unsafe {
			// TODO: Proof
			let mem_mut = self.memory_as_slice_mut();
			allocator.allocate(mem_mut, size)
		}
	}

	pub fn deallocate(
		&self,
		allocator: &mut sc_executor_common::allocator::FreeingBumpHeapAllocator,
		ptr: Pointer<u8>,
	) -> Result<()> {
		unsafe {
			// TODO: Proof
			let mem_mut = self.memory_as_slice_mut();
			allocator.deallocate(mem_mut, ptr)
		}
	}

	/// Returns linear memory of the wasm instance as a slice.
	///
	/// # Safety
	///
	/// Wasmtime doesn't provide comprehensive documentation about the exact behavior of the data
	/// pointer. If a dynamic style heap is used the base pointer of the heap can change. Since
	/// growing, we cannot guarantee the lifetime of the returned slice reference.
	unsafe fn memory_as_slice(&self) -> &[u8] {
		let ptr = self.memory.data_ptr() as *const _;
		let len = self.memory.data_size();

		if len == 0 {
			&[]
		} else {
			slice::from_raw_parts(ptr, len)
		}
	}

	/// Returns linear memory of the wasm instance as a slice.
	///
	/// # Safety
	///
	/// See `[memory_as_slice]`. In addition to those requirements, since a mutable reference is
	/// returned it must be ensured that only one mutable reference to memory exists.
	unsafe fn memory_as_slice_mut(&self) -> &mut [u8] {
		let ptr = self.memory.data_ptr();
		let len = self.memory.data_size();

		if len == 0 {
			&mut []
		} else {
			slice::from_raw_parts_mut(ptr, len)
		}
	}
}

/// Construct a range from an offset to a data length after the offset.
/// Returns None if the end of the range would exceed some maximum offset.
fn checked_range(offset: usize, len: usize, max: usize) -> Option<Range<usize>> {
	let end = offset.checked_add(len)?;
	if end <= max {
		Some(offset..end)
	} else {
		None
	}
}
