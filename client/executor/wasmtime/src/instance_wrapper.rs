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

use crate::util;
use crate::imports::Imports;

use std::{slice, marker};
use sc_executor_common::{
	error::{Error, Result},
	util::{WasmModuleInfo, DataSegmentsSnapshot},
};
use sp_wasm_interface::{Pointer, WordSize, Value};
use wasmtime::{Store, Instance, Module, Memory, Table, Val, Func, Extern, Global};

mod globals_snapshot;

pub use globals_snapshot::GlobalsSnapshot;

pub struct ModuleWrapper {
	imported_globals_count: u32,
	globals_count: u32,
	module: Module,
	data_segments_snapshot: DataSegmentsSnapshot,
}

impl ModuleWrapper {
	pub fn new(store: &Store, code: &[u8]) -> Result<Self> {
		let module = Module::new(&store, code)
			.map_err(|e| Error::from(format!("cannot create module: {}", e)))?;

		let module_info = WasmModuleInfo::new(code)
			.ok_or_else(|| Error::from("cannot deserialize module".to_string()))?;
		let declared_globals_count = module_info.declared_globals_count();
		let imported_globals_count = module_info.imported_globals_count();
		let globals_count = imported_globals_count + declared_globals_count;

		let data_segments_snapshot = DataSegmentsSnapshot::take(&module_info)
			.map_err(|e| Error::from(format!("cannot take data segments snapshot: {}", e)))?;

		Ok(Self {
			module,
			imported_globals_count,
			globals_count,
			data_segments_snapshot,
		})
	}

	pub fn module(&self) -> &Module {
		&self.module
	}

	pub fn data_segments_snapshot(&self) -> &DataSegmentsSnapshot {
		&self.data_segments_snapshot
	}
}

/// Wrap the given WebAssembly Instance of a wasm module with Substrate-runtime.
///
/// This struct is a handy wrapper around a wasmtime `Instance` that provides substrate specific
/// routines.
pub struct InstanceWrapper {
	instance: Instance,
	globals_count: u32,
	imported_globals_count: u32,
	// The memory instance of the `instance`.
	//
	// It is important to make sure that we don't make any copies of this to make it easier to proof
	// See `memory_as_slice` and `memory_as_slice_mut`.
	memory: Memory,
	table: Option<Table>,
	// Make this struct explicitly !Send & !Sync.
	_not_send_nor_sync: marker::PhantomData<*const ()>,
}

fn extern_memory(extern_: &Extern) -> Option<&Memory> {
	match extern_ {
		Extern::Memory(mem) => Some(mem),
		_ => None,
	}
}


fn extern_global(extern_: &Extern) -> Option<&Global> {
	match extern_ {
		Extern::Global(glob) => Some(glob),
		_ => None,
	}
}

fn extern_table(extern_: &Extern) -> Option<&Table> {
	match extern_ {
		Extern::Table(table) => Some(table),
		_ => None,
	}
}

fn extern_func(extern_: &Extern) -> Option<&Func> {
	match extern_ {
		Extern::Func(func) => Some(func),
		_ => None,
	}
}

impl InstanceWrapper {
	/// Create a new instance wrapper from the given wasm module.
	pub fn new(module_wrapper: &ModuleWrapper, imports: &Imports, heap_pages: u32) -> Result<Self> {
		let instance = Instance::new(&module_wrapper.module, &imports.externs)
			.map_err(|e| Error::from(format!("cannot instantiate: {}", e)))?;

		let memory = match imports.memory_import_index {
			Some(memory_idx) => {
				extern_memory(&imports.externs[memory_idx])
					.expect("only memory can be at the `memory_idx`; qed")
					.clone()
			}
			None => {
				let memory = get_linear_memory(&instance)?;
				if !memory.grow(heap_pages).is_ok() {
					return Err("failed top increase the linear memory size".into());
				}
				memory
			},
		};

		Ok(Self {
			table: get_table(&instance),
			instance,
			globals_count: module_wrapper.globals_count,
			imported_globals_count: module_wrapper.imported_globals_count,
			memory,
			_not_send_nor_sync: marker::PhantomData,
		})
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
			.ok_or_else(|| Error::from(format!("Exported method {} is not found", name)))?;
		let entrypoint = extern_func(&export)
			.ok_or_else(|| Error::from(format!("Export {} is not a function", name)))?;
		match (entrypoint.ty().params(), entrypoint.ty().results()) {
			(&[wasmtime::ValType::I32, wasmtime::ValType::I32], &[wasmtime::ValType::I64]) => {}
			_ => {
				return Err(Error::from(format!(
					"method {} have an unsupported signature",
					name
				)))
			}
		}
		Ok(entrypoint.clone())
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

		let heap_base_global = extern_global(&heap_base_export)
			.ok_or_else(|| Error::from("__heap_base is not a global"))?;

		let heap_base = heap_base_global
			.get()
			.i32()
			.ok_or_else(|| Error::from("__heap_base is not a i32"))?;

		Ok(heap_base as u32)
	}

	/// Get the value from a global with the given `name`.
	pub fn get_global_val(&self, name: &str) -> Result<Option<Value>> {
		let global = match self.instance.get_export(name) {
			Some(global) => global,
			None => return Ok(None),
		};

		let global = extern_global(&global).ok_or_else(|| format!("`{}` is not a global", name))?;

		match global.get() {
			Val::I32(val) => Ok(Some(Value::I32(val))),
			Val::I64(val) => Ok(Some(Value::I64(val))),
			Val::F32(val) => Ok(Some(Value::F32(val))),
			Val::F64(val) => Ok(Some(Value::F64(val))),
			_ => Err("Unknown value type".into()),
		}
	}
}

/// Extract linear memory instance from the given instance.
fn get_linear_memory(instance: &Instance) -> Result<Memory> {
	let memory_export = instance
		.get_export("memory")
		.ok_or_else(|| Error::from("memory is not exported under `memory` name"))?;

	let memory = extern_memory(&memory_export)
		.ok_or_else(|| Error::from("the `memory` export should have memory type"))?
		.clone();

	Ok(memory)
}

/// Extract the table from the given instance if any.
fn get_table(instance: &Instance) -> Option<Table> {
	instance
		.get_export("__indirect_function_table")
		.as_ref()
		.and_then(extern_table)
		.cloned()
}

/// Functions realted to memory.
impl InstanceWrapper {
	/// Read data from a slice of memory into a destination buffer.
	///
	/// Returns an error if the read would go out of the memory bounds.
	pub fn read_memory_into(&self, address: Pointer<u8>, dest: &mut [u8]) -> Result<()> {
		unsafe {
			// This should be safe since we don't grow up memory while caching this reference and
			// we give up the reference before returning from this function.
			let memory = self.memory_as_slice();

			let range = util::checked_range(address.into(), dest.len(), memory.len())
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
			// This should be safe since we don't grow up memory while caching this reference and
			// we give up the reference before returning from this function.
			let memory = self.memory_as_slice_mut();

			let range = util::checked_range(address.into(), data.len(), memory.len())
				.ok_or_else(|| Error::Other("memory write is out of bounds".into()))?;
			&mut memory[range].copy_from_slice(data);
			Ok(())
		}
	}

	/// Allocate some memory of the given size. Returns pointer to the allocated memory region.
	///
	/// Returns `Err` in case memory cannot be allocated. Refer to the allocator documentation
	/// to get more details.
	pub fn allocate(
		&self,
		allocator: &mut sp_allocator::FreeingBumpHeapAllocator,
		size: WordSize,
	) -> Result<Pointer<u8>> {
		unsafe {
			// This should be safe since we don't grow up memory while caching this reference and
			// we give up the reference before returning from this function.
			let memory = self.memory_as_slice_mut();

			allocator.allocate(memory, size).map_err(Into::into)
		}
	}

	/// Deallocate the memory pointed by the given pointer.
	///
	/// Returns `Err` in case the given memory region cannot be deallocated.
	pub fn deallocate(
		&self,
		allocator: &mut sp_allocator::FreeingBumpHeapAllocator,
		ptr: Pointer<u8>,
	) -> Result<()> {
		unsafe {
			// This should be safe since we don't grow up memory while caching this reference and
			// we give up the reference before returning from this function.
			let memory = self.memory_as_slice_mut();

			allocator.deallocate(memory, ptr).map_err(Into::into)
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
	/// returned it must be ensured that only one mutable and no shared references to memory exists
	/// at the same time.
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
