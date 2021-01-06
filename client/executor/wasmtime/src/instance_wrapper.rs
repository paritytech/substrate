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

//! Defines data and logic needed for interaction with an WebAssembly instance of a substrate
//! runtime module.

use crate::util;
use crate::imports::Imports;

use std::{slice, marker};
use sc_executor_common::{
	error::{Error, Result},
	util::{WasmModuleInfo, DataSegmentsSnapshot},
	wasm_runtime::InvokeMethod,
};
use sp_wasm_interface::{Pointer, WordSize, Value};
use wasmtime::{Engine, Instance, Module, Memory, Table, Val, Func, Extern, Global, Store};
use parity_wasm::elements;

mod globals_snapshot;

pub use globals_snapshot::GlobalsSnapshot;

pub struct ModuleWrapper {
	module: Module,
	data_segments_snapshot: DataSegmentsSnapshot,
}

impl ModuleWrapper {
	pub fn new(engine: &Engine, code: &[u8]) -> Result<Self> {
		let mut raw_module: elements::Module = elements::deserialize_buffer(code)
			.map_err(|e| Error::from(format!("cannot decode module: {}", e)))?;
		pwasm_utils::export_mutable_globals(&mut raw_module, "exported_internal_global");
		let instrumented_code = elements::serialize(raw_module)
			.map_err(|e| Error::from(format!("cannot encode module: {}", e)))?;

		let module = Module::new(engine, &instrumented_code)
			.map_err(|e| Error::from(format!("cannot create module: {}", e)))?;

		let module_info = WasmModuleInfo::new(code)
			.ok_or_else(|| Error::from("cannot deserialize module".to_string()))?;

		let data_segments_snapshot = DataSegmentsSnapshot::take(&module_info)
			.map_err(|e| Error::from(format!("cannot take data segments snapshot: {}", e)))?;

		Ok(Self {
			module,
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

/// Invoked entrypoint format.
pub enum EntryPointType {
	/// Direct call.
	///
	/// Call is made by providing only payload reference and length.
	Direct,
	/// Indirect call.
	///
	/// Call is made by providing payload reference and length, and extra argument
	/// for advanced routing (typically extra WASM function pointer).
	Wrapped(u32),
}

/// Wasm blob entry point.
pub struct EntryPoint {
	call_type: EntryPointType,
	func: wasmtime::Func,
}

impl EntryPoint {
	/// Call this entry point.
	pub fn call(&self, data_ptr: Pointer<u8>, data_len: WordSize) -> Result<u64> {
		let data_ptr = u32::from(data_ptr) as i32;
		let data_len = u32::from(data_len) as i32;

		(match self.call_type {
			EntryPointType::Direct => {
				self.func.call(&[
					wasmtime::Val::I32(data_ptr),
					wasmtime::Val::I32(data_len),
				])
			},
			EntryPointType::Wrapped(func) => {
				self.func.call(&[
					wasmtime::Val::I32(func as _),
					wasmtime::Val::I32(data_ptr),
					wasmtime::Val::I32(data_len),
				])
			},
		})
			.map(|results| 
				// the signature is checked to have i64 return type
				results[0].unwrap_i64() as u64
			)
			.map_err(|err| Error::from(format!(
				"Wasm execution trapped: {}",
				err
			)))
	}

	pub fn direct(func: wasmtime::Func) -> std::result::Result<Self, &'static str> {
		match (func.ty().params(), func.ty().results()) {
			(&[wasmtime::ValType::I32, wasmtime::ValType::I32], &[wasmtime::ValType::I64]) => {
				Ok(Self { func, call_type: EntryPointType::Direct })
			}
			_ => {
				Err("Invalid signature for direct entry point")
			}
		}
	}

	pub fn wrapped(dispatcher: wasmtime::Func, func: u32) -> std::result::Result<Self, &'static str> {
		match (dispatcher.ty().params(), dispatcher.ty().results()) {
			(
				&[wasmtime::ValType::I32, wasmtime::ValType::I32, wasmtime::ValType::I32],
				&[wasmtime::ValType::I64],
			) => {
				Ok(Self { func: dispatcher, call_type: EntryPointType::Wrapped(func) })
			},
			_ => {
				Err("Invalid signature for wrapped entry point")
			}
		}
	}
}

/// Wrap the given WebAssembly Instance of a wasm module with Substrate-runtime.
///
/// This struct is a handy wrapper around a wasmtime `Instance` that provides substrate specific
/// routines.
pub struct InstanceWrapper {
	instance: Instance,
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
	pub fn new(store: &Store, module_wrapper: &ModuleWrapper, imports: &Imports, heap_pages: u32) -> Result<Self> {
		let instance = Instance::new(store, &module_wrapper.module, &imports.externs)
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
			memory,
			_not_send_nor_sync: marker::PhantomData,
		})
	}

	/// Resolves a substrate entrypoint by the given name.
	///
	/// An entrypoint must have a signature `(i32, i32) -> i64`, otherwise this function will return
	/// an error.
	pub fn resolve_entrypoint(&self, method: InvokeMethod) -> Result<EntryPoint> {
		Ok(match method {
			InvokeMethod::Export(method) => {
				// Resolve the requested method and verify that it has a proper signature.
				let export = self
					.instance
					.get_export(method)
					.ok_or_else(|| Error::from(format!("Exported method {} is not found", method)))?;
				let func = extern_func(&export)
					.ok_or_else(|| Error::from(format!("Export {} is not a function", method)))?
					.clone();
				EntryPoint::direct(func)
					.map_err(|_|
						Error::from(format!(
							"Exported function '{}' has invalid signature.",
							method,
						))
					)?
			},
			InvokeMethod::Table(func_ref) => {
				let table = self.instance.get_table("__indirect_function_table").ok_or(Error::NoTable)?;
				let val = table.get(func_ref)
					.ok_or(Error::NoTableEntryWithIndex(func_ref))?;
				let func = val
					.funcref()
					.ok_or(Error::TableElementIsNotAFunction(func_ref))?
					.ok_or(Error::FunctionRefIsNull(func_ref))?
					.clone();

				EntryPoint::direct(func)
					.map_err(|_|
						Error::from(format!(
							"Function @{} in exported table has invalid signature for direct call.",
							func_ref,
						))
					)?
				},
			InvokeMethod::TableWithWrapper { dispatcher_ref, func } => {
				let table = self.instance.get_table("__indirect_function_table").ok_or(Error::NoTable)?;
				let val = table.get(dispatcher_ref)
					.ok_or(Error::NoTableEntryWithIndex(dispatcher_ref))?;
				let dispatcher = val
					.funcref()
					.ok_or(Error::TableElementIsNotAFunction(dispatcher_ref))?
					.ok_or(Error::FunctionRefIsNull(dispatcher_ref))?
					.clone();

				EntryPoint::wrapped(dispatcher, func)
					.map_err(|_|
						Error::from(format!(
							"Function @{} in exported table has invalid signature for wrapped call.",
							dispatcher_ref,
						))
					)?
			},
		})
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
