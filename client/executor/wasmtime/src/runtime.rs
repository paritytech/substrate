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

//! Defines the compiled Wasm runtime that uses Wasmtime internally.

use crate::function_executor::{FunctionExecutor, FunctionExecutorState};
use crate::imports::resolve_imports;
use crate::state_holder::StateHolder;

use sc_executor_common::{
	error::{Error, Result, WasmError},
	wasm_runtime::WasmRuntime,
	allocator::FreeingBumpHeapAllocator,
};
use sp_core::traits::Externalities;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, Value, ValueType, WordSize};

use std::cell::{self, RefCell};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::ops::Range;
use std::rc::Rc;
use std::slice;

use wasmtime::{
	Config, Engine, Extern, ExternType, Func, Instance, Memory, Module, Store, Table, Trap, Val,
};

/// A `WasmRuntime` implementation using wasmtime to compile the runtime module to machine code
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	module: Module,
	externs: Vec<Extern>,
	state_holder: StateHolder,
	heap_pages: u32,
	host_functions: Vec<&'static dyn Function>,
}

impl WasmRuntime for WasmtimeRuntime {
	fn host_functions(&self) -> &[&'static dyn Function] {
		&self.host_functions
	}

	fn call(&mut self, ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&self.module,
			&self.externs,
			&self.state_holder,
			ext,
			method,
			data,
			self.heap_pages,
		)
	}
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
pub fn create_instance(
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	// Create the engine, store and finally the module from the given code.
	let mut config = Config::new();
	config.cranelift_opt_level(wasmtime::OptLevel::SpeedAndSize);

	let engine = Engine::new(&config);
	let store = Store::new(&engine);
	let module = Module::new(&store, code)
		.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;

	let state_holder = StateHolder::empty();

	// Scan all imports, find the matching host functions, and create stubs that adapt arguments
	// and results.
	let externs = resolve_imports(&state_holder, &module, &host_functions)?;

	Ok(WasmtimeRuntime {
		module,
		externs,
		state_holder,
		heap_pages: heap_pages as u32,
		host_functions,
	})
}

/// Call a function inside a precompiled Wasm module.
fn call_method(
	module: &Module,
	externs: &[Extern],
	state_holder: &StateHolder,
	ext: &mut dyn Externalities,
	method: &str,
	data: &[u8],
	heap_pages: u32,
) -> Result<Vec<u8>> {
	let instance = Instance::new(module, externs)
		.map_err(|e| WasmError::Other(format!("cannot instantiate: {}", e)))?;

	let instance_wrapper = unsafe { InstanceWrapper::new(instance)? };
	instance_wrapper.increase_linear_memory(heap_pages)?;

	let heap_base = instance_wrapper.extract_heap_base()?;
	let allocator = FreeingBumpHeapAllocator::new(heap_base);

	let entrypoint = instance_wrapper.resolve_entrypoint(method)?;

	perform_call(ext, data, state_holder, instance_wrapper, entrypoint, allocator)
}

fn perform_call(
	ext: &mut dyn Externalities,
	data: &[u8],
	state_holder: &StateHolder,
	instance_wrapper: InstanceWrapper,
	entrypoint: wasmtime::Func,
	mut allocator: FreeingBumpHeapAllocator,
) -> Result<Vec<u8>> {
	let (data_ptr, data_len) = inject_input_data(&instance_wrapper, &mut allocator, data)?;

	let mut executor_state = FunctionExecutorState::new(allocator, instance_wrapper);

	let (output_ptr, output_len) = state_holder.init_state(&mut executor_state, || {
		sp_externalities::set_and_run_with_externalities(ext, || {
			match entrypoint.call(&[
				wasmtime::Val::I32(u32::from(data_ptr) as i32),
				wasmtime::Val::I32(u32::from(data_len) as i32),
			]) {
				Ok(results) => {
					let retval = results[0].unwrap_i64() as u64;
					Ok(unpack_ptr_and_len(retval))
				}
				Err(trap) => {
					return Err(Error::from(format!(
						"Wasm execution trapped: {}",
						trap.message()
					)));
				}
			}
		})
	})?;

	let output = extract_output_data(&executor_state.into_instance(), output_ptr, output_len)?;

	Ok(output)
}

fn inject_input_data(
	instance: &InstanceWrapper,
	allocator: &mut FreeingBumpHeapAllocator,
	data: &[u8],
) -> Result<(Pointer<u8>, WordSize)> {
	let data_len = data.len() as WordSize;
	let data_ptr = instance.allocate(allocator, data_len)?;
	instance.write_memory_from(data_ptr, data)?;
	Ok((data_ptr, data_len))
}

fn extract_output_data(
	instance: &InstanceWrapper,
	output_ptr: u32,
	output_len: u32,
) -> Result<Vec<u8>> {
	let mut output = vec![0; output_len as usize];
	instance.read_memory_into(Pointer::new(output_ptr), &mut output)?;
	Ok(output)
}

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

	pub fn increase_linear_memory(&self, pages: u32) -> Result<()> {
		if self.memory.grow(pages) {
			Ok(())
		} else {
			return Err("failed top increase the linear memory size".into());
		}
	}

	pub fn resolve_entrypoint(&self, entrypoint_name: &str) -> Result<wasmtime::Func> {
		// Resolve the requested method and verify that it has a proper signature.
		let export = self
			.instance
			.find_export_by_name(entrypoint_name)
			.ok_or_else(|| {
				Error::from(format!("Exported method {} is not found", entrypoint_name))
			})?;
		let entrypoint_func = export
			.func()
			.ok_or_else(|| Error::from(format!("Export {} is not a function", entrypoint_name)))?;
		// TODO: Check the signature
		Ok(entrypoint_func.clone())
	}

	pub fn table(&self) -> Option<&Table> {
		self.table.as_ref()
	}

	pub fn memory_size(&self) -> u32 {
		self.memory.data_size() as u32
	}

	fn extract_heap_base(&self) -> Result<u32> {
		let heap_base_export = self
			.instance
			.find_export_by_name("__heap_base")
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
		.find_export_by_name("__indirect_function_table")
		.and_then(|export| export.table())
		.cloned()
}

fn get_linear_memory(instance: &Instance) -> Result<Memory> {
	let memory_export = instance
		.find_export_by_name("memory")
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
