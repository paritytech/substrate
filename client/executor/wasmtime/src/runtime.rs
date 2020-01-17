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

use crate::function_executor::HostState;
use crate::instance_wrapper::InstanceWrapper;
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
	instance_wrapper.grow_memory(heap_pages)?;

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

	let mut host_state = HostState::new(allocator, instance_wrapper);

	let (output_ptr, output_len) = state_holder.init_state(&mut host_state, || {
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

	let instance = host_state.into_instance();
	let output = extract_output_data(&instance, output_ptr, output_len)?;

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
