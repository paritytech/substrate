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

use crate::host::HostState;
use crate::imports::{Imports, resolve_imports};
use crate::instance_wrapper::{ModuleWrapper, InstanceWrapper, GlobalsSnapshot, EntryPoint};
use crate::state_holder;

use std::rc::Rc;
use std::sync::Arc;
use sc_executor_common::{
	error::{Result, WasmError},
	wasm_runtime::{WasmModule, WasmInstance, InvokeMethod},
};
use sp_allocator::FreeingBumpHeapAllocator;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, WordSize, Value};
use wasmtime::{Config, Engine, Store};

/// A `WasmModule` implementation using wasmtime to compile the runtime module to machine code
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	module_wrapper: Arc<ModuleWrapper>,
	heap_pages: u32,
	allow_missing_func_imports: bool,
	host_functions: Vec<&'static dyn Function>,
	engine: Engine,
}

impl WasmModule for WasmtimeRuntime {
	fn new_instance(&self) -> Result<Box<dyn WasmInstance>> {
		let store = Store::new(&self.engine);

		// Scan all imports, find the matching host functions, and create stubs that adapt arguments
		// and results.
		let imports = resolve_imports(
			&store,
			self.module_wrapper.module(),
			&self.host_functions,
			self.heap_pages,
			self.allow_missing_func_imports,
		)?;

		let instance_wrapper =
			InstanceWrapper::new(&store, &self.module_wrapper, &imports, self.heap_pages)?;
		let heap_base = instance_wrapper.extract_heap_base()?;
		let globals_snapshot = GlobalsSnapshot::take(&instance_wrapper)?;

		Ok(Box::new(WasmtimeInstance {
			store,
			instance_wrapper: Rc::new(instance_wrapper),
			module_wrapper: Arc::clone(&self.module_wrapper),
			imports,
			globals_snapshot,
			heap_pages: self.heap_pages,
			heap_base,
		}))
	}
}

/// A `WasmInstance` implementation that reuses compiled module and spawns instances
/// to execute the compiled code.
pub struct WasmtimeInstance {
	store: Store,
	module_wrapper: Arc<ModuleWrapper>,
	instance_wrapper: Rc<InstanceWrapper>,
	globals_snapshot: GlobalsSnapshot,
	imports: Imports,
	heap_pages: u32,
	heap_base: u32,
}

// This is safe because `WasmtimeInstance` does not leak reference to `self.imports`
// and all imports don't reference any anything, other than host functions and memory
unsafe impl Send for WasmtimeInstance {}

impl WasmInstance for WasmtimeInstance {
	fn call(&self, method: InvokeMethod, data: &[u8]) -> Result<Vec<u8>> {
		let entrypoint = self.instance_wrapper.resolve_entrypoint(method)?;
		let allocator = FreeingBumpHeapAllocator::new(self.heap_base);

		self.module_wrapper
			.data_segments_snapshot()
			.apply(|offset, contents| {
				self.instance_wrapper
					.write_memory_from(Pointer::new(offset), contents)
			})?;

		self.globals_snapshot.apply(&*self.instance_wrapper)?;

		perform_call(
			data,
			Rc::clone(&self.instance_wrapper),
			entrypoint,
			allocator,
		)
	}

	fn get_global_const(&self, name: &str) -> Result<Option<Value>> {
		let instance = InstanceWrapper::new(&self.store, &self.module_wrapper, &self.imports, self.heap_pages)?;
		instance.get_global_val(name)
	}
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
pub fn create_runtime(
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	// Create the engine, store and finally the module from the given code.
	let mut config = Config::new();
	config.cranelift_opt_level(wasmtime::OptLevel::SpeedAndSize);

	let engine = Engine::new(&config);

	let module_wrapper = ModuleWrapper::new(&engine, code)
		.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;

	Ok(WasmtimeRuntime {
		module_wrapper: Arc::new(module_wrapper),
		heap_pages: heap_pages as u32,
		allow_missing_func_imports,
		host_functions,
		engine,
	})
}

fn perform_call(
	data: &[u8],
	instance_wrapper: Rc<InstanceWrapper>,
	entrypoint: EntryPoint,
	mut allocator: FreeingBumpHeapAllocator,
) -> Result<Vec<u8>> {
	let (data_ptr, data_len) = inject_input_data(&instance_wrapper, &mut allocator, data)?;

	let host_state = HostState::new(allocator, instance_wrapper.clone());
	let ret = state_holder::with_initialized_state(&host_state, || -> Result<_> {
		Ok(unpack_ptr_and_len(entrypoint.call(data_ptr, data_len)?))
	});
	let (output_ptr, output_len) = ret?;
	let output = extract_output_data(&instance_wrapper, output_ptr, output_len)?;

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
