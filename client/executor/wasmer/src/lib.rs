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

use sc_executor_common::{
	error::{Error, Result, WasmError},
	wasm_runtime,
};
use sp_allocator::FreeingBumpHeapAllocator;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, WordSize, Value};
use wasmer_runtime::{
	compile_with, compiler_for_backend, func, imports, instantiate, Backend, ImportObject, Memory,
	Module,
};
use std::sync::Arc;

mod host;
mod imports;
mod state_holder;
mod util;

use crate::host::HostState;
use crate::imports::Imports;

pub struct WasmerRuntime {
	module: Arc<Module>,
	host_functions: Vec<&'static dyn Function>,
	imports: Imports,
}

unsafe impl Sync for WasmerRuntime {
}

impl wasm_runtime::WasmModule for WasmerRuntime {
	fn new_instance(&self) -> Result<Box<dyn wasm_runtime::WasmInstance>> {
		let (import_object, memory) = self.imports.materialize();
		Ok(Box::new(WasmerInstance {
			module: self.module.clone(),
			memory,
			import_object
		}))
	}
}

pub fn create_instance(
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> std::result::Result<WasmerRuntime, WasmError> {
	let compiler = compiler_for_backend(Backend::default()).unwrap();
	let module = Arc::new(compile_with(code, compiler.as_ref()).unwrap());

	let imports = imports::resolve_imports(
		&host_functions,
		code,
		allow_missing_func_imports,
		heap_pages as u32,
	);

	Ok(WasmerRuntime {
		module,
		host_functions,
		imports,
	})
}

pub struct WasmerInstance {
	module: Arc<Module>,
	memory: Option<Memory>,
	import_object: ImportObject,
}

impl wasm_runtime::WasmInstance for WasmerInstance {
	fn call(&self, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&self.module,
			&self.import_object,
			self.memory.as_ref(),
			method,
			data,
		)
	}

	fn get_global_const(&self, name: &str) -> Result<Option<Value>> {
		todo!()
	}
}

fn call_method(
	module: &Module,
	import_object: &ImportObject,
	memory: Option<&Memory>,
	method: &str,
	data: &[u8],
) -> Result<Vec<u8>> {
	// This import object can contain shared functions, but it should have its own memory.
	let instance = module.instantiate(import_object).unwrap();

	let heap_base = 1054880; // TODO:
	let mut allocator = FreeingBumpHeapAllocator::new(heap_base);

	let memory = memory.unwrap(); // TODO: Support non imported memory.

	let (data_ptr, data_len) = inject_input_data(&mut allocator, memory, data);

	let host_state = HostState::new(allocator, memory.clone());
	let ret = state_holder::with_initialized_state(&host_state, || {
		match instance.call(
			method,
			&[
				wasmer_runtime_core::types::Value::I32(u32::from(data_ptr) as i32),
				wasmer_runtime_core::types::Value::I32(u32::from(data_len) as i32),
			],
		) {
			Ok(results) => {
				let retval = match results[0] {
					wasmer_runtime_core::types::Value::I64(retval) => retval as u64,
					_ => panic!(),
				};
				Ok(unpack_ptr_and_len(retval))
			}
			Err(trap) => {
				return Err(Error::from(format!("Wasm execution trapped: {}", trap)));
			}
		}
	});

	let (output_ptr, output_len) = ret?;
	let output = extract_output_data(memory, output_ptr, output_len);

	Ok(output)
}

fn inject_input_data(
	allocator: &mut FreeingBumpHeapAllocator,
	memory: &Memory,
	input_data: &[u8],
) -> (u32, u32) {
	let len = input_data.len() as u32;
	let ptr = allocator
		.allocate(&mut util::AllocatorMemory(memory), len)
		.map_err(|e| e.to_string())
		.unwrap();
	util::write_memory(memory, ptr.into(), input_data).unwrap();
	(ptr.into(), len)
}

fn extract_output_data(memory: &Memory, output_ptr: u32, output_len: u32) -> Vec<u8> {
	let mut output = vec![0; output_len as usize];
	util::read_memory(memory, output_ptr, &mut output).unwrap();
	output
}
