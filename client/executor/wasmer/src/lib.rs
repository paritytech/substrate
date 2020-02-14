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
	wasm_runtime::WasmRuntime,
};
use sp_allocator::FreeingBumpHeapAllocator;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, WordSize};
use wasmer_runtime::{
	compile_with, compiler_for_backend, func, imports, instantiate, Backend, ImportObject, Memory,
	Module,
};

mod host;
mod imports;
mod state_holder;

use crate::host::HostState;
use crate::imports::Imports;
use crate::state_holder::StateHolder;

pub struct WasmerRuntime {
	module: Module,
	state_holder: StateHolder,
	host_functions: Vec<&'static dyn Function>,
	imports: Imports,
}

impl WasmRuntime for WasmerRuntime {
	fn host_functions(&self) -> &[&'static dyn Function] {
		&self.host_functions
	}

	fn call(&mut self, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&self.module,
			&self.state_holder,
			&self.imports,
			method,
			data,
		)
	}
}

pub fn create_instance(
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> std::result::Result<WasmerRuntime, WasmError> {
	let compiler = compiler_for_backend(Backend::default()).unwrap();
	let module = compile_with(code, compiler.as_ref()).unwrap();

	let state_holder = StateHolder::empty();
	let imports = imports::resolve_imports(
		&state_holder,
		&host_functions,
		code,
		allow_missing_func_imports,
		heap_pages as u32,
	);

	Ok(WasmerRuntime {
		module,
		host_functions,
		state_holder,
		imports,
	})
}

fn call_method(
	module: &Module,
	state_holder: &StateHolder,
	imports: &Imports,
	method: &str,
	data: &[u8],
) -> Result<Vec<u8>> {
	let instance = module.instantiate(&imports.import_object).unwrap();

	let heap_base = 1054760; // TODO:
	let mut allocator = FreeingBumpHeapAllocator::new(heap_base);
	let memory = imports.memory.as_ref().unwrap().clone();

	let (data_ptr, data_len) = inject_input_data(&mut allocator, &memory, data);

	let host_state = HostState::new(allocator, memory.clone());
	let (ret, host_state) = state_holder.with_initialized_state(host_state, || {
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
	let output = extract_output_data(&memory, output_ptr, output_len);

	Ok(output)
}

fn inject_input_data(
	allocator: &mut FreeingBumpHeapAllocator,
	memory: &Memory,
	input_data: &[u8],
) -> (u32, u32) {
	use std::ops::Deref;
	let view = memory.view::<u8>();
	let cell_slice = view.deref();
	#[allow(mutable_transmutes)]
	let slice: &mut [u8] = unsafe { std::mem::transmute(cell_slice) };
	let len = input_data.len();
	let ptr = allocator
		.allocate(slice, len as u32)
		.map_err(|e| e.to_string())
		.unwrap();
	let ptr = usize::from(ptr);
	slice[ptr..(ptr + len)].copy_from_slice(input_data);
	(u32::from(ptr as u32), len as u32)
}

fn extract_output_data(memory: &Memory, output_ptr: u32, output_len: u32) -> Vec<u8> {
	use std::ops::Deref;
	let len = output_len as usize;
	let mut output = vec![0; len];
	let view = memory.view::<u8>();
	let cell_slice = view.deref();
	let slice: &[u8] = unsafe { std::mem::transmute(cell_slice) };
	let offset = output_ptr as usize;
	output.copy_from_slice(&slice[offset..offset + len]);
	output
}
