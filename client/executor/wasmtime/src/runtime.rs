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
use crate::util::{read_memory_into, write_memory_from};

use sc_executor_common::{
	error::{Error, Result, WasmError},
	wasm_runtime::WasmRuntime,
};
use sp_core::traits::Externalities;
use sp_runtime_interface::unpack_ptr_and_len;
use sp_wasm_interface::{Function, Pointer, Value, ValueType, WordSize};

use std::cell::{self, RefCell};
use std::collections::HashMap;
use std::convert::TryFrom;
use std::rc::Rc;

use wasmtime::{
	Callable, Config, Extern, ExternType, Func, Instance, Memory, Module, Store, Table, Trap, Val,
};

/// A `WasmRuntime` implementation using wasmtime to compile the runtime module to machine code
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	store: Store,
	module: Module,
	externs: Vec<Extern>,
	state_holder: StateHolder,
	max_heap_pages: Option<u32>,
	heap_pages: u32,
	/// The host functions registered for this instance.
	host_functions: Vec<&'static dyn Function>,
}

impl WasmRuntime for WasmtimeRuntime {
	fn update_heap_pages(&mut self, heap_pages: u64) -> bool {
		// match heap_pages_valid(heap_pages, self.max_heap_pages) {
		// 	Some(heap_pages) => {
		// 		self.heap_pages = heap_pages;
		// 		true
		// 	}
		// 	None => false,
		// }
		// TODO:
		true
	}

	fn host_functions(&self) -> &[&'static dyn Function] {
		&self.host_functions
	}

	fn call(&mut self, ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&self.store,
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
	// TODO: Tinker with the config.
	// For now the default Store would suffice.
	let store = Store::default();
	let module = Module::new(&store, code)
		.map_err(|e| WasmError::Other(format!("cannot create module: {}", e)))?;

	// TODO: Check the heap pages
	let max_heap_pages = None;

	let state_holder = StateHolder::empty();
	let mut externs = vec![];
	for import_ty in module.imports() {
		if import_ty.module() != "env" {
			return Err(WasmError::Other(format!(
				"host doesn't provide any imports from non-env module: {}:{}",
				import_ty.module(),
				import_ty.name()
			)));
		}

		let host_func = host_functions
			.iter()
			.find(|host_func| host_func.name() == import_ty.name())
			.unwrap(); // TODO: Handle missing functions

		let func_ty = match import_ty.ty() {
			ExternType::Func(func_ty) => func_ty,
			_ => {
				return Err(WasmError::Other(format!(
					"host doesn't provide any non function imports: {}:{}",
					import_ty.module(),
					import_ty.name()
				)))
			}
		};
		// TODO: Check the signature

		externs.push(wrap_substrate_func(
			&store,
			state_holder.clone(),
			*host_func,
		));
	}

	Ok(WasmtimeRuntime {
		store,
		module,
		externs,
		state_holder,
		max_heap_pages,
		heap_pages: heap_pages as u32,
		host_functions,
	})
}

fn wrap_substrate_func(
	store: &Store,
	state_holder: StateHolder,
	host_func: &'static dyn Function,
) -> Extern {
	let func_ty = wasmtime_func_sig(host_func);
	let callable = HostFuncAdapterCallable::new(state_holder, host_func);
	let func = Func::new(store, func_ty, Rc::new(callable));
	Extern::Func(func)
}

#[derive(Clone)]
struct StateHolder {
	// This is `Some` only during a call.
	state: Rc<RefCell<Option<FunctionExecutorState>>>,
}

impl StateHolder {
	fn empty() -> StateHolder {
		StateHolder {
			state: Rc::new(RefCell::new(None)),
		}
	}

	fn set(&self, state: FunctionExecutorState) {
		*self.state.borrow_mut() = Some(state);
	}

	fn reset(&self) {
		*self.state.borrow_mut() = None;
	}

	fn get(&self) -> Option<cell::Ref<FunctionExecutorState>> {
		let state = self.state.borrow();
		match *state {
			Some(_) => Some(cell::Ref::map(state, |inner| {
				inner
					.as_ref()
					.expect("cannot fail, checked in the arm; qed")
			})),
			None => None,
		}
	}
}

struct HostFuncAdapterCallable {
	state_holder: StateHolder,
	host_func: &'static dyn Function,
}

impl HostFuncAdapterCallable {
	fn new(state_holder: StateHolder, host_func: &'static dyn Function) -> Self {
		Self {
			state_holder,
			host_func,
		}
	}
}

impl Callable for HostFuncAdapterCallable {
	fn call(&self, params: &[Val], results: &mut [Val]) -> std::result::Result<(), Trap> {
		let mut substrate_params = params
			.iter()
			.cloned()
			.map(convert_wasmtime_val_to_substrate_value);
		let state = self.state_holder.state.borrow();
		let mut host_func_ctx = state.as_ref().unwrap().materialize(); // TODO: Unwrap

		let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			self.host_func
				.execute(&mut host_func_ctx, &mut substrate_params)
		}));

		let execution_result = match unwind_result {
			Ok(execution_result) => execution_result,
			Err(err) => {
				let msg = match err.downcast::<&'static str>() {
					Ok(msg) => msg.to_string(),
					Err(err) => match err.downcast::<String>() {
						Ok(msg) => *msg,
						Err(_) => "Box<Any>".to_string(),
					},
				};
				return Err(Trap::new(msg));
			}
		};

		match execution_result {
			Ok(Some(ret_val)) => {
				// TODO: Should we check the return type?
				results[0] = convert_substrate_value_to_wasmtime_val(ret_val);
				Ok(())
			}
			Ok(None) => {
				// TODO: Should we check the return type?
				Ok(())
			}
			Err(msg) => Err(Trap::new(msg)),
		}
	}
}

fn wasmtime_func_sig(func: &dyn Function) -> wasmtime::FuncType {
	let params = func
		.signature()
		.args
		.iter()
		.cloned()
		.map(convert_substrate_value_type_to_val_type)
		.collect::<Vec<_>>()
		.into_boxed_slice();
	let results = func
		.signature()
		.return_value
		.iter()
		.cloned()
		.map(convert_substrate_value_type_to_val_type)
		.collect::<Vec<_>>()
		.into_boxed_slice();
	wasmtime::FuncType::new(params, results)
}

fn convert_substrate_value_type_to_val_type(val_ty: ValueType) -> wasmtime::ValType {
	match val_ty {
		ValueType::I32 => wasmtime::ValType::I32,
		ValueType::I64 => wasmtime::ValType::I64,
		_ => todo!(), // TODO:
	}
}

fn convert_wasmtime_val_to_substrate_value(val: Val) -> Value {
	match val {
		Val::I32(v) => Value::I32(v),
		Val::I64(v) => Value::I64(v),
		_ => todo!(), // TODO:
	}
}

fn convert_substrate_value_to_wasmtime_val(value: Value) -> Val {
	match value {
		Value::I32(v) => Val::I32(v),
		Value::I64(v) => Val::I64(v),
		_ => todo!(), // TODO:
	}
}

/// Call a function inside a precompiled Wasm module.
fn call_method(
	store: &Store,
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

	increase_linear_memory(&instance, heap_pages)?;
	let heap_base = extract_heap_base(&instance)?;

	let table = get_table(&instance);
	let memory = get_linear_memory(&instance)?;
	let executor_state = FunctionExecutorState::new(heap_base, memory, table);

	state_holder.set(executor_state);
	let output = {
		let (data_ptr, data_len) = inject_input_data(state_holder, data)?;

		// TODO: Perform the invocation
		let export = instance
			.find_export_by_name(method)
			.ok_or_else(|| Error::from(format!("Exported method {} is not found", method)))?;
		let method_callable = export
			.func()
			.ok_or_else(|| Error::from(format!("Export {} is not a function", method)))?;

		// TODO: Check the signature

		let (output_ptr, output_len) =
			sp_externalities::set_and_run_with_externalities(ext, || {
				match method_callable.call(&[
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
			})?;

		let mut output = vec![0; output_len as usize];
		extract_output_data(state_holder, Pointer::new(output_ptr), &mut output)?;
		output
	};
	state_holder.reset();

	Ok(output)
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

fn increase_linear_memory(instance: &Instance, pages: u32) -> Result<()> {
	let memory = get_linear_memory(instance)?;
	if memory.grow(pages) {
		Ok(())
	} else {
		return Err("failed top increase the linear memory size".into());
	}
}

fn extract_heap_base(instance: &Instance) -> Result<u32> {
	let heap_base_export = instance
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

fn inject_input_data(state_holder: &StateHolder, data: &[u8]) -> Result<(Pointer<u8>, WordSize)> {
	unsafe {
		let state = state_holder.get().unwrap();

		// TODO:
		let data_len = data.len() as WordSize;
		let data_ptr = state
			.allocator
			.borrow_mut()
			.allocate(state.memory.data(), data_len)?;
		write_memory_from(state.memory.data(), data_ptr, data)?;
		Ok((data_ptr, data_len))
	}
}

fn extract_output_data(
	state_holder: &StateHolder,
	ptr: Pointer<u8>,
	output: &mut [u8],
) -> Result<()> {
	unsafe {
		let state = state_holder.get().unwrap();
		read_memory_into(state.memory.data(), ptr, output)?;
	}
	Ok(())
}
