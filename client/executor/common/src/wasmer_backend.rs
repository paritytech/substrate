// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Wasmer specific impls for sandbox

use codec::Encode;
use sp_wasm_interface::{Value, Pointer, WordSize, FunctionContext};
use wasmi::RuntimeValue;
use std::{rc::Rc, collections::HashMap};

use crate::sandbox::{SandboxContext, InstantiationError, WasmerBackend, GuestEnvironment, SandboxInstance, SupervisorFuncIndex, deserialize_result, BackendInstance};

environmental::environmental!(SandboxContextStore: trait SandboxContext);

pub fn invoke_wasmer(
	instance: &wasmer::Instance,

	// function to call that is exported from the module
	export_name: &str,

	// arguments passed to the function
	args: &[Value],

	// arbitraty context data of the call
	state: u32,

	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Option<Value>, wasmi::Error> {
	let function = instance
		.exports
		.get_function(export_name)
		.map_err(|error| wasmi::Error::Function(error.to_string()))?;

	let args: Vec<wasmer::Val> = args
		.iter()
		.map(|v| match *v {
			Value::I32(val) => wasmer::Val::I32(val),
			Value::I64(val) => wasmer::Val::I64(val),
			Value::F32(val) => wasmer::Val::F32(f32::from_bits(val)),
			Value::F64(val) => wasmer::Val::F64(f64::from_bits(val)),
		})
		.collect();

	let wasmer_result = SandboxContextStore::using(sandbox_context, || {
		function.call(&args).map_err(|error| wasmi::Error::Function(error.to_string()))
	})?;

	if wasmer_result.len() > 1 {
		return Err(wasmi::Error::Function(
			"multiple return types are not supported yet".into(),
		))
	}

	wasmer_result
		.first()
		.map(|wasm_value| {
			let wasmer_value = match *wasm_value {
				wasmer::Val::I32(val) => Value::I32(val),
				wasmer::Val::I64(val) => Value::I64(val),
				wasmer::Val::F32(val) => Value::F32(f32::to_bits(val)),
				wasmer::Val::F64(val) => Value::F64(f64::to_bits(val)),
				_ =>
					return Err(wasmi::Error::Function(format!(
						"Unsupported return value: {:?}",
						wasm_value,
					))),
			};

			Ok(wasmer_value)
		})
		.transpose()
}

pub fn instantiate_wasmer(
	context: &WasmerBackend,
	wasm: &[u8],
	guest_env: GuestEnvironment,
	state: u32,
	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Rc<SandboxInstance>, InstantiationError> {
	let module = wasmer::Module::new(&context.store, wasm)
		.map_err(|_| InstantiationError::ModuleDecoding)?;

	type Exports = HashMap<String, wasmer::Exports>;
	let mut exports_map = Exports::new();

	for import in module.imports().into_iter() {
		match import.ty() {
			// Nothing to do here
			wasmer::ExternType::Global(_) | wasmer::ExternType::Table(_) => (),

			wasmer::ExternType::Memory(_) => {
				let exports = exports_map
					.entry(import.module().to_string())
					.or_insert(wasmer::Exports::new());

				let memory = guest_env
					.imports
					.memory_by_name(import.module(), import.name())
					.ok_or(InstantiationError::ModuleDecoding)?;

				let mut wasmer_memory_ref = memory.as_wasmer().expect(
					"memory is created by wasmer; \
					exported by the same module and backend; \
					thus the operation can't fail; \
					qed",
				);

				// This is safe since we're only instantiating the module and populating
				// the export table, so no memory access can happen at this time.
				// All subsequent memory accesses should happen through the wrapper,
				// that enforces the memory access protocol.
				let wasmer_memory = unsafe { wasmer_memory_ref.clone_inner() };

				exports.insert(import.name(), wasmer::Extern::Memory(wasmer_memory));
			},

			wasmer::ExternType::Function(func_ty) => {
				let guest_func_index =
					guest_env.imports.func_by_name(import.module(), import.name());

				let guest_func_index = if let Some(index) = guest_func_index {
					index
				} else {
					// Missing import (should we abort here?)
					continue
				};

				let supervisor_func_index = guest_env
					.guest_to_supervisor_mapping
					.func_by_guest_index(guest_func_index)
					.ok_or(InstantiationError::ModuleDecoding)?;

				let function = wasmer_dispatch_function(
					supervisor_func_index,
					&context.store,
					func_ty,
					state,
				);

				let exports = exports_map
					.entry(import.module().to_string())
					.or_insert(wasmer::Exports::new());

				exports.insert(import.name(), wasmer::Extern::Function(function));
			},
		}
	}

	let mut import_object = wasmer::ImportObject::new();
	for (module_name, exports) in exports_map.into_iter() {
		import_object.register(module_name, exports);
	}

	let instance = SandboxContextStore::using(sandbox_context, || {
		wasmer::Instance::new(&module, &import_object).map_err(|error| match error {
			wasmer::InstantiationError::Link(_) => InstantiationError::Instantiation,
			wasmer::InstantiationError::Start(_) => InstantiationError::StartTrapped,
			wasmer::InstantiationError::HostEnvInitialization(_) =>
				InstantiationError::EnvironmentDefinitionCorrupted,
		})
	})?;

	Ok(Rc::new(SandboxInstance {
		backend_instance: BackendInstance::Wasmer(instance),
		guest_to_supervisor_mapping: guest_env.guest_to_supervisor_mapping,
	}))
}

pub fn wasmer_dispatch_function(
	supervisor_func_index: SupervisorFuncIndex,
	store: &wasmer::Store,
	func_ty: &wasmer::FunctionType,
	state: u32,
) -> wasmer::Function {
	wasmer::Function::new(store, func_ty, move |params| {
		SandboxContextStore::with(|sandbox_context| {
			use sp_wasm_interface::Value;

			// Serialize arguments into a byte vector.
			let invoke_args_data = params
				.iter()
				.map(|val| match val {
					wasmer::Val::I32(val) => Ok(Value::I32(*val)),
					wasmer::Val::I64(val) => Ok(Value::I64(*val)),
					wasmer::Val::F32(val) => Ok(Value::F32(f32::to_bits(*val))),
					wasmer::Val::F64(val) => Ok(Value::F64(f64::to_bits(*val))),
					_ => Err(wasmer::RuntimeError::new(format!(
						"Unsupported function argument: {:?}",
						val
					))),
				})
				.collect::<std::result::Result<Vec<_>, _>>()?
				.encode();

			// Move serialized arguments inside the memory, invoke dispatch thunk and
			// then free allocated memory.
			let invoke_args_len = invoke_args_data.len() as WordSize;
			let invoke_args_ptr = sandbox_context
				.supervisor_context()
				.allocate_memory(invoke_args_len)
				.map_err(|_| {
					wasmer::RuntimeError::new(
						"Can't allocate memory in supervisor for the arguments",
					)
				})?;

			let deallocate = |fe: &mut dyn FunctionContext, ptr, fail_msg| {
				fe.deallocate_memory(ptr).map_err(|_| wasmer::RuntimeError::new(fail_msg))
			};

			if sandbox_context
				.supervisor_context()
				.write_memory(invoke_args_ptr, &invoke_args_data)
				.is_err()
			{
				deallocate(
					sandbox_context.supervisor_context(),
					invoke_args_ptr,
					"Failed dealloction after failed write of invoke arguments",
				)?;

				return Err(wasmer::RuntimeError::new("Can't write invoke args into memory"))
			}

			// Perform the actuall call
			let serialized_result = sandbox_context
				.invoke(invoke_args_ptr, invoke_args_len, state, supervisor_func_index)
				.map_err(|e| wasmer::RuntimeError::new(e.to_string()))?;

			// dispatch_thunk returns pointer to serialized arguments.
			// Unpack pointer and len of the serialized result data.
			let (serialized_result_val_ptr, serialized_result_val_len) = {
				// Cast to u64 to use zero-extension.
				let v = serialized_result as u64;
				let ptr = (v as u64 >> 32) as u32;
				let len = (v & 0xFFFFFFFF) as u32;
				(Pointer::new(ptr), len)
			};

			let serialized_result_val = sandbox_context
				.supervisor_context()
				.read_memory(serialized_result_val_ptr, serialized_result_val_len)
				.map_err(|_| {
					wasmer::RuntimeError::new(
						"Can't read the serialized result from dispatch thunk",
					)
				});

			let deserialized_result = deallocate(
				sandbox_context.supervisor_context(),
				serialized_result_val_ptr,
				"Can't deallocate memory for dispatch thunk's result",
			)
			.and_then(|_| serialized_result_val)
			.and_then(|serialized_result_val| {
				deserialize_result(&serialized_result_val)
					.map_err(|e| wasmer::RuntimeError::new(e.to_string()))
			})?;

			if let Some(value) = deserialized_result {
				Ok(vec![match value {
					RuntimeValue::I32(val) => wasmer::Val::I32(val),
					RuntimeValue::I64(val) => wasmer::Val::I64(val),
					RuntimeValue::F32(val) => wasmer::Val::F32(val.into()),
					RuntimeValue::F64(val) => wasmer::Val::F64(val.into()),
				}])
			} else {
				Ok(vec![])
			}
		})
		.expect("SandboxContextStore is set when invoking sandboxed functions; qed")
	})
}
