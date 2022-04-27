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

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use wasmer::RuntimeError;

use codec::{Decode, Encode};
use sp_sandbox::HostError;
use sp_wasm_interface::{FunctionContext, Pointer, ReturnValue, Value, WordSize};

use crate::{
	error::{Error, Result},
	sandbox::{
		BackendInstance, GuestEnvironment, InstantiationError, Memory, SandboxContext,
		SandboxInstance, SupervisorFuncIndex,
	},
	util::{checked_range, MemoryTransfer},
};

environmental::environmental!(SandboxContextStore: trait SandboxContext);

/// Wasmer specific context
pub struct Backend {
	store: wasmer::Store,
}

impl Backend {
	pub fn new() -> Self {
		let compiler = wasmer::Singlepass::default();
		Backend { store: wasmer::Store::new(&wasmer::Universal::new(compiler).engine()) }
	}
}

/// Invoke a function within a sandboxed module
pub fn invoke(
	instance: &wasmer::Instance,
	export_name: &str,
	args: &[Value],
	_state: u32,
	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Option<Value>, Error> {
	let function = instance
		.exports
		.get_function(export_name)
		.map_err(|error| Error::Sandbox(error.to_string()))?;

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
		function.call(&args).map_err(|error| Error::Sandbox(error.to_string()))
	})?;

	match wasmer_result.as_ref() {
		[] => Ok(None),

		[wasm_value] => {
			let wasmer_value = match *wasm_value {
				wasmer::Val::I32(val) => Value::I32(val),
				wasmer::Val::I64(val) => Value::I64(val),
				wasmer::Val::F32(val) => Value::F32(f32::to_bits(val)),
				wasmer::Val::F64(val) => Value::F64(f64::to_bits(val)),
				_ =>
					return Err(Error::Sandbox(format!(
						"Unsupported return value: {:?}",
						wasm_value,
					))),
			};

			Ok(Some(wasmer_value))
		},

		_ => Err(Error::Sandbox("multiple return types are not supported yet".into())),
	}
}

/// Instantiate a module within a sandbox context
pub fn instantiate(
	context: &Backend,
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

				let wasmer_memory_ref = memory.as_wasmer().expect(
					"memory is created by wasmer; \
					exported by the same module and backend; \
					thus the operation can't fail; \
					qed",
				);

				// This is safe since we're only instantiating the module and populating
				// the export table, so no memory access can happen at this time.
				// All subsequent memory accesses should happen through the wrapper,
				// that enforces the memory access protocol.
				//
				// We take exclusive lock to ensure that we're the only one here,
				// since during instantiation phase the memory should only be created
				// and not yet accessed.
				let wasmer_memory = wasmer_memory_ref
					.buffer
					.try_borrow_mut()
					.map_err(|_| InstantiationError::EnvironmentDefinitionCorrupted)?
					.clone();

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

				let function =
					dispatch_function(supervisor_func_index, &context.store, func_ty, state);

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
			wasmer::InstantiationError::CpuFeature(_) => InstantiationError::CpuFeature,
		})
	})?;

	Ok(Rc::new(SandboxInstance {
		backend_instance: BackendInstance::Wasmer(instance),
		guest_to_supervisor_mapping: guest_env.guest_to_supervisor_mapping,
	}))
}

fn dispatch_function(
	supervisor_func_index: SupervisorFuncIndex,
	store: &wasmer::Store,
	func_ty: &wasmer::FunctionType,
	state: u32,
) -> wasmer::Function {
	wasmer::Function::new(store, func_ty, move |params| {
		SandboxContextStore::with(|sandbox_context| {
			// Serialize arguments into a byte vector.
			let invoke_args_data = params
				.iter()
				.map(|val| match val {
					wasmer::Val::I32(val) => Ok(Value::I32(*val)),
					wasmer::Val::I64(val) => Ok(Value::I64(*val)),
					wasmer::Val::F32(val) => Ok(Value::F32(f32::to_bits(*val))),
					wasmer::Val::F64(val) => Ok(Value::F64(f64::to_bits(*val))),
					_ =>
						Err(RuntimeError::new(format!("Unsupported function argument: {:?}", val))),
				})
				.collect::<std::result::Result<Vec<_>, _>>()?
				.encode();

			// Move serialized arguments inside the memory, invoke dispatch thunk and
			// then free allocated memory.
			let invoke_args_len = invoke_args_data.len() as WordSize;
			let invoke_args_ptr =
				sandbox_context.supervisor_context().allocate_memory(invoke_args_len).map_err(
					|_| RuntimeError::new("Can't allocate memory in supervisor for the arguments"),
				)?;

			let deallocate = |fe: &mut dyn FunctionContext, ptr, fail_msg| {
				fe.deallocate_memory(ptr).map_err(|_| RuntimeError::new(fail_msg))
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

				return Err(RuntimeError::new("Can't write invoke args into memory"))
			}

			// Perform the actuall call
			let serialized_result = sandbox_context
				.invoke(invoke_args_ptr, invoke_args_len, state, supervisor_func_index)
				.map_err(|e| RuntimeError::new(e.to_string()));

			deallocate(
				sandbox_context.supervisor_context(),
				invoke_args_ptr,
				"Failed dealloction after invoke",
			)?;

			let serialized_result = serialized_result?;

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
					RuntimeError::new("Can't read the serialized result from dispatch thunk")
				});

			deallocate(
				sandbox_context.supervisor_context(),
				serialized_result_val_ptr,
				"Can't deallocate memory for dispatch thunk's result",
			)?;

			let serialized_result_val = serialized_result_val?;

			let deserialized_result = std::result::Result::<ReturnValue, HostError>::decode(
				&mut serialized_result_val.as_slice(),
			)
			.map_err(|_| RuntimeError::new("Decoding Result<ReturnValue, HostError> failed!"))?
			.map_err(|_| RuntimeError::new("Supervisor function returned sandbox::HostError"))?;

			let result = match deserialized_result {
				ReturnValue::Value(Value::I32(val)) => vec![wasmer::Val::I32(val)],
				ReturnValue::Value(Value::I64(val)) => vec![wasmer::Val::I64(val)],
				ReturnValue::Value(Value::F32(val)) => vec![wasmer::Val::F32(f32::from_bits(val))],
				ReturnValue::Value(Value::F64(val)) => vec![wasmer::Val::F64(f64::from_bits(val))],

				ReturnValue::Unit => vec![],
			};

			Ok(result)
		})
		.expect("SandboxContextStore is set when invoking sandboxed functions; qed")
	})
}

/// Allocate new memory region
pub fn new_memory(
	context: &Backend,
	initial: u32,
	maximum: Option<u32>,
) -> crate::error::Result<Memory> {
	let ty = wasmer::MemoryType::new(initial, maximum, false);
	let memory = Memory::Wasmer(MemoryWrapper::new(
		wasmer::Memory::new(&context.store, ty).map_err(|_| Error::InvalidMemoryReference)?,
	));

	Ok(memory)
}

/// In order to enforce memory access protocol to the backend memory
/// we wrap it with `RefCell` and encapsulate all memory operations.
#[derive(Debug, Clone)]
pub struct MemoryWrapper {
	buffer: Rc<RefCell<wasmer::Memory>>,
}

impl MemoryWrapper {
	/// Take ownership of the memory region and return a wrapper object
	pub fn new(memory: wasmer::Memory) -> Self {
		Self { buffer: Rc::new(RefCell::new(memory)) }
	}

	/// Returns linear memory of the wasm instance as a slice.
	///
	/// # Safety
	///
	/// Wasmer doesn't provide comprehensive documentation about the exact behavior of the data
	/// pointer. If a dynamic style heap is used the base pointer of the heap can change. Since
	/// growing, we cannot guarantee the lifetime of the returned slice reference.
	unsafe fn memory_as_slice(memory: &wasmer::Memory) -> &[u8] {
		let ptr = memory.data_ptr() as *const _;

		let len: usize = memory.data_size().try_into().expect(
			"maximum memory object size never exceeds pointer size on any architecture; \
			usize by design and definition is enough to store any memory object size \
			possible on current achitecture; thus the conversion can not fail; qed",
		);

		if len == 0 {
			&[]
		} else {
			core::slice::from_raw_parts(ptr, len)
		}
	}

	/// Returns linear memory of the wasm instance as a slice.
	///
	/// # Safety
	///
	/// See `[memory_as_slice]`. In addition to those requirements, since a mutable reference is
	/// returned it must be ensured that only one mutable and no shared references to memory
	/// exists at the same time.
	unsafe fn memory_as_slice_mut(memory: &mut wasmer::Memory) -> &mut [u8] {
		let ptr = memory.data_ptr();

		let len: usize = memory.data_size().try_into().expect(
			"maximum memory object size never exceeds pointer size on any architecture; \
			usize by design and definition is enough to store any memory object size \
			possible on current achitecture; thus the conversion can not fail; qed",
		);

		if len == 0 {
			&mut []
		} else {
			core::slice::from_raw_parts_mut(ptr, len)
		}
	}
}

impl MemoryTransfer for MemoryWrapper {
	fn read(&self, source_addr: Pointer<u8>, size: usize) -> Result<Vec<u8>> {
		let memory = self.buffer.borrow();

		let data_size: usize = memory.data_size().try_into().expect(
			"maximum memory object size never exceeds pointer size on any architecture; \
			usize by design and definition is enough to store any memory object size \
			possible on current achitecture; thus the conversion can not fail; qed",
		);

		let range = checked_range(source_addr.into(), size, data_size)
			.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;

		let mut buffer = vec![0; range.len()];
		self.read_into(source_addr, &mut buffer)?;

		Ok(buffer)
	}

	fn read_into(&self, source_addr: Pointer<u8>, destination: &mut [u8]) -> Result<()> {
		unsafe {
			let memory = self.buffer.borrow();

			// This should be safe since we don't grow up memory while caching this reference
			// and we give up the reference before returning from this function.
			let source = Self::memory_as_slice(&memory);

			let range = checked_range(source_addr.into(), destination.len(), source.len())
				.ok_or_else(|| Error::Other("memory read is out of bounds".into()))?;

			destination.copy_from_slice(&source[range]);
			Ok(())
		}
	}

	fn write_from(&self, dest_addr: Pointer<u8>, source: &[u8]) -> Result<()> {
		unsafe {
			let memory = &mut self.buffer.borrow_mut();

			// This should be safe since we don't grow up memory while caching this reference
			// and we give up the reference before returning from this function.
			let destination = Self::memory_as_slice_mut(memory);

			let range = checked_range(dest_addr.into(), source.len(), destination.len())
				.ok_or_else(|| Error::Other("memory write is out of bounds".into()))?;

			destination[range].copy_from_slice(source);
			Ok(())
		}
	}
}

/// Get global value by name
pub fn get_global(instance: &wasmer::Instance, name: &str) -> Option<Value> {
	let global = instance.exports.get_global(name).ok()?;
	let wasmtime_value = match global.get() {
		wasmer::Val::I32(val) => Value::I32(val),
		wasmer::Val::I64(val) => Value::I64(val),
		wasmer::Val::F32(val) => Value::F32(f32::to_bits(val)),
		wasmer::Val::F64(val) => Value::F64(f64::to_bits(val)),
		_ => None?,
	};

	Some(wasmtime_value)
}
