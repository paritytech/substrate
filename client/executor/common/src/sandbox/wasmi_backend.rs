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

//! Wasmi specific impls for sandbox

use codec::{Decode, Encode};
use sp_core::sandbox::HostError;
use sp_wasm_interface::{FunctionContext, Pointer, ReturnValue, Value, WordSize};
use std::rc::Rc;

use wasmi::{
	memory_units::Pages, ImportResolver, MemoryInstance, Module, ModuleInstance, RuntimeArgs,
	RuntimeValue, Trap, TrapKind,
};

use crate::{
	error::{self, Error},
	sandbox::{
		BackendInstance, GuestEnvironment, GuestExternals, GuestFuncIndex, Imports,
		InstantiationError, Memory, SandboxContext, SandboxInstance,
	},
	util::{checked_range, MemoryTransfer},
};

environmental::environmental!(SandboxContextStore: trait SandboxContext);

/// Construct trap error from specified message
fn trap(msg: &'static str) -> Trap {
	TrapKind::Host(Box::new(Error::Other(msg.into()))).into()
}

impl ImportResolver for Imports {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &wasmi::Signature,
	) -> std::result::Result<wasmi::FuncRef, wasmi::Error> {
		let idx = self.func_by_name(module_name, field_name).ok_or_else(|| {
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		})?;

		Ok(wasmi::FuncInstance::alloc_host(signature.clone(), idx.0))
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &wasmi::MemoryDescriptor,
	) -> std::result::Result<wasmi::MemoryRef, wasmi::Error> {
		let mem = self.memory_by_name(module_name, field_name).ok_or_else(|| {
			wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name))
		})?;

		let wrapper = mem.as_wasmi().ok_or_else(|| {
			wasmi::Error::Instantiation(format!(
				"Unsupported non-wasmi export {}:{}",
				module_name, field_name
			))
		})?;

		// Here we use inner memory reference only to resolve the imports
		// without accessing the memory contents. All subsequent memory accesses
		// should happen through the wrapper, that enforces the memory access protocol.
		let mem = wrapper.0.clone();

		Ok(mem)
	}

	fn resolve_global(
		&self,
		module_name: &str,
		field_name: &str,
		_global_type: &wasmi::GlobalDescriptor,
	) -> std::result::Result<wasmi::GlobalRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name)))
	}

	fn resolve_table(
		&self,
		module_name: &str,
		field_name: &str,
		_table_type: &wasmi::TableDescriptor,
	) -> std::result::Result<wasmi::TableRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!("Export {}:{} not found", module_name, field_name)))
	}
}

/// Allocate new memory region
pub fn new_memory(initial: u32, maximum: Option<u32>) -> crate::error::Result<Memory> {
	let memory = Memory::Wasmi(MemoryWrapper::new(
		MemoryInstance::alloc(Pages(initial as usize), maximum.map(|m| Pages(m as usize)))
			.map_err(|error| Error::Sandbox(error.to_string()))?,
	));

	Ok(memory)
}

/// Wasmi provides direct access to its memory using slices.
///
/// This wrapper limits the scope where the slice can be taken to
#[derive(Debug, Clone)]
pub struct MemoryWrapper(wasmi::MemoryRef);

impl MemoryWrapper {
	/// Take ownership of the memory region and return a wrapper object
	fn new(memory: wasmi::MemoryRef) -> Self {
		Self(memory)
	}
}

impl MemoryTransfer for MemoryWrapper {
	fn read(&self, source_addr: Pointer<u8>, size: usize) -> error::Result<Vec<u8>> {
		self.0.with_direct_access(|source| {
			let range = checked_range(source_addr.into(), size, source.len())
				.ok_or_else(|| error::Error::Other("memory read is out of bounds".into()))?;

			Ok(Vec::from(&source[range]))
		})
	}

	fn read_into(&self, source_addr: Pointer<u8>, destination: &mut [u8]) -> error::Result<()> {
		self.0.with_direct_access(|source| {
			let range = checked_range(source_addr.into(), destination.len(), source.len())
				.ok_or_else(|| error::Error::Other("memory read is out of bounds".into()))?;

			destination.copy_from_slice(&source[range]);
			Ok(())
		})
	}

	fn write_from(&self, dest_addr: Pointer<u8>, source: &[u8]) -> error::Result<()> {
		self.0.with_direct_access_mut(|destination| {
			let range = checked_range(dest_addr.into(), source.len(), destination.len())
				.ok_or_else(|| error::Error::Other("memory write is out of bounds".into()))?;

			destination[range].copy_from_slice(source);
			Ok(())
		})
	}
}

impl<'a> wasmi::Externals for GuestExternals<'a> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> std::result::Result<Option<RuntimeValue>, Trap> {
		SandboxContextStore::with(|sandbox_context| {
			// Make `index` typesafe again.
			let index = GuestFuncIndex(index);

			// Convert function index from guest to supervisor space
			let func_idx = self.sandbox_instance
				.guest_to_supervisor_mapping
				.func_by_guest_index(index)
				.expect(
					"`invoke_index` is called with indexes registered via `FuncInstance::alloc_host`;
					`FuncInstance::alloc_host` is called with indexes that were obtained from `guest_to_supervisor_mapping`;
					`func_by_guest_index` called with `index` can't return `None`;
					qed"
				);

			// Serialize arguments into a byte vector.
			let invoke_args_data: Vec<u8> = args
				.as_ref()
				.iter()
				.cloned()
				.map(sp_wasm_interface::Value::from)
				.collect::<Vec<_>>()
				.encode();

			let state = self.state;

			// Move serialized arguments inside the memory, invoke dispatch thunk and
			// then free allocated memory.
			let invoke_args_len = invoke_args_data.len() as WordSize;
			let invoke_args_ptr = sandbox_context
				.supervisor_context()
				.allocate_memory(invoke_args_len)
				.map_err(|_| trap("Can't allocate memory in supervisor for the arguments"))?;

			let deallocate = |supervisor_context: &mut dyn FunctionContext, ptr, fail_msg| {
				supervisor_context.deallocate_memory(ptr).map_err(|_| trap(fail_msg))
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
				return Err(trap("Can't write invoke args into memory"))
			}

			let result = sandbox_context.invoke(
				invoke_args_ptr,
				invoke_args_len,
				state,
				func_idx,
			);

			deallocate(
				sandbox_context.supervisor_context(),
				invoke_args_ptr,
				"Can't deallocate memory for dispatch thunk's invoke arguments",
			)?;
			let result = result?;

			// dispatch_thunk returns pointer to serialized arguments.
			// Unpack pointer and len of the serialized result data.
			let (serialized_result_val_ptr, serialized_result_val_len) = {
				// Cast to u64 to use zero-extension.
				let v = result as u64;
				let ptr = (v as u64 >> 32) as u32;
				let len = (v & 0xFFFFFFFF) as u32;
				(Pointer::new(ptr), len)
			};

			let serialized_result_val = sandbox_context
				.supervisor_context()
				.read_memory(serialized_result_val_ptr, serialized_result_val_len)
				.map_err(|_| trap("Can't read the serialized result from dispatch thunk"));

			deallocate(
				sandbox_context.supervisor_context(),
				serialized_result_val_ptr,
				"Can't deallocate memory for dispatch thunk's result",
			)
			.and_then(|_| serialized_result_val)
			.and_then(|serialized_result_val| {
				let result_val = std::result::Result::<ReturnValue, HostError>::decode(&mut serialized_result_val.as_slice())
					.map_err(|_| trap("Decoding Result<ReturnValue, HostError> failed!"))?;

				match result_val {
					Ok(return_value) => Ok(match return_value {
						ReturnValue::Unit => None,
						ReturnValue::Value(typed_value) => Some(RuntimeValue::from(typed_value)),
					}),
					Err(HostError) => Err(trap("Supervisor function returned sandbox::HostError")),
				}
			})
		}).expect("SandboxContextStore is set when invoking sandboxed functions; qed")
	}
}

fn with_guest_externals<R, F>(sandbox_instance: &SandboxInstance, state: u32, f: F) -> R
where
	F: FnOnce(&mut GuestExternals) -> R,
{
	f(&mut GuestExternals { sandbox_instance, state })
}

/// Instantiate a module within a sandbox context
pub fn instantiate(
	wasm: &[u8],
	guest_env: GuestEnvironment,
	state: u32,
	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Rc<SandboxInstance>, InstantiationError> {
	let wasmi_module = Module::from_buffer(wasm).map_err(|_| InstantiationError::ModuleDecoding)?;
	let wasmi_instance = ModuleInstance::new(&wasmi_module, &guest_env.imports)
		.map_err(|_| InstantiationError::Instantiation)?;

	let sandbox_instance = Rc::new(SandboxInstance {
		// In general, it's not a very good idea to use `.not_started_instance()` for
		// anything but for extracting memory and tables. But in this particular case, we
		// are extracting for the purpose of running `start` function which should be ok.
		backend_instance: BackendInstance::Wasmi(wasmi_instance.not_started_instance().clone()),
		guest_to_supervisor_mapping: guest_env.guest_to_supervisor_mapping,
	});

	with_guest_externals(&sandbox_instance, state, |guest_externals| {
		SandboxContextStore::using(sandbox_context, || {
			wasmi_instance
				.run_start(guest_externals)
				.map_err(|_| InstantiationError::StartTrapped)
		})
	})?;

	Ok(sandbox_instance)
}

/// Invoke a function within a sandboxed module
pub fn invoke(
	instance: &SandboxInstance,
	module: &wasmi::ModuleRef,
	export_name: &str,
	args: &[Value],
	state: u32,
	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Option<Value>, error::Error> {
	with_guest_externals(instance, state, |guest_externals| {
		SandboxContextStore::using(sandbox_context, || {
			let args = args.iter().cloned().map(Into::into).collect::<Vec<_>>();

			module
				.invoke_export(export_name, &args, guest_externals)
				.map(|result| result.map(Into::into))
				.map_err(|error| error::Error::Sandbox(error.to_string()))
		})
	})
}

/// Get global value by name
pub fn get_global(instance: &wasmi::ModuleRef, name: &str) -> Option<Value> {
	Some(instance.export_by_name(name)?.as_global()?.get().into())
}
