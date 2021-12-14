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

//! This module defines `HostState` and `HostContext` structs which provide logic and state
//! required for execution of host.

use crate::{runtime::StoreData, util};
use codec::{Decode, Encode};
use log::trace;
use sc_allocator::FreeingBumpHeapAllocator;
use sc_executor_common::{
	error::Result,
	sandbox::{self, SupervisorFuncIndex},
	util::MemoryTransfer,
};
use sp_core::sandbox as sandbox_primitives;
use sp_wasm_interface::{FunctionContext, MemoryId, Pointer, Sandbox, WordSize};
use wasmtime::{Caller, Func, Val};

// The sandbox store is inside of a Option<Box<..>>> so that we can temporarily borrow it.
struct SandboxStore(Option<Box<sandbox::Store<Func>>>);

// There are a bunch of `Rc`s within the sandbox store, however we only manipulate
// those within one thread so this should be safe.
unsafe impl Send for SandboxStore {}

/// The state required to construct a HostContext context. The context only lasts for one host
/// call, whereas the state is maintained for the duration of a Wasm runtime call, which may make
/// many different host calls that must share state.
pub struct HostState {
	sandbox_store: SandboxStore,
	allocator: FreeingBumpHeapAllocator,
}

impl HostState {
	/// Constructs a new `HostState`.
	pub fn new(allocator: FreeingBumpHeapAllocator) -> Self {
		HostState {
			sandbox_store: SandboxStore(Some(Box::new(sandbox::Store::new(
				sandbox::SandboxBackend::TryWasmer,
			)))),
			allocator,
		}
	}
}

/// A `HostContext` implements `FunctionContext` for making host calls from a Wasmtime
/// runtime. The `HostContext` exists only for the lifetime of the call and borrows state from
/// a longer-living `HostState`.
pub(crate) struct HostContext<'a> {
	pub(crate) caller: Caller<'a, StoreData>,
}

impl<'a> HostContext<'a> {
	fn host_state(&self) -> &HostState {
		self.caller
			.data()
			.host_state()
			.expect("host state is not empty when calling a function in wasm; qed")
	}

	fn host_state_mut(&mut self) -> &mut HostState {
		self.caller
			.data_mut()
			.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
	}

	fn sandbox_store(&self) -> &sandbox::Store<Func> {
		self.host_state()
			.sandbox_store
			.0
			.as_ref()
			.expect("sandbox store is only empty when temporarily borrowed")
	}

	fn sandbox_store_mut(&mut self) -> &mut sandbox::Store<Func> {
		self.host_state_mut()
			.sandbox_store
			.0
			.as_mut()
			.expect("sandbox store is only empty when temporarily borrowed")
	}
}

impl<'a> sp_wasm_interface::FunctionContext for HostContext<'a> {
	fn read_memory_into(
		&self,
		address: Pointer<u8>,
		dest: &mut [u8],
	) -> sp_wasm_interface::Result<()> {
		util::read_memory_into(&self.caller, address, dest).map_err(|e| e.to_string())
	}

	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> sp_wasm_interface::Result<()> {
		util::write_memory_from(&mut self.caller, address, data).map_err(|e| e.to_string())
	}

	fn allocate_memory(&mut self, size: WordSize) -> sp_wasm_interface::Result<Pointer<u8>> {
		let memory = self.caller.data().memory();
		let (memory, data) = memory.data_and_store_mut(&mut self.caller);
		data.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
			.allocator
			.allocate(memory, size)
			.map_err(|e| e.to_string())
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> sp_wasm_interface::Result<()> {
		let memory = self.caller.data().memory();
		let (memory, data) = memory.data_and_store_mut(&mut self.caller);
		data.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
			.allocator
			.deallocate(memory, ptr)
			.map_err(|e| e.to_string())
	}

	fn sandbox(&mut self) -> &mut dyn Sandbox {
		self
	}
}

impl<'a> Sandbox for HostContext<'a> {
	fn memory_get(
		&mut self,
		memory_id: MemoryId,
		offset: WordSize,
		buf_ptr: Pointer<u8>,
		buf_len: WordSize,
	) -> sp_wasm_interface::Result<u32> {
		let sandboxed_memory = self.sandbox_store().memory(memory_id).map_err(|e| e.to_string())?;

		let len = buf_len as usize;

		let buffer = match sandboxed_memory.read(Pointer::new(offset as u32), len) {
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
			Ok(buffer) => buffer,
		};

		if util::write_memory_from(&mut self.caller, buf_ptr, &buffer).is_err() {
			return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS)
		}

		Ok(sandbox_primitives::ERR_OK)
	}

	fn memory_set(
		&mut self,
		memory_id: MemoryId,
		offset: WordSize,
		val_ptr: Pointer<u8>,
		val_len: WordSize,
	) -> sp_wasm_interface::Result<u32> {
		let sandboxed_memory = self.sandbox_store().memory(memory_id).map_err(|e| e.to_string())?;

		let len = val_len as usize;

		let buffer = match util::read_memory(&self.caller, val_ptr, len) {
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
			Ok(buffer) => buffer,
		};

		if sandboxed_memory.write_from(Pointer::new(offset as u32), &buffer).is_err() {
			return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS)
		}

		Ok(sandbox_primitives::ERR_OK)
	}

	fn memory_teardown(&mut self, memory_id: MemoryId) -> sp_wasm_interface::Result<()> {
		self.sandbox_store_mut().memory_teardown(memory_id).map_err(|e| e.to_string())
	}

	fn memory_new(&mut self, initial: u32, maximum: u32) -> sp_wasm_interface::Result<u32> {
		self.sandbox_store_mut().new_memory(initial, maximum).map_err(|e| e.to_string())
	}

	fn invoke(
		&mut self,
		instance_id: u32,
		export_name: &str,
		args: &[u8],
		return_val: Pointer<u8>,
		return_val_len: u32,
		state: u32,
	) -> sp_wasm_interface::Result<u32> {
		trace!(target: "sp-sandbox", "invoke, instance_idx={}", instance_id);

		// Deserialize arguments and convert them into wasmi types.
		let args = Vec::<sp_wasm_interface::Value>::decode(&mut &args[..])
			.map_err(|_| "Can't decode serialized arguments for the invocation")?
			.into_iter()
			.map(Into::into)
			.collect::<Vec<_>>();

		let instance = self.sandbox_store().instance(instance_id).map_err(|e| e.to_string())?;

		let dispatch_thunk =
			self.sandbox_store().dispatch_thunk(instance_id).map_err(|e| e.to_string())?;

		let result = instance.invoke(
			export_name,
			&args,
			state,
			&mut SandboxContext { host_context: self, dispatch_thunk },
		);

		match result {
			Ok(None) => Ok(sandbox_primitives::ERR_OK),
			Ok(Some(val)) => {
				// Serialize return value and write it back into the memory.
				sp_wasm_interface::ReturnValue::Value(val.into()).using_encoded(|val| {
					if val.len() > return_val_len as usize {
						Err("Return value buffer is too small")?;
					}
					<HostContext as FunctionContext>::write_memory(self, return_val, val)
						.map_err(|_| "can't write return value")?;
					Ok(sandbox_primitives::ERR_OK)
				})
			},
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	}

	fn instance_teardown(&mut self, instance_id: u32) -> sp_wasm_interface::Result<()> {
		self.sandbox_store_mut()
			.instance_teardown(instance_id)
			.map_err(|e| e.to_string())
	}

	fn instance_new(
		&mut self,
		dispatch_thunk_id: u32,
		wasm: &[u8],
		raw_env_def: &[u8],
		state: u32,
	) -> sp_wasm_interface::Result<u32> {
		// Extract a dispatch thunk from the instance's table by the specified index.
		let dispatch_thunk = {
			let table = self
				.caller
				.data()
				.table()
				.ok_or_else(|| "Runtime doesn't have a table; sandbox is unavailable")?;
			let table_item = table.get(&mut self.caller, dispatch_thunk_id);

			table_item
				.ok_or_else(|| "dispatch_thunk_id is out of bounds")?
				.funcref()
				.ok_or_else(|| "dispatch_thunk_idx should be a funcref")?
				.ok_or_else(|| "dispatch_thunk_idx should point to actual func")?
				.clone()
		};

		let guest_env = match sandbox::GuestEnvironment::decode(&self.sandbox_store(), raw_env_def)
		{
			Ok(guest_env) => guest_env,
			Err(_) => return Ok(sandbox_primitives::ERR_MODULE as u32),
		};

		let mut store = self
			.host_state_mut()
			.sandbox_store
			.0
			.take()
			.expect("sandbox store is only empty when borrowed");

		// Catch any potential panics so that we can properly restore the sandbox store
		// which we've destructively borrowed.
		let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			store.instantiate(
				wasm,
				guest_env,
				state,
				&mut SandboxContext { host_context: self, dispatch_thunk: dispatch_thunk.clone() },
			)
		}));

		self.host_state_mut().sandbox_store.0 = Some(store);

		let result = match result {
			Ok(result) => result,
			Err(error) => std::panic::resume_unwind(error),
		};

		let instance_idx_or_err_code = match result {
			Ok(instance) => instance.register(&mut self.sandbox_store_mut(), dispatch_thunk),
			Err(sandbox::InstantiationError::StartTrapped) => sandbox_primitives::ERR_EXECUTION,
			Err(_) => sandbox_primitives::ERR_MODULE,
		};

		Ok(instance_idx_or_err_code as u32)
	}

	fn get_global_val(
		&self,
		instance_idx: u32,
		name: &str,
	) -> sp_wasm_interface::Result<Option<sp_wasm_interface::Value>> {
		self.sandbox_store()
			.instance(instance_idx)
			.map(|i| i.get_global_val(name))
			.map_err(|e| e.to_string())
	}
}

struct SandboxContext<'a, 'b> {
	host_context: &'a mut HostContext<'b>,
	dispatch_thunk: Func,
}

impl<'a, 'b> sandbox::SandboxContext for SandboxContext<'a, 'b> {
	fn invoke(
		&mut self,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		state: u32,
		func_idx: SupervisorFuncIndex,
	) -> Result<i64> {
		let mut ret_vals = [Val::null()];
		let result = self.dispatch_thunk.call(
			&mut self.host_context.caller,
			&[
				Val::I32(u32::from(invoke_args_ptr) as i32),
				Val::I32(invoke_args_len as i32),
				Val::I32(state as i32),
				Val::I32(usize::from(func_idx) as i32),
			],
			&mut ret_vals,
		);

		match result {
			Ok(()) =>
				if let Some(ret_val) = ret_vals[0].i64() {
					Ok(ret_val)
				} else {
					return Err("Supervisor function returned unexpected result!".into())
				},
			Err(err) => Err(err.to_string().into()),
		}
	}

	fn supervisor_context(&mut self) -> &mut dyn FunctionContext {
		self.host_context
	}
}
