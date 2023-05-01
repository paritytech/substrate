// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::{instance_wrapper::MemoryWrapper, runtime::StoreData, util};
use core::ops::ControlFlow;
use sc_allocator::{AllocationStats, FreeingBumpHeapAllocator};
use sp_io::{RiscvExecOutcome, RiscvState};
use sp_wasm_interface::{Pointer, WordSize};
use std::mem::size_of;
use wasmtime::{AsContext, Caller, TypedFunc};

/// The state required to construct a HostContext context. The context only lasts for one host
/// call, whereas the state is maintained for the duration of a Wasm runtime call, which may make
/// many different host calls that must share state.
pub struct HostState {
	/// The allocator instance to keep track of allocated memory.
	///
	/// This is stored as an `Option` as we need to temporarly set this to `None` when we are
	/// allocating/deallocating memory. The problem being that we can only mutable access `caller`
	/// once.
	allocator: Option<FreeingBumpHeapAllocator>,
	panic_message: Option<String>,
	syscalling_riscv_instance: Option<*mut RiscvInstance>,
}

unsafe impl Send for HostState {}

impl HostState {
	/// Constructs a new `HostState`.
	pub fn new(allocator: FreeingBumpHeapAllocator) -> Self {
		HostState {
			allocator: Some(allocator),
			panic_message: None,
			syscalling_riscv_instance: None,
		}
	}

	/// Takes the error message out of the host state, leaving a `None` in its place.
	pub fn take_panic_message(&mut self) -> Option<String> {
		self.panic_message.take()
	}

	pub(crate) fn allocation_stats(&self) -> AllocationStats {
		self.allocator.as_ref()
			.expect("Allocator is always set and only unavailable when doing an allocation/deallocation; qed")
			.stats()
	}
}

/// A `HostContext` implements `FunctionContext` for making host calls from a Wasmtime
/// runtime. The `HostContext` exists only for the lifetime of the call and borrows state from
/// a longer-living `HostState`.
pub(crate) struct HostContext<'a> {
	pub(crate) caller: Caller<'a, StoreData>,
}

impl<'a> HostContext<'a> {
	fn host_state_mut(&mut self) -> &mut HostState {
		self.caller
			.data_mut()
			.host_state_mut()
			.expect("host state is not empty when calling a function in wasm; qed")
	}

	fn syscalling_riscv_instance<'b, 'c>(&'b mut self) -> Option<&'c mut RiscvInstance> {
		self.host_state_mut().syscalling_riscv_instance.map(|i| unsafe { &mut *i })
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
		let mut allocator = self
			.host_state_mut()
			.allocator
			.take()
			.expect("allocator is not empty when calling a function in wasm; qed");

		// We can not return on error early, as we need to store back allocator.
		let res = allocator
			.allocate(&mut MemoryWrapper(&memory, &mut self.caller), size)
			.map_err(|e| e.to_string());

		self.host_state_mut().allocator = Some(allocator);

		res
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> sp_wasm_interface::Result<()> {
		let memory = self.caller.data().memory();
		let mut allocator = self
			.host_state_mut()
			.allocator
			.take()
			.expect("allocator is not empty when calling a function in wasm; qed");

		// We can not return on error early, as we need to store back allocator.
		let res = allocator
			.deallocate(&mut MemoryWrapper(&memory, &mut self.caller), ptr)
			.map_err(|e| e.to_string());

		self.host_state_mut().allocator = Some(allocator);

		res
	}

	fn register_panic_error_message(&mut self, message: &str) {
		self.host_state_mut().panic_message = Some(message.to_owned());
	}

	fn riscv(&mut self) -> &mut dyn sp_wasm_interface::Riscv {
		self
	}
}

impl<'a> sp_wasm_interface::Riscv for HostContext<'a> {
	fn execute(
		&mut self,
		program: &[u8],
		a0: u32,
		syscall_handler: u32,
		state_ptr: u32,
	) -> sp_wasm_interface::Result<u8> {
		// Extract a syscall handler from the instance's table by the specified index.
		let syscall_handler = {
			let table = self
				.caller
				.data()
				.table
				.ok_or("Runtime doesn't have a table; sandbox is unavailable")?;
			let table_item = table.get(&mut self.caller, syscall_handler);

			table_item
				.ok_or("dispatch_thunk_id is out of bounds")?
				.funcref()
				.ok_or("dispatch_thunk_idx should be a funcref")?
				.ok_or("dispatch_thunk_idx should point to actual func")?
				.typed(&mut self.caller)
				.map_err(|_| "dispatch_thunk_idx has the wrong type")?
		};

		let program = riscv::jit::Program::new(program);
		let mut config = riscv::jit::CompileConfig::default();
		config.set_memory_size(2 * 1024 * 1024);
		let module = riscv::jit::Module::compile(&program, config);

		let mut instance = module.instantiate(RiscvContext {
			host_context: self,
			data: RiscvInstance {
				syscall_handler,
				state_ptr,
				trapped: false,
				instance: 0 as *mut _,
			},
		});
		instance.set_reg(riscv::isa::Reg::A0, a0);
		instance.run();

		let outcome = if instance.user().data.trapped {
			RiscvExecOutcome::Trap
		} else {
			RiscvExecOutcome::Ok
		};

		Ok(outcome as u8)
	}

	fn read_memory(
		&mut self,
		offset: u32,
		buf_ptr: u32,
		buf_len: u32,
	) -> sp_wasm_interface::Result<bool> {
		let instance =
			self.syscalling_riscv_instance().ok_or("No riscv instance found")?.instance();
		let offset = offset as usize;
		let Some(buf) =  instance.memory().get(offset..offset.saturating_add(buf_len as usize)) else {
			return Ok(false);
		};
		util::write_memory_from(&mut self.caller, buf_ptr.into(), buf)
			.map_err(|_| "Failed to write memory from the sandboxed instance to the supervisor")?;
		Ok(true)
	}

	fn write_memory(
		&mut self,
		offset: u32,
		buf_ptr: u32,
		buf_len: u32,
	) -> sp_wasm_interface::Result<bool> {
		let instance =
			self.syscalling_riscv_instance().ok_or("No riscv instance found")?.instance();
		let offset = offset as usize;
		let Some(buf) =  instance.memory_mut().get_mut(offset..offset.saturating_add(buf_len as usize)) else {
			return Ok(false);
		};
		util::read_memory_into(&self.caller, buf_ptr.into(), buf)
			.map_err(|_| "Failed to read memory from supervisor")?;
		Ok(true)
	}
}

struct RiscvContext<'a, 'b> {
	host_context: &'a mut HostContext<'b>,
	data: RiscvInstance,
}

struct RiscvInstance {
	syscall_handler: TypedFunc<(u32, u32, u32, u32, u32, u32, u32), u64>,
	instance: *mut riscv::jit::InstanceRef,
	state_ptr: u32,
	trapped: bool,
}

impl<'a, 'b> RiscvContext<'a, 'b> {
	fn shared_state_mut(&mut self) -> Option<&mut RiscvState<()>> {
		let offset = self.data.state_ptr as usize;
		let buf = self
			.host_context
			.caller
			.as_context()
			.data()
			.memory()
			.data_mut(&mut self.host_context.caller);
		let scoped = buf.get_mut(offset..offset.saturating_add(size_of::<RiscvState<()>>()))?;
		unsafe { Some(&mut *(scoped.as_mut_ptr() as *mut _)) }
	}
}

impl RiscvInstance {
	fn instance<'a, 'b>(&'a mut self) -> &'b mut riscv::jit::InstanceRef {
		unsafe { &mut *self.instance }
	}
}

impl<'a, 'b> riscv::jit::UserContext for RiscvContext<'a, 'b> {
	fn on_ecall(&mut self, instance: &mut riscv::jit::InstanceRef) -> ControlFlow<()> {
		use riscv::isa::Reg;

		self.data.instance = instance as *mut _;
		self.host_context
			.caller
			.data_mut()
			.host_state_mut()
			.unwrap()
			.syscalling_riscv_instance = Some(&mut self.data as *mut _);

		let result = self.data.syscall_handler.call(
			&mut self.host_context.caller,
			(
				self.data.state_ptr,
				instance.get_reg(Reg::A0),
				instance.get_reg(Reg::A1),
				instance.get_reg(Reg::A2),
				instance.get_reg(Reg::A3),
				instance.get_reg(Reg::A4),
				instance.get_reg(Reg::A5),
			),
		);

		self.host_context
			.caller
			.data_mut()
			.host_state_mut()
			.unwrap()
			.syscalling_riscv_instance = None;

		match result {
			Err(err) => {
				self.data.trapped = true;
				log::error!("RiscV syscall handler failed: {}", err);
				ControlFlow::Break(())
			},
			Ok(_)
				if self
					.shared_state_mut()
					.expect("shared state ptr was validated when setting up instance; qed")
					.exit =>
				ControlFlow::Break(()),
			Ok(result) => {
				instance.set_reg(Reg::A0, (result & 0xFFFF_FFFF) as u32);
				instance.set_reg(Reg::A1, (result >> 32) as u32);
				ControlFlow::Continue(())
			},
		}
	}

	fn on_unimp(&mut self, _instance: &mut riscv::jit::InstanceRef) {
		self.data.trapped = true;
	}

	fn on_step(&mut self, _instance: &mut riscv::jit::InstanceRef, pc: u32) {
		println!("pc: {:#x}", pc);
	}
}
