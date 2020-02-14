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

//! This module defines `HostState` and `HostContext` structs which provide logic and state
//! required for execution of host.

use codec::{Decode, Encode};
use log::trace;
use sc_executor_common::error::Result;
use sc_executor_common::sandbox::{self, SandboxCapabilities, SupervisorFuncIndex};
use sp_allocator::FreeingBumpHeapAllocator;
use sp_core::sandbox as sandbox_primitives;
use sp_wasm_interface::{FunctionContext, MemoryId, Pointer, Sandbox, WordSize};
use std::cell::RefCell;
use wasmer_runtime_core::memory::Memory;

/// Wrapper type for pointer to a Wasm table entry.
///
/// The wrapper type is used to ensure that the function reference is valid as it must be unsafely
/// dereferenced from within the safe method `<HostContext as SandboxCapabilities>::invoke`.
#[derive(Clone)]
pub struct SupervisorFuncRef(());

/// The state required to construct a HostContext context. The context only lasts for one host
/// call, whereas the state is maintained for the duration of a Wasm runtime call, which may make
/// many different host calls that must share state.
pub struct HostState {
	// We need some interior mutability here since the host state is shared between all host
	// function handlers and the wasmtime backend's `impl WasmRuntime`.
	//
	// Furthermore, because of recursive calls (e.g. runtime can create and call an sandboxed
	// instance which in turn can call the runtime back) we have to be very careful with borrowing
	// those.
	//
	// Basically, most of the interactions should do temporary borrow immediately releasing the
	// borrow after performing necessary queries/changes.
	sandbox_store: RefCell<sandbox::Store<SupervisorFuncRef>>,
	allocator: RefCell<FreeingBumpHeapAllocator>,
	memory: Memory,
}

impl HostState {
	/// Constructs a new `HostState`.
	pub fn new(allocator: FreeingBumpHeapAllocator, memory: Memory) -> Self {
		HostState {
			sandbox_store: RefCell::new(sandbox::Store::new()),
			allocator: RefCell::new(allocator),
			memory,
		}
	}

	// /// Destruct the host state and extract the `InstanceWrapper` passed at the creation.
	// pub fn into_instance(self) -> InstanceWrapper {
	// 	self.instance
	// }

	/// Materialize `HostContext` that can be used to invoke a substrate host `dyn Function`.
	pub fn materialize<'a>(&'a self) -> HostContext<'a> {
		HostContext(self)
	}
}

/// A `HostContext` implements `FunctionContext` for making host calls from a Wasmtime
/// runtime. The `HostContext` exists only for the lifetime of the call and borrows state from
/// a longer-living `HostState`.
pub struct HostContext<'a>(&'a HostState);

impl<'a> std::ops::Deref for HostContext<'a> {
	type Target = HostState;
	fn deref(&self) -> &HostState {
		self.0
	}
}

impl<'a> SandboxCapabilities for HostContext<'a> {
	type SupervisorFuncRef = SupervisorFuncRef;

	fn invoke(
		&mut self,
		dispatch_thunk: &Self::SupervisorFuncRef,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		state: u32,
		func_idx: SupervisorFuncIndex,
	) -> Result<i64> {
		todo!()
	}
}

impl<'a> sp_wasm_interface::FunctionContext for HostContext<'a> {
	fn read_memory_into(
		&self,
		address: Pointer<u8>,
		dest: &mut [u8],
	) -> sp_wasm_interface::Result<()> {
		use std::ops::Deref;
		let view = self.memory.view::<u8>();
		let cell_slice = view.deref();
		let slice: &[u8] = unsafe { std::mem::transmute(cell_slice) };
		let len = dest.len();
		let offset = usize::from(address);
		dest.copy_from_slice(&slice[offset..offset + len]);
		Ok(())
	}

	fn write_memory(&mut self, address: Pointer<u8>, data: &[u8]) -> sp_wasm_interface::Result<()> {
		use std::ops::Deref;
		let view = self.memory.view::<u8>();
		let cell_slice = view.deref();
		#[allow(mutable_transmutes)]
		let slice: &mut [u8] = unsafe { std::mem::transmute(cell_slice) };
		let len = data.len();
		let offset = usize::from(address);
		slice[offset..offset + len].copy_from_slice(data);
		Ok(())
	}

	fn allocate_memory(&mut self, size: WordSize) -> sp_wasm_interface::Result<Pointer<u8>> {
		use std::ops::Deref;
		let view = self.memory.view::<u8>();
		let cell_slice = view.deref();
		#[allow(mutable_transmutes)]
		let slice: &mut [u8] = unsafe { std::mem::transmute(cell_slice) };
		self.allocator
			.borrow_mut()
			.allocate(slice, size)
			.map_err(|e| e.to_string())
	}

	fn deallocate_memory(&mut self, ptr: Pointer<u8>) -> sp_wasm_interface::Result<()> {
		use std::ops::Deref;
		let view = self.memory.view::<u8>();
		let cell_slice = view.deref();
		#[allow(mutable_transmutes)]
		let slice: &mut [u8] = unsafe { std::mem::transmute(cell_slice) };
		self.allocator
			.borrow_mut()
			.deallocate(slice, ptr)
			.map_err(|e| e.to_string())
	}

	fn sandbox(&mut self) -> &mut dyn Sandbox {
		todo!()
	}
}
