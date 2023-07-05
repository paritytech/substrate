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

use wasmtime::Caller;

use sc_allocator::{AllocationStats, FreeingBumpHeapAllocator};
use sp_wasm_interface::{Pointer, WordSize};

use crate::{instance_wrapper::MemoryWrapper, runtime::StoreData, util};

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
}

impl HostState {
	/// Constructs a new `HostState`.
	pub fn new(allocator: FreeingBumpHeapAllocator) -> Self {
		HostState { allocator: Some(allocator), panic_message: None }
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
}
