// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! This crate provides means for sandboxed execution of wasm modules.
//!
//! In case this crate is used within wasm execution environment
//! then same VM will be used for execution of sandboxed code without
//! comrpomising the security of the sandbox owner.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(lang_items))]
#![cfg_attr(not(feature = "std"), feature(core_intrinsics))]
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_std as rstd;
extern crate substrate_primitives as primitives;

use rstd::prelude::*;

pub use primitives::sandbox::{TypedValue, ReturnValue, HostError};

mod imp {
	#[cfg(feature = "std")]
	include!("../with_std.rs");

	#[cfg(not(feature = "std"))]
	include!("../without_std.rs");
}

/// Error that can occur while using this crate.
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Error {
	/// Module is not valid, couldn't be instantiated or it's `start` function trapped
	/// when executed.
	Module,

	/// Access to a memory or table was made with an address or an index which is out of bounds.
	///
	/// Note that if wasm module makes an out-of-bounds access then trap will occur.
	OutOfBounds,

	/// Failed to invoke an exported function for some reason.
	Execution,
}

impl From<Error> for HostError {
	fn from(_e: Error) -> HostError {
		HostError
	}
}

/// Callable function pointer.
pub type HostFuncType<T> = fn(&mut T, &[TypedValue]) -> Result<ReturnValue, HostError>;

/// Reference to a sandboxed linear memory.
#[derive(Clone)]
pub struct Memory {
	inner: imp::Memory,
}

impl Memory {
	/// Construct a new linear memory instance.
	pub fn new(initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
		Ok(Memory {
			inner: imp::Memory::new(initial, maximum)?,
		})
	}

	/// Read a memory area at the address `ptr` with the size of the provided slice `buf`.
	pub fn get(&self, ptr: u32, buf: &mut [u8]) -> Result<(), Error> {
		self.inner.get(ptr, buf)
	}

	/// Write a memory area at the address `ptr` with contents of the provided slice `buf`.
	pub fn set(&self, ptr: u32, value: &[u8]) -> Result<(), Error> {
		self.inner.set(ptr, value)
	}
}

/// Struct that can be used for defining an environment for a sandboxed module.
///
/// The sandboxed module can access only the entities which were defined and passed
/// to the module at the instantiation time.
pub struct EnvironmentDefinitionBuilder<T> {
	inner: imp::EnvironmentDefinitionBuilder<T>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
	/// Construct a new `EnvironmentDefinitionBuilder`.
	pub fn new() -> EnvironmentDefinitionBuilder<T> {
		EnvironmentDefinitionBuilder {
			inner: imp::EnvironmentDefinitionBuilder::new(),
		}
	}

	/// Register a host function in this environment defintion.
	pub fn add_host_func<N1, N2>(&mut self, module: N1, field: N2, f: HostFuncType<T>)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		self.inner.add_host_func(module, field, f);
	}

	/// Register a memory in this environment definition.
	pub fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		self.inner.add_memory(module, field, mem.inner);
	}
}

/// Sandboxed instance of a wasm module.
///
/// This instance can be used for invoking exported functions.
pub struct Instance<T> {
	inner: imp::Instance<T>,

}

impl<T> Instance<T> {
	/// Instantiate a module with the given [`EnvironmentDefinitionBuilder`].
	///
	/// [`EnvironmentDefinitionBuilder`]: struct.EnvironmentDefinitionBuilder.html
	pub fn new(code: &[u8], env_def_builder: &EnvironmentDefinitionBuilder<T>, state: &mut T) -> Result<Instance<T>, Error> {
		Ok(Instance {
			inner: imp::Instance::new(code, &env_def_builder.inner, state)?,
		})
	}

	/// Invoke an exported function with the given name.
	///
	/// # Errors
	///
	/// Returns `Err(Error::Execution)` if:
	///
	/// - An export function name isn't a proper utf8 byte sequence,
	/// - This module doesn't have an exported function with the given name,
	/// - If types of the arguments passed to the function doesn't match function signature
	///   then trap occurs (as if the exported function was called via call_indirect),
	/// - Trap occured at the execution time.
	pub fn invoke(
		&mut self,
		name: &[u8],
		args: &[TypedValue],
		state: &mut T,
	) -> Result<ReturnValue, Error> {
		self.inner.invoke(name, args, state)
	}
}
