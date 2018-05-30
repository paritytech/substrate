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

use rstd::prelude::*;
use rstd::{slice, marker, mem};
use codec::Slicable;
use primitives::sandbox as sandbox_primitives;
use super::{Error, TypedValue, ReturnValue, HostFuncType};

mod ffi {
	use rstd::mem;
	use super::HostFuncType;

	/// Index into the default table that points to a `HostFuncType`.
	pub type HostFuncIndex = usize;

	/// Coerce `HostFuncIndex` to a callable host function pointer.
	///
	/// # Safety
	///
	/// This function should be only called with a `HostFuncIndex` that was previously registered
	/// in the environment defintion. Typically this should only
	/// be called with an argument received in `dispatch_thunk`.
	pub unsafe fn coerce_host_index_to_func<T>(idx: HostFuncIndex) -> HostFuncType<T> {
		// We need to ensure that sizes of a callable function pointer and host function index is
		// indeed equal.
		// We can't use `static_assertions` create because it makes compiler panic, fallback to runtime assert.
		// const_assert!(mem::size_of::<HostFuncIndex>() == mem::size_of::<HostFuncType<T>>(),);
		assert!(mem::size_of::<HostFuncIndex>() == mem::size_of::<HostFuncType<T>>());
		mem::transmute::<HostFuncIndex, HostFuncType<T>>(idx)
	}

	extern "C" {
		pub fn ext_sandbox_instantiate(
			dispatch_thunk: extern "C" fn(
				serialized_args_ptr: *const u8,
				serialized_args_len: usize,
				state: usize,
				f: HostFuncIndex,
			) -> u64,
			wasm_ptr: *const u8,
			wasm_len: usize,
			imports_ptr: *const u8,
			imports_len: usize,
			state: usize,
		) -> u32;
		pub fn ext_sandbox_invoke(
			instance_idx: u32,
			export_ptr: *const u8,
			export_len: usize,
			args_ptr: *const u8,
			args_len: usize,
			state: usize,
		) -> u32;
		pub fn ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32;
		pub fn ext_sandbox_memory_get(
			memory_idx: u32,
			offset: u32,
			buf_ptr: *mut u8,
			buf_len: usize,
		) -> u32;
		pub fn ext_sandbox_memory_set(
			memory_idx: u32,
			offset: u32,
			val_ptr: *const u8,
			val_len: usize,
		) -> u32;
		pub fn ext_sandbox_memory_teardown(
			memory_idx: u32,
		);
		pub fn ext_sandbox_instance_teardown(
			instance_idx: u32,
		);
	}
}

#[derive(Clone)]
pub struct Memory {
	memory_idx: u32,
}

impl Memory {
	pub fn new(initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
		let result = unsafe {
			let maximum = if let Some(maximum) = maximum {
				maximum
			} else {
				sandbox_primitives::MEM_UNLIMITED
			};
			ffi::ext_sandbox_memory_new(initial, maximum)
		};
		match result {
			sandbox_primitives::ERR_MODULE => Err(Error::Module),
			memory_idx => Ok(Memory { memory_idx }),
		}
	}

	pub fn get(&self, offset: u32, buf: &mut [u8]) -> Result<(), Error> {
		let result = unsafe { ffi::ext_sandbox_memory_get(self.memory_idx, offset, buf.as_mut_ptr(), buf.len()) };
		match result {
			sandbox_primitives::ERR_OK => Ok(()),
			sandbox_primitives::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
			_ => unreachable!(),
		}
	}

	pub fn set(&self, offset: u32, val: &[u8]) -> Result<(), Error> {
		let result = unsafe { ffi::ext_sandbox_memory_set(self.memory_idx, offset, val.as_ptr(), val.len()) };
		match result {
			sandbox_primitives::ERR_OK => Ok(()),
			sandbox_primitives::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
			_ => unreachable!(),
		}
	}
}

impl Drop for Memory {
	fn drop(&mut self) {
		unsafe {
			ffi::ext_sandbox_memory_teardown(self.memory_idx);
		}
	}
}

pub struct EnvironmentDefinitionBuilder<T> {
	env_def: sandbox_primitives::EnvironmentDefinition,
	_marker: marker::PhantomData<T>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
	pub fn new() -> EnvironmentDefinitionBuilder<T> {
		EnvironmentDefinitionBuilder {
			env_def: sandbox_primitives::EnvironmentDefinition {
				entries: Vec::new(),
			},
			_marker: marker::PhantomData::<T>,
		}
	}

	fn add_entry<N1, N2>(
		&mut self,
		module: N1,
		field: N2,
		extern_entity: sandbox_primitives::ExternEntity,
	) where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		let entry = sandbox_primitives::Entry {
			module_name: module.into(),
			field_name: field.into(),
			entity: extern_entity,
		};
		self.env_def.entries.push(entry);
	}

	pub fn add_host_func<N1, N2>(&mut self, module: N1, field: N2, f: HostFuncType<T>)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		let f = sandbox_primitives::ExternEntity::Function(f as u32);
		self.add_entry(module, field, f);
	}

	pub fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
	where
		N1: Into<Vec<u8>>,
		N2: Into<Vec<u8>>,
	{
		let mem = sandbox_primitives::ExternEntity::Memory(mem.memory_idx as u32);
		self.add_entry(module, field, mem);
	}
}

pub struct Instance<T> {
	instance_idx: u32,
	_marker: marker::PhantomData<T>,
}

/// The primary responsibility of this thunk is to deserialize arguments and
/// call the original function, specified by the index.
extern "C" fn dispatch_thunk<T>(
	serialized_args_ptr: *const u8,
	serialized_args_len: usize,
	state: usize,
	f: ffi::HostFuncIndex,
) -> u64 {
	let serialized_args = unsafe {
		if serialized_args_len == 0 {
			&[]
		} else {
			slice::from_raw_parts(serialized_args_ptr, serialized_args_len)
		}
	};
	let args = Vec::<TypedValue>::decode(&mut &serialized_args[..]).expect(
		"serialized args should be provided by the runtime;
			correctly serialized data should be deserializable;
			qed",
	);

	unsafe {
		// This should be safe since `coerce_host_index_to_func` is called with an argument
		// received in an `dispatch_thunk` implementation, so `f` should point
		// on a valid host function.
		let f = ffi::coerce_host_index_to_func(f);

		// This should be safe since mutable reference to T is passed upon the invocation.
		let state = &mut *(state as *mut T);

		// Pass control flow to the designated function.
		let result = f(state, &args).encode();

		// Leak the result vector and return the pointer to return data.
		let result_ptr = result.as_ptr() as u64;
		let result_len = result.len() as u64;
		mem::forget(result);

		(result_ptr << 32) | result_len
	}
}

impl<T> Instance<T> {
	pub fn new(code: &[u8], env_def_builder: &EnvironmentDefinitionBuilder<T>, state: &mut T) -> Result<Instance<T>, Error> {
		let serialized_env_def: Vec<u8> = env_def_builder.env_def.encode();
		let result = unsafe {
			// It's very important to instantiate thunk with the right type.
			let dispatch_thunk = dispatch_thunk::<T>;

			ffi::ext_sandbox_instantiate(
				dispatch_thunk,
				code.as_ptr(),
				code.len(),
				serialized_env_def.as_ptr(),
				serialized_env_def.len(),
				state as *const T as usize,
			)
		};
		let instance_idx = match result {
			sandbox_primitives::ERR_MODULE => return Err(Error::Module),
			instance_idx => instance_idx,
		};
		Ok(Instance {
			instance_idx,
			_marker: marker::PhantomData::<T>,
		})
	}

	pub fn invoke(
		&mut self,
		name: &[u8],
		args: &[TypedValue],
		state: &mut T,
	) -> Result<ReturnValue, Error> {
		let serialized_args = args.to_vec().encode();

		let result = unsafe {
			ffi::ext_sandbox_invoke(
				self.instance_idx,
				name.as_ptr(),
				name.len(),
				serialized_args.as_ptr(),
				serialized_args.len(),
				state as *const T as usize,
			)
		};
		match result {
			sandbox_primitives::ERR_OK => {
				// TODO: Fetch the result of the execution.
				Ok(ReturnValue::Unit)
			}
			sandbox_primitives::ERR_EXECUTION => Err(Error::Execution),
			_ => unreachable!(),
		}
	}
}

impl<T> Drop for Instance<T> {
	fn drop(&mut self) {
		unsafe {
			ffi::ext_sandbox_instance_teardown(self.instance_idx);
		}
	}
}
