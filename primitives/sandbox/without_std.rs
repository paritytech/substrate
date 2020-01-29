// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};
use sp_core::sandbox as sandbox_primitives;
use sp_io::sandbox;
use sp_std::{prelude::*, slice, marker, mem, vec, rc::Rc};
use super::{Error, Value, ReturnValue, HostFuncType};

mod ffi {
	use sp_std::mem;
	use super::HostFuncType;

	/// Index into the default table that points to a `HostFuncType`.
	pub type HostFuncIndex = usize;

	/// Coerce `HostFuncIndex` to a callable host function pointer.
	///
	/// # Safety
	///
	/// This function should be only called with a `HostFuncIndex` that was previously registered
	/// in the environment definition. Typically this should only
	/// be called with an argument received in `dispatch_thunk`.
	pub unsafe fn coerce_host_index_to_func<T>(idx: HostFuncIndex) -> HostFuncType<T> {
		// We need to ensure that sizes of a callable function pointer and host function index is
		// indeed equal.
		// We can't use `static_assertions` create because it makes compiler panic, fallback to runtime assert.
		// const_assert!(mem::size_of::<HostFuncIndex>() == mem::size_of::<HostFuncType<T>>(),);
		assert!(mem::size_of::<HostFuncIndex>() == mem::size_of::<HostFuncType<T>>());
		mem::transmute::<HostFuncIndex, HostFuncType<T>>(idx)
	}
}

struct MemoryHandle {
	memory_idx: u32,
}

impl Drop for MemoryHandle {
	fn drop(&mut self) {
		sandbox::memory_teardown(self.memory_idx);
	}
}

#[derive(Clone)]
pub struct Memory {
	// Handle to memory instance is wrapped to add reference-counting semantics
	// to `Memory`.
	handle: Rc<MemoryHandle>,
}

impl Memory {
	pub fn new(initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
		let maximum = if let Some(maximum) = maximum {
			maximum
		} else {
			sandbox_primitives::MEM_UNLIMITED
		};

		match sandbox::memory_new(initial, maximum) {
			sandbox_primitives::ERR_MODULE => Err(Error::Module),
			memory_idx => Ok(Memory {
				handle: Rc::new(MemoryHandle { memory_idx, }),
			}),
		}
	}

	pub fn get(&self, offset: u32, buf: &mut [u8]) -> Result<(), Error> {
		let result = sandbox::memory_get(
			self.handle.memory_idx,
			offset,
			buf.as_mut_ptr(),
			buf.len() as u32,
		);
		match result {
			sandbox_primitives::ERR_OK => Ok(()),
			sandbox_primitives::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
			_ => unreachable!(),
		}
	}

	pub fn set(&self, offset: u32, val: &[u8]) -> Result<(), Error> {
		let result = sandbox::memory_set(
			self.handle.memory_idx,
			offset,
			val.as_ptr() as _ ,
			val.len() as u32,
		);
		match result {
			sandbox_primitives::ERR_OK => Ok(()),
			sandbox_primitives::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
			_ => unreachable!(),
		}
	}
}

pub struct EnvironmentDefinitionBuilder<T> {
	env_def: sandbox_primitives::EnvironmentDefinition,
	retained_memories: Vec<Memory>,
	_marker: marker::PhantomData<T>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
	pub fn new() -> EnvironmentDefinitionBuilder<T> {
		EnvironmentDefinitionBuilder {
			env_def: sandbox_primitives::EnvironmentDefinition {
				entries: Vec::new(),
			},
			retained_memories: Vec::new(),
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
		// We need to retain memory to keep it alive while the EnvironmentDefinitionBuilder alive.
		self.retained_memories.push(mem.clone());

		let mem = sandbox_primitives::ExternEntity::Memory(mem.handle.memory_idx as u32);
		self.add_entry(module, field, mem);
	}
}

pub struct Instance<T> {
	instance_idx: u32,
	_retained_memories: Vec<Memory>,
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
	let args = Vec::<Value>::decode(&mut &serialized_args[..]).expect(
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
	pub fn new(
		code: &[u8],
		env_def_builder: &EnvironmentDefinitionBuilder<T>,
		state: &mut T,
	) -> Result<Instance<T>, Error> {
		let serialized_env_def: Vec<u8> = env_def_builder.env_def.encode();
		// It's very important to instantiate thunk with the right type.
		let dispatch_thunk = dispatch_thunk::<T>;
		let result = sandbox::instantiate(
			dispatch_thunk as u32,
			code,
			&serialized_env_def,
			state as *const T as _,
		);

		let instance_idx = match result {
			sandbox_primitives::ERR_MODULE => return Err(Error::Module),
			sandbox_primitives::ERR_EXECUTION => return Err(Error::Execution),
			instance_idx => instance_idx,
		};

		// We need to retain memories to keep them alive while the Instance is alive.
		let retained_memories = env_def_builder.retained_memories.clone();
		Ok(Instance {
			instance_idx,
			_retained_memories: retained_memories,
			_marker: marker::PhantomData::<T>,
		})
	}

	pub fn invoke(
		&mut self,
		name: &str,
		args: &[Value],
		state: &mut T,
	) -> Result<ReturnValue, Error> {
		let serialized_args = args.to_vec().encode();
		let mut return_val = vec![0u8; ReturnValue::ENCODED_MAX_SIZE];

		let result = sandbox::invoke(
			self.instance_idx,
			name,
			&serialized_args,
			return_val.as_mut_ptr() as _,
			return_val.len() as u32,
			state as *const T as _,
		);

		match result {
			sandbox_primitives::ERR_OK => {
				let return_val = ReturnValue::decode(&mut &return_val[..])
					.map_err(|_| Error::Execution)?;
				Ok(return_val)
			}
			sandbox_primitives::ERR_EXECUTION => Err(Error::Execution),
			_ => unreachable!(),
		}
	}

	pub fn get_global_val(&self, name: &str) -> Option<Value> {
		sandbox::get_global_val(self.instance_idx, name)
	}
}

impl<T> Drop for Instance<T> {
	fn drop(&mut self) {
		sandbox::instance_teardown(self.instance_idx);
	}
}
