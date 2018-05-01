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

//! This module implements sandboxing support in the runtime.

use codec::Slicable;
use primitives::sandbox as sandbox_primitives;
use std::collections::HashMap;
use wasm_utils::DummyUserError;
use wasmi::memory_units::Pages;
use wasmi::{Externals, FuncRef, ImportResolver, MemoryInstance, MemoryRef, Module, ModuleInstance,
            ModuleRef, RuntimeArgs, RuntimeValue, Trap, TrapKind};

/// Index of a function inside the supervisor.
///
/// This is a typically an index in the default table of the supervisor, however
/// the exact meaning of this index is depends on the implementation of dispatch function.
#[derive(Copy, Clone, Debug, PartialEq)]
struct SupervisorFuncIndex(usize);

/// Index of a function within guest index space.
///
/// This index is supposed to be used with as index for `Externals`.
#[derive(Copy, Clone, Debug, PartialEq)]
struct GuestFuncIndex(usize);

/// This struct holds a mapping from guest index space to supervisor.
struct GuestToSuperviserFunctionMapping {
	funcs: Vec<SupervisorFuncIndex>,
}

impl GuestToSuperviserFunctionMapping {
	fn new() -> GuestToSuperviserFunctionMapping {
		GuestToSuperviserFunctionMapping { funcs: Vec::new() }
	}

	fn define(&mut self, supervisor_func: SupervisorFuncIndex) -> GuestFuncIndex {
		let idx = self.funcs.len();
		self.funcs.push(supervisor_func);
		GuestFuncIndex(idx)
	}

	fn func_by_guest_index(&self, guest_func_idx: GuestFuncIndex) -> Option<SupervisorFuncIndex> {
		self.funcs.get(guest_func_idx.0).cloned()
	}
}

struct Imports {
	func_map: HashMap<(Vec<u8>, Vec<u8>), GuestFuncIndex>,
	memories_map: HashMap<(Vec<u8>, Vec<u8>), MemoryRef>,
}

impl ImportResolver for Imports {
	fn resolve_func(
		&self,
		module_name: &str,
		field_name: &str,
		signature: &::wasmi::Signature,
	) -> Result<FuncRef, ::wasmi::Error> {
		let key = (
			module_name.as_bytes().to_owned(),
			field_name.as_bytes().to_owned(),
		);
		let idx = *self.func_map.get(&key).ok_or_else(|| {
			::wasmi::Error::Instantiation(format!(
				"Export {}:{} not found",
				module_name, field_name
			))
		})?;
		Ok(::wasmi::FuncInstance::alloc_host(signature.clone(), idx.0))
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &::wasmi::MemoryDescriptor,
	) -> Result<MemoryRef, ::wasmi::Error> {
		let key = (
			module_name.as_bytes().to_vec(),
			field_name.as_bytes().to_vec(),
		);
		let mem = self.memories_map
			.get(&key)
			.ok_or_else(|| {
				::wasmi::Error::Instantiation(format!(
					"Export {}:{} not found",
					module_name, field_name
				))
			})?
			.clone();
		Ok(mem)
	}

	fn resolve_global(
		&self,
		_module_name: &str,
		_field_name: &str,
		_global_type: &::wasmi::GlobalDescriptor,
	) -> Result<::wasmi::GlobalRef, ::wasmi::Error> {
		// TODO:
		unimplemented!()
	}

	fn resolve_table(
		&self,
		_module_name: &str,
		_field_name: &str,
		_table_type: &::wasmi::TableDescriptor,
	) -> Result<::wasmi::TableRef, ::wasmi::Error> {
		// TODO:
		unimplemented!()
	}
}

/// This trait encapsulates sandboxing capabilities.
///
/// Note that this functions are only called in the `supervisor` context.
pub trait SandboxCapabilities {
	/// Returns associated sandbox `Store`.
	fn store(&self) -> &Store;

	/// Allocate space of the specified length in the supervisor memory.
	///
	/// Returns pointer to the allocated block.
	fn allocate(&mut self, len: u32) -> u32;

	/// Deallocate space specified by the pointer that was previously returned by [`allocate`].
	///
	/// [`allocate`]: #tymethod.allocate
	fn deallocate(&mut self, ptr: u32);

	/// Write `data` into the supervisor memory at offset specified by `ptr`.
	///
	/// # Errors
	///
	/// Returns `Err` if `ptr + data.len()` is out of bounds.
	fn write_memory(&mut self, ptr: u32, data: &[u8]) -> Result<(), DummyUserError>;

	/// Read `len` bytes from the supervisor memory.
	///
	/// # Errors
	///
	/// Returns `Err` if `ptr + len` is out of bounds.
	fn read_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>, DummyUserError>;
}

/// Implementation of [`Externals`] that allows execution of guest module with
/// [externals][`Externals`] that might refer functions defined by supervisor.
///
/// [`Externals`]: ../../wasmi/trait.Externals.html
pub struct GuestExternals<'a, FE: SandboxCapabilities + Externals + 'a> {
	supervisor_externals: &'a mut FE,
	instance_idx: u32,
	state: u32,
}

impl<'a, FE: SandboxCapabilities + Externals + 'a> GuestExternals<'a, FE> {
	/// Create a new instance of `GuestExternals`.
	///
	/// It will use `supervisor_externals` to execute calls from guest to supervisor.
	/// `instance_idx` required to fetch settings for this particular instance, e.g
	/// associated dispatch thunk funtion and mapping between externals function ids to
	/// functions in supervisor module.
	/// `state` is just an integer that allows supervisor to have arbitrary state associated with the call,
	/// typically used for implementing runtime functions.
	pub fn new(supervisor_externals: &mut FE, instance_idx: u32, state: u32) -> GuestExternals<FE> {
		GuestExternals {
			supervisor_externals,
			instance_idx,
			state,
		}
	}
}

fn trap() -> Trap {
	TrapKind::Host(Box::new(DummyUserError)).into()
}

fn deserialize_result(serialized_result: &[u8]) -> Result<Option<RuntimeValue>, Trap> {
	use self::sandbox_primitives::{HostError, ReturnValue};
	let result_val = Result::<ReturnValue, HostError>::decode(&mut &serialized_result[..])
		.ok_or_else(|| trap())?;

	match result_val {
		Ok(return_value) => Ok(match return_value {
			ReturnValue::Unit => None,
			ReturnValue::Value(typed_value) => Some(RuntimeValue::from(typed_value)),
		}),
		Err(HostError) => Err(trap()),
	}
}

impl<'a, FE: SandboxCapabilities + Externals + 'a> Externals for GuestExternals<'a, FE> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> Result<Option<RuntimeValue>, Trap> {
		let (func_idx, dispatch_thunk) = {
			let instance = &self.supervisor_externals.store().instances[self.instance_idx as usize];
			let dispatch_thunk = instance.dispatch_thunk.clone();
			let func_idx = instance
				.guest_to_supervisor_mapping
				.func_by_guest_index(
					GuestFuncIndex(index)
				)
				.expect(
					"`invoke_index` is called with indexes registered via `FuncInstance::alloc_host`;
						`FuncInstance::alloc_host` is called with indexes that was obtained from `guest_to_supervisor_mapping`;
						`func_by_guest_index` called with `index` can't return `None`;
						qed"
				);
			(func_idx, dispatch_thunk)
		};

		// Serialize arguments into a byte vector.
		let invoke_args_data: Vec<u8> = args.as_ref()
			.iter()
			.cloned()
			.map(sandbox_primitives::TypedValue::from)
			.collect::<Vec<_>>()
			.encode();

		let state = self.state;

		// Move serialized arguments inside the memory and invoke dispatch thunk and
		// then free allocated memory.
		let invoke_args_ptr = self.supervisor_externals
			.allocate(invoke_args_data.len() as u32);
		self.supervisor_externals
			.write_memory(invoke_args_ptr, &invoke_args_data)?;
		let result = ::wasmi::FuncInstance::invoke(
			&dispatch_thunk,
			&[
				RuntimeValue::I32(invoke_args_ptr as i32),
				RuntimeValue::I32(invoke_args_data.len() as i32),
				RuntimeValue::I32(state as i32),
				RuntimeValue::I32(func_idx.0 as i32),
			],
			self.supervisor_externals,
		);
		self.supervisor_externals.deallocate(invoke_args_ptr);

		// dispatch_thunk returns pointer to serialized arguments.
		let (serialized_result_val_ptr, serialized_result_val_len) = match result {
			// Unpack pointer and len of the serialized result data.
			Ok(Some(RuntimeValue::I64(v))) => {
				// Cast to u64 to use zero-extension.
				let v = v as u64;
				let ptr = (v as u64 >> 32) as u32;
				let len = (v & 0xFFFFFFFF) as u32;
				(ptr, len)
			}
			_ => return Err(trap()),
		};

		let serialized_result_val = self.supervisor_externals
			.read_memory(serialized_result_val_ptr, serialized_result_val_len)?;
		self.supervisor_externals
			.deallocate(serialized_result_val_ptr);

		// TODO: check the signature?

		deserialize_result(&serialized_result_val)
	}
}

struct SandboxInstance {
	instance: ModuleRef,
	dispatch_thunk: FuncRef,
	guest_to_supervisor_mapping: GuestToSuperviserFunctionMapping,
}

fn decode_environment_definition(
	raw_env_def: &[u8],
	memories: &[MemoryRef],
) -> Result<(Imports, GuestToSuperviserFunctionMapping), DummyUserError> {
	let env_def = sandbox_primitives::EnvironmentDefinition::decode(&mut &raw_env_def[..]).ok_or_else(|| DummyUserError)?;

	let mut func_map = HashMap::new();
	let mut memories_map = HashMap::new();
	let mut guest_to_supervisor_mapping = GuestToSuperviserFunctionMapping::new();

	for entry in &env_def.entries {
		let module = entry.module_name.clone();
		let field = entry.field_name.clone();

		match entry.entity {
			sandbox_primitives::ExternEntity::Function(func_idx) => {
				let externals_idx =
					guest_to_supervisor_mapping.define(SupervisorFuncIndex(func_idx as usize));
				func_map.insert((module, field), externals_idx);
			}
			sandbox_primitives::ExternEntity::Memory(memory_idx) => {
				let memory_ref = memories
					.get(memory_idx as usize)
					.ok_or_else(|| DummyUserError)?;
				memories_map.insert((module, field), memory_ref.clone());
			}
		}
	}

	Ok((
		Imports {
			func_map,
			memories_map,
		},
		guest_to_supervisor_mapping,
	))
}

/// This struct keeps track of all sandboxed components.
pub struct Store {
	instances: Vec<SandboxInstance>,
	memories: Vec<MemoryRef>,
}

impl Store {
	/// Create new empty sandbox store.
	pub fn new() -> Store {
		Store {
			instances: Vec::new(),
			memories: Vec::new(),
		}
	}

	/// Instantiate a guest module and return it's index in the store.
	///
	/// The guest module's code is specified in `wasm`. Environment that will be available to
	/// guest module is specified in `raw_env_def` (serialized version of [`EnvironmentDefinition`]).
	/// `dispatch_thunk` is used as function that handle calls from guests.
	///
	/// # Errors
	///
	/// Returns `Err` if any of the following conditions happens:
	///
	/// - `raw_env_def` can't be deserialized as a [`EnvironmentDefinition`].
	/// - Module in `wasm` is invalid or couldn't be instantiated.
	///
	/// [`EnvironmentDefinition`]: ../../sandbox/struct.EnvironmentDefinition.html
	pub fn instantiate(
		&mut self,
		dispatch_thunk: FuncRef,
		wasm: &[u8],
		raw_env_def: &[u8],
		_state: u32,
	) -> Result<u32, DummyUserError> {
		let (imports, guest_to_supervisor_mapping) =
			decode_environment_definition(raw_env_def, &self.memories)?;

		// TODO: Run `start`.
		let module = Module::from_buffer(wasm).map_err(|_| DummyUserError)?;
		let instance = ModuleInstance::new(&module, &imports)
			.map_err(|_| DummyUserError)?
			.assert_no_start();

		let instance_idx = self.instances.len();

		self.instances.push(SandboxInstance {
			instance,
			dispatch_thunk,
			guest_to_supervisor_mapping,
		});

		Ok(instance_idx as u32)
	}

	/// Create a new memory instance and return it's index.
	///
	/// # Errors
	///
	/// Returns `Err` if the memory couldn't be created.
	/// Typically happens if `initial` is more than `maximum`.
	pub fn new_memory(&mut self, initial: u32, maximum: u32) -> Result<u32, DummyUserError> {
		let maximum = match maximum {
			sandbox_primitives::MEM_UNLIMITED => None,
			specified_limit => Some(Pages(specified_limit as usize)),
		};

		let mem = MemoryInstance::alloc(Pages(initial as usize), maximum).map_err(|_| DummyUserError)?;
		self.memories.push(mem);
		let mem_idx = self.memories.len() - 1;
		Ok(mem_idx as u32)
	}

	/// Returns `ModuleRef` by `instance_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `instance_idx` isn't a valid index of an instance.
	pub fn instance(&self, instance_idx: u32) -> Result<ModuleRef, DummyUserError> {
		self.instances
			.get(instance_idx as usize)
			.map(|i| i.instance.clone())
			.ok_or_else(|| DummyUserError)
	}

	/// Returns reference to a memory instance by `memory_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `memory_idx` isn't a valid index of an instance.
	pub fn memory(&self, memory_idx: u32) -> Result<MemoryRef, DummyUserError> {
		self.memories
			.get(memory_idx as usize)
			.cloned()
			.ok_or_else(|| DummyUserError)
	}
}

#[cfg(test)]
mod tests {
	use wasm_executor::WasmExecutor;
	use state_machine::{TestExternalities, CodeExecutor};
	use wabt;

	#[test]
	fn sandbox_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))
			(import "env" "inc_counter" (func $inc_counter (param i32) (result i32)))
			(func (export "call")
				(drop
					(call $inc_counter (i32.const 5))
				)

				(call $inc_counter (i32.const 3))
				;; current counter value is on the stack

				;; check whether current == 8
				i32.const 8
				i32.eq

				call $assert
			)
		)
		"#).unwrap();

		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_sandbox", &code).unwrap(),
			vec![1],
		);
	}

	#[test]
	fn sandbox_trap() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))
			(func (export "call")
				i32.const 0
				call $assert
			)
		)
		"#).unwrap();

		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_sandbox", &code).unwrap(),
			vec![0],
		);
	}
}
