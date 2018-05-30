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

#![warn(missing_docs)]

//! This module implements sandboxing support in the runtime.

use std::collections::HashMap;
use std::rc::Rc;
use codec::Slicable;
use primitives::sandbox as sandbox_primitives;
use wasm_utils::DummyUserError;
use wasmi;
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
struct GuestToSupervisorFunctionMapping {
	funcs: Vec<SupervisorFuncIndex>,
}

impl GuestToSupervisorFunctionMapping {
	fn new() -> GuestToSupervisorFunctionMapping {
		GuestToSupervisorFunctionMapping { funcs: Vec::new() }
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
	/// Returns a reference to an associated sandbox `Store`.
	fn store(&self) -> &Store;

	/// Returns a mutable reference to an associated sandbox `Store`.
	fn store_mut(&mut self) -> &mut Store;

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
	sandbox_instance: &'a SandboxInstance,
	state: u32,
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
		// Make `index` typesafe again.
		let index = GuestFuncIndex(index);

		let dispatch_thunk = self.sandbox_instance.dispatch_thunk.clone();
		let func_idx = self.sandbox_instance
			.guest_to_supervisor_mapping
			.func_by_guest_index(index)
			.expect(
				"`invoke_index` is called with indexes registered via `FuncInstance::alloc_host`;
					`FuncInstance::alloc_host` is called with indexes that was obtained from `guest_to_supervisor_mapping`;
					`func_by_guest_index` called with `index` can't return `None`;
					qed"
			);

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

		// We do not have to check the signature here, because it's automatically
		// checked by wasmi.

		deserialize_result(&serialized_result_val)
	}
}

fn with_guest_externals<FE, R, F>(
	supervisor_externals: &mut FE,
	sandbox_instance: &SandboxInstance,
	state: u32,
	f: F,
) -> R
where
	FE: SandboxCapabilities + Externals,
	F: FnOnce(&mut GuestExternals<FE>) -> R,
{
	let mut guest_externals = GuestExternals {
		supervisor_externals,
		sandbox_instance,
		state,
	};
	f(&mut guest_externals)
}

/// Sandboxed instance of a wasm module.
///
/// It's primary purpose is to [`invoke`] exported functions on it.
///
/// All imports of this instance are specified at the creation time and
/// imports are implemented by the supervisor.
///
/// Hence, in order to invoke an exported function on a sandboxed module instance,
/// it's required to provide supervisor externals: it will be used to execute
/// code in the supervisor context.
///
/// [`invoke`]: #method.invoke
pub struct SandboxInstance {
	instance: ModuleRef,
	dispatch_thunk: FuncRef,
	guest_to_supervisor_mapping: GuestToSupervisorFunctionMapping,
}

impl SandboxInstance {
	/// Invoke an exported function by a name.
	///
	/// `supervisor_externals` is required to execute the implementations
	/// of the syscalls that published to a sandboxed module instance.
	///
	/// The `state` parameter can be used to provide custom data for
	/// these syscall implementations.
	pub fn invoke<FE: SandboxCapabilities + Externals>(
		&self,
		export_name: &str,
		args: &[RuntimeValue],
		supervisor_externals: &mut FE,
		state: u32,
	) -> Result<Option<wasmi::RuntimeValue>, wasmi::Error> {
		with_guest_externals(
			supervisor_externals,
			self,
			state,
			|guest_externals| {
				self.instance
					.invoke_export(export_name, args, guest_externals)
			},
		)
	}
}

fn decode_environment_definition(
	raw_env_def: &[u8],
	memories: &[Option<MemoryRef>],
) -> Result<(Imports, GuestToSupervisorFunctionMapping), DummyUserError> {
	let env_def = sandbox_primitives::EnvironmentDefinition::decode(&mut &raw_env_def[..]).ok_or_else(|| DummyUserError)?;

	let mut func_map = HashMap::new();
	let mut memories_map = HashMap::new();
	let mut guest_to_supervisor_mapping = GuestToSupervisorFunctionMapping::new();

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
					.cloned()
					.ok_or_else(|| DummyUserError)?
					.ok_or_else(|| DummyUserError)?;
				memories_map.insert((module, field), memory_ref);
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
pub fn instantiate<FE: SandboxCapabilities + Externals>(
	supervisor_externals: &mut FE,
	dispatch_thunk: FuncRef,
	wasm: &[u8],
	raw_env_def: &[u8],
	state: u32,
) -> Result<u32, DummyUserError> {
	let (imports, guest_to_supervisor_mapping) =
		decode_environment_definition(raw_env_def, &supervisor_externals.store().memories)?;

	let module = Module::from_buffer(wasm).map_err(|_| DummyUserError)?;
	let instance = ModuleInstance::new(&module, &imports).map_err(|_| DummyUserError)?;

	let sandbox_instance = Rc::new(SandboxInstance {
		// In general, it's not a very good idea to use `.not_started_instance()` for anything
		// but for extracting memory and tables. But in this particular case, we are extracting
		// for the purpose of running `start` function which should be ok.
		instance: instance.not_started_instance().clone(),
		dispatch_thunk,
		guest_to_supervisor_mapping,
	});

	with_guest_externals(
		supervisor_externals,
		&sandbox_instance,
		state,
		|guest_externals| {
			instance
				.run_start(guest_externals)
				.map_err(|_| DummyUserError)
		},
	)?;

	let instance_idx = supervisor_externals
		.store_mut()
		.register_sandbox_instance(sandbox_instance);

	Ok(instance_idx)
}

/// This struct keeps track of all sandboxed components.
pub struct Store {
	// Memories and instances are `Some` untill torndown.
	instances: Vec<Option<Rc<SandboxInstance>>>,
	memories: Vec<Option<MemoryRef>>,
}

impl Store {
	/// Create a new empty sandbox store.
	pub fn new() -> Store {
		Store {
			instances: Vec::new(),
			memories: Vec::new(),
		}
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

		let mem =
			MemoryInstance::alloc(Pages(initial as usize), maximum).map_err(|_| DummyUserError)?;
		let mem_idx = self.memories.len();
		self.memories.push(Some(mem));
		Ok(mem_idx as u32)
	}

	/// Returns `SandboxInstance` by `instance_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `instance_idx` isn't a valid index of an instance or
	/// instance is already torndown.
	pub fn instance(&self, instance_idx: u32) -> Result<Rc<SandboxInstance>, DummyUserError> {
		self.instances
			.get(instance_idx as usize)
			.cloned()
			.ok_or_else(|| DummyUserError)?
			.ok_or_else(|| DummyUserError)
	}

	/// Returns reference to a memory instance by `memory_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `memory_idx` isn't a valid index of an memory or
	/// memory is already torndown.
	pub fn memory(&self, memory_idx: u32) -> Result<MemoryRef, DummyUserError> {
		self.memories
			.get(memory_idx as usize)
			.cloned()
			.ok_or_else(|| DummyUserError)?
			.ok_or_else(|| DummyUserError)
	}

	/// Teardown the memory at the specified index.
	///
	/// # Errors
	///
	/// Returns `Err` if `memory_idx` isn't a valid index of an memory.
	pub fn memory_teardown(&mut self, memory_idx: u32) -> Result<(), DummyUserError> {
		if memory_idx as usize >= self.memories.len() {
			return Err(DummyUserError);
		}
		self.memories[memory_idx as usize] = None;
		Ok(())
	}

	/// Teardown the instance at the specified index.
	pub fn instance_teardown(&mut self, instance_idx: u32) -> Result<(), DummyUserError> {
		if instance_idx as usize >= self.instances.len() {
			return Err(DummyUserError);
		}
		self.instances[instance_idx as usize] = None;
		Ok(())
	}

	fn register_sandbox_instance(&mut self, sandbox_instance: Rc<SandboxInstance>) -> u32 {
		let instance_idx = self.instances.len();
		self.instances.push(Some(sandbox_instance));
		instance_idx as u32
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

	#[test]
	fn start_called() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))
			(import "env" "inc_counter" (func $inc_counter (param i32) (result i32)))

			;; Start function
			(start $start)
			(func $start
				;; Increment counter by 1
				(drop
					(call $inc_counter (i32.const 1))
				)
			)

			(func (export "call")
				;; Increment counter by 1. The current value is placed on the stack.
				(call $inc_counter (i32.const 1))

				;; Counter is incremented twice by 1, once there and once in `start` func.
				;; So check the returned value is equal to 2.
				i32.const 2
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
}
