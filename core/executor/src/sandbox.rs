// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use crate::error::{Result, Error};
use std::{collections::HashMap, rc::Rc};
use codec::{Decode, Encode};
use primitives::sandbox as sandbox_primitives;
use wasmi::{
	Externals, ImportResolver, MemoryInstance, MemoryRef, Module, ModuleInstance,
	ModuleRef, RuntimeArgs, RuntimeValue, Trap, TrapKind, memory_units::Pages,
};
use wasm_interface::{Pointer, WordSize};

/// Index of a function inside the supervisor.
///
/// This is a typically an index in the default table of the supervisor, however
/// the exact meaning of this index is depends on the implementation of dispatch function.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct SupervisorFuncIndex(usize);

impl From<SupervisorFuncIndex> for usize {
	fn from(index: SupervisorFuncIndex) -> Self {
		index.0
	}
}

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
	) -> std::result::Result<wasmi::FuncRef, wasmi::Error> {
		let key = (
			module_name.as_bytes().to_owned(),
			field_name.as_bytes().to_owned(),
		);
		let idx = *self.func_map.get(&key).ok_or_else(|| {
			wasmi::Error::Instantiation(format!(
				"Export {}:{} not found",
				module_name, field_name
			))
		})?;
		Ok(wasmi::FuncInstance::alloc_host(signature.clone(), idx.0))
	}

	fn resolve_memory(
		&self,
		module_name: &str,
		field_name: &str,
		_memory_type: &::wasmi::MemoryDescriptor,
	) -> std::result::Result<MemoryRef, wasmi::Error> {
		let key = (
			module_name.as_bytes().to_vec(),
			field_name.as_bytes().to_vec(),
		);
		let mem = self.memories_map
			.get(&key)
			.ok_or_else(|| {
				wasmi::Error::Instantiation(format!(
					"Export {}:{} not found",
					module_name, field_name
				))
			})?
			.clone();
		Ok(mem)
	}

	fn resolve_global(
		&self,
		module_name: &str,
		field_name: &str,
		_global_type: &::wasmi::GlobalDescriptor,
	) -> std::result::Result<wasmi::GlobalRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!(
			"Export {}:{} not found",
			module_name, field_name
		)))
	}

	fn resolve_table(
		&self,
		module_name: &str,
		field_name: &str,
		_table_type: &::wasmi::TableDescriptor,
	) -> std::result::Result<wasmi::TableRef, wasmi::Error> {
		Err(wasmi::Error::Instantiation(format!(
			"Export {}:{} not found",
			module_name, field_name
		)))
	}
}

/// This trait encapsulates sandboxing capabilities.
///
/// Note that this functions are only called in the `supervisor` context.
pub trait SandboxCapabilities {
	/// Represents a function reference into the supervisor environment.
	type SupervisorFuncRef;

	/// Returns a reference to an associated sandbox `Store`.
	fn store(&self) -> &Store<Self::SupervisorFuncRef>;

	/// Returns a mutable reference to an associated sandbox `Store`.
	fn store_mut(&mut self) -> &mut Store<Self::SupervisorFuncRef>;

	/// Allocate space of the specified length in the supervisor memory.
	///
	/// # Errors
	///
	/// Returns `Err` if allocation not possible or errors during heap management.
	///
	/// Returns pointer to the allocated block.
	fn allocate(&mut self, len: WordSize) -> Result<Pointer<u8>>;

	/// Deallocate space specified by the pointer that was previously returned by [`allocate`].
	///
	/// # Errors
	///
	/// Returns `Err` if deallocation not possible or because of errors in heap management.
	///
	/// [`allocate`]: #tymethod.allocate
	fn deallocate(&mut self, ptr: Pointer<u8>) -> Result<()>;

	/// Write `data` into the supervisor memory at offset specified by `ptr`.
	///
	/// # Errors
	///
	/// Returns `Err` if `ptr + data.len()` is out of bounds.
	fn write_memory(&mut self, ptr: Pointer<u8>, data: &[u8]) -> Result<()>;

	/// Read `len` bytes from the supervisor memory.
	///
	/// # Errors
	///
	/// Returns `Err` if `ptr + len` is out of bounds.
	fn read_memory(&self, ptr: Pointer<u8>, len: WordSize) -> Result<Vec<u8>>;

	/// Invoke a function in the supervisor environment.
	///
	/// This first invokes the dispatch_thunk function, passing in the function index of the
	/// desired function to call and serialized arguments. The thunk calls the desired function
	/// with the deserialized arguments, then serializes the result into memory and returns
	/// reference. The pointer to and length of the result in linear memory is encoded into an i64,
	/// with the upper 32 bits representing the pointer and the lower 32 bits representing the
	/// length.
	///
	/// # Errors
	///
	/// Returns `Err` if the dispatch_thunk function has an incorrect signature or traps during
	/// execution.
	fn invoke(
		&mut self,
		dispatch_thunk: &Self::SupervisorFuncRef,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		state: u32,
		func_idx: SupervisorFuncIndex,
	) -> Result<i64>;
}

/// Implementation of [`Externals`] that allows execution of guest module with
/// [externals][`Externals`] that might refer functions defined by supervisor.
///
/// [`Externals`]: ../../wasmi/trait.Externals.html
pub struct GuestExternals<'a, FE: SandboxCapabilities + 'a> {
	supervisor_externals: &'a mut FE,
	sandbox_instance: &'a SandboxInstance<FE::SupervisorFuncRef>,
	state: u32,
}

fn trap(msg: &'static str) -> Trap {
	TrapKind::Host(Box::new(Error::Other(msg.into()))).into()
}

fn deserialize_result(serialized_result: &[u8]) -> std::result::Result<Option<RuntimeValue>, Trap> {
	use self::sandbox_primitives::{HostError, ReturnValue};
	let result_val = std::result::Result::<ReturnValue, HostError>::decode(&mut &serialized_result[..])
		.map_err(|_| trap("Decoding Result<ReturnValue, HostError> failed!"))?;

	match result_val {
		Ok(return_value) => Ok(match return_value {
			ReturnValue::Unit => None,
			ReturnValue::Value(typed_value) => Some(RuntimeValue::from(typed_value)),
		}),
		Err(HostError) => Err(trap("Supervisor function returned sandbox::HostError")),
	}
}

impl<'a, FE: SandboxCapabilities + 'a> Externals for GuestExternals<'a, FE> {
	fn invoke_index(
		&mut self,
		index: usize,
		args: RuntimeArgs,
	) -> std::result::Result<Option<RuntimeValue>, Trap> {
		// Make `index` typesafe again.
		let index = GuestFuncIndex(index);

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
		let invoke_args_len = invoke_args_data.len() as WordSize;
		let invoke_args_ptr = self.supervisor_externals.allocate(invoke_args_len)?;
		self.supervisor_externals.write_memory(invoke_args_ptr, &invoke_args_data)?;
		let result = self.supervisor_externals.invoke(
			&self.sandbox_instance.dispatch_thunk,
			invoke_args_ptr,
			invoke_args_len,
			state,
			func_idx,
		)?;
		self.supervisor_externals.deallocate(invoke_args_ptr)?;

		// dispatch_thunk returns pointer to serialized arguments.
		// Unpack pointer and len of the serialized result data.
		let (serialized_result_val_ptr, serialized_result_val_len) = {
			// Cast to u64 to use zero-extension.
			let v = result as u64;
			let ptr = (v as u64 >> 32) as u32;
			let len = (v & 0xFFFFFFFF) as u32;
			(Pointer::new(ptr), len)
		};

		let serialized_result_val = self.supervisor_externals
			.read_memory(serialized_result_val_ptr, serialized_result_val_len)?;
		self.supervisor_externals
			.deallocate(serialized_result_val_ptr)?;

		deserialize_result(&serialized_result_val)
	}
}

fn with_guest_externals<FE, R, F>(
	supervisor_externals: &mut FE,
	sandbox_instance: &SandboxInstance<FE::SupervisorFuncRef>,
	state: u32,
	f: F,
) -> R
where
	FE: SandboxCapabilities,
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
/// This is generic over a supervisor function reference type.
///
/// [`invoke`]: #method.invoke
pub struct SandboxInstance<FR> {
	instance: ModuleRef,
	dispatch_thunk: FR,
	guest_to_supervisor_mapping: GuestToSupervisorFunctionMapping,
}

impl<FR> SandboxInstance<FR> {
	/// Invoke an exported function by a name.
	///
	/// `supervisor_externals` is required to execute the implementations
	/// of the syscalls that published to a sandboxed module instance.
	///
	/// The `state` parameter can be used to provide custom data for
	/// these syscall implementations.
	pub fn invoke<FE: SandboxCapabilities<SupervisorFuncRef=FR>>(
		&self,
		export_name: &str,
		args: &[RuntimeValue],
		supervisor_externals: &mut FE,
		state: u32,
	) -> std::result::Result<Option<wasmi::RuntimeValue>, wasmi::Error> {
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

/// Error occurred during instantiation of a sandboxed module.
pub enum InstantiationError {
	/// Something wrong with the environment definition. It either can't
	/// be decoded, have a reference to a non-existent or torn down memory instance.
	EnvironmentDefinitionCorrupted,
	/// Provided module isn't recognized as a valid webassembly binary.
	ModuleDecoding,
	/// Module is a well-formed webassembly binary but could not be instantiated. This could
	/// happen because, e.g. the module imports entries not provided by the environment.
	Instantiation,
	/// Module is well-formed, instantiated and linked, but while executing the start function
	/// a trap was generated.
	StartTrapped,
}

fn decode_environment_definition(
	raw_env_def: &[u8],
	memories: &[Option<MemoryRef>],
) -> std::result::Result<(Imports, GuestToSupervisorFunctionMapping), InstantiationError> {
	let env_def = sandbox_primitives::EnvironmentDefinition::decode(&mut &raw_env_def[..])
		.map_err(|_| InstantiationError::EnvironmentDefinitionCorrupted)?;

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
					.ok_or_else(|| InstantiationError::EnvironmentDefinitionCorrupted)?
					.ok_or_else(|| InstantiationError::EnvironmentDefinitionCorrupted)?;
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
pub fn instantiate<FE: SandboxCapabilities>(
	supervisor_externals: &mut FE,
	dispatch_thunk: FE::SupervisorFuncRef,
	wasm: &[u8],
	raw_env_def: &[u8],
	state: u32,
) -> std::result::Result<u32, InstantiationError> {
	let (imports, guest_to_supervisor_mapping) =
		decode_environment_definition(raw_env_def, &supervisor_externals.store().memories)?;

	let module = Module::from_buffer(wasm).map_err(|_| InstantiationError::ModuleDecoding)?;
	let instance = ModuleInstance::new(&module, &imports).map_err(|_| InstantiationError::Instantiation)?;

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
				.map_err(|_| InstantiationError::StartTrapped)
		},
	)?;

	// At last, register the instance.
	let instance_idx = supervisor_externals
		.store_mut()
		.register_sandbox_instance(sandbox_instance);
	Ok(instance_idx)
}

/// This struct keeps track of all sandboxed components.
///
/// This is generic over a supervisor function reference type.
pub struct Store<FR> {
	// Memories and instances are `Some` untill torndown.
	instances: Vec<Option<Rc<SandboxInstance<FR>>>>,
	memories: Vec<Option<MemoryRef>>,
}

impl<FR> Store<FR> {
	/// Create a new empty sandbox store.
	pub fn new() -> Self {
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
	pub fn new_memory(&mut self, initial: u32, maximum: u32) -> Result<u32> {
		let maximum = match maximum {
			sandbox_primitives::MEM_UNLIMITED => None,
			specified_limit => Some(Pages(specified_limit as usize)),
		};

		let mem =
			MemoryInstance::alloc(
				Pages(initial as usize),
				maximum,
			)?;

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
	pub fn instance(&self, instance_idx: u32) -> Result<Rc<SandboxInstance<FR>>> {
		self.instances
			.get(instance_idx as usize)
			.cloned()
			.ok_or_else(|| "Trying to access a non-existent instance")?
			.ok_or_else(|| "Trying to access a torndown instance".into())
	}

	/// Returns reference to a memory instance by `memory_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `memory_idx` isn't a valid index of an memory or
	/// if memory has been torn down.
	pub fn memory(&self, memory_idx: u32) -> Result<MemoryRef> {
		self.memories
			.get(memory_idx as usize)
			.cloned()
			.ok_or_else(|| "Trying to access a non-existent sandboxed memory")?
			.ok_or_else(|| "Trying to access a torndown sandboxed memory".into())
	}

	/// Tear down the memory at the specified index.
	///
	/// # Errors
	///
	/// Returns `Err` if `memory_idx` isn't a valid index of an memory or
	/// if it has been torn down.
	pub fn memory_teardown(&mut self, memory_idx: u32) -> Result<()> {
		match self.memories.get_mut(memory_idx as usize) {
			None => Err("Trying to teardown a non-existent sandboxed memory".into()),
			Some(None) => Err("Double teardown of a sandboxed memory".into()),
			Some(memory) => {
				*memory = None;
				Ok(())
			}
		}
	}

	/// Tear down the instance at the specified index.
	///
	/// # Errors
	///
	/// Returns `Err` if `instance_idx` isn't a valid index of an instance or
	/// if it has been torn down.
	pub fn instance_teardown(&mut self, instance_idx: u32) -> Result<()> {
		match self.instances.get_mut(instance_idx as usize) {
			None => Err("Trying to teardown a non-existent instance".into()),
			Some(None) => Err("Double teardown of an instance".into()),
			Some(instance) => {
				*instance = None;
				Ok(())
			}
		}
	}

	fn register_sandbox_instance(&mut self, sandbox_instance: Rc<SandboxInstance<FR>>) -> u32 {
		let instance_idx = self.instances.len();
		self.instances.push(Some(sandbox_instance));
		instance_idx as u32
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, traits::Externalities};
	use crate::wasm_runtime::WasmRuntime;
	use crate::wasmi_execution;
	use state_machine::TestExternalities as CoreTestExternalities;
	use wabt;
	use runtime_test::WASM_BINARY;

	type TestExternalities = CoreTestExternalities<Blake2Hasher, u64>;

	fn call_wasm<E: Externalities>(
		ext: &mut E,
		heap_pages: u64,
		code: &[u8],
		method: &str,
		data: &[u8],
	) -> Result<Vec<u8>> {
		let mut instance = wasmi_execution::create_instance(ext, code, heap_pages)
			.map_err(|err| err.to_string())?;
		instance.call(ext, method, data)
	}

	#[test]
	fn sandbox_should_work() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

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
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox", &code).unwrap(),
			true.encode(),
		);
	}

	#[test]
	fn sandbox_trap() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

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
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox", &code).unwrap(),
			vec![0],
		);
	}

	#[test]
	fn sandbox_should_trap_when_heap_exhausted() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))
			(func (export "call")
				i32.const 0
				call $assert
			)
		)
		"#).unwrap().encode();

		let res = call_wasm(&mut ext, 8, &test_code[..], "test_exhaust_heap", &code);
		assert_eq!(res.is_err(), true);
		if let Err(err) = res {
			assert_eq!(
				format!("{}", err),
				format!(
					"{}",
					wasmi::Error::Trap(Error::FunctionExecution("AllocatorOutOfSpace".into()).into()),
				),
			);
		}
	}

	#[test]
	fn start_called() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

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
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox", &code).unwrap(),
			true.encode(),
		);
	}

	#[test]
	fn invoke_args() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call") (param $x i32) (param $y i64)
				;; assert that $x = 0x12345678
				(call $assert
					(i32.eq
						(get_local $x)
						(i32.const 0x12345678)
					)
				)

				(call $assert
					(i64.eq
						(get_local $y)
						(i64.const 0x1234567887654321)
					)
				)
			)
		)
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_args", &code).unwrap(),
			true.encode(),
		);
	}

	#[test]
	fn return_val() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(func (export "call") (param $x i32) (result i32)
				(i32.add
					(get_local $x)
					(i32.const 1)
				)
			)
		)
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_return_val", &code).unwrap(),
			true.encode(),
		);
	}

	#[test]
	fn unlinkable_module() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(import "env" "non-existent" (func))

			(func (export "call")
			)
		)
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_instantiate", &code).unwrap(),
			1u8.encode(),
		);
	}

	#[test]
	fn corrupted_module() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		// Corrupted wasm file
		let code = vec![0u8, 0, 0, 0, 1, 0, 0, 0].encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_instantiate", &code).unwrap(),
			1u8.encode(),
		);
	}

	#[test]
	fn start_fn_ok() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(func (export "call")
			)

			(func $start
			)

			(start $start)
		)
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_instantiate", &code).unwrap(),
			0u8.encode(),
		);
	}

	#[test]
	fn start_fn_traps() {
		let mut ext = TestExternalities::default();
		let mut ext = ext.ext();
		let test_code = WASM_BINARY;

		let code = wabt::wat2wasm(r#"
		(module
			(func (export "call")
			)

			(func $start
				unreachable
			)

			(start $start)
		)
		"#).unwrap().encode();

		assert_eq!(
			call_wasm(&mut ext, 8, &test_code[..], "test_sandbox_instantiate", &code).unwrap(),
			2u8.encode(),
		);
	}
}
