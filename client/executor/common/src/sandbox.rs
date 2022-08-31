// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! This module implements sandboxing support in the runtime.
//!
//! Sandboxing is baked by wasmi at the moment. In future, however, we would like to add/switch to
//! a compiled execution engine.

use crate::error::{Result, Error};
use std::{collections::HashMap, rc::Rc};
use codec::{Decode, Encode};
use sp_core::sandbox as sandbox_primitives;
use wasmi::{
	Externals, ImportResolver, MemoryInstance, MemoryRef, Module, ModuleInstance,
	ModuleRef, RuntimeArgs, RuntimeValue, Trap, TrapKind, memory_units::Pages,
};
use sp_wasm_interface::{FunctionContext, Pointer, WordSize};

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
pub trait SandboxCapabilities: FunctionContext {
	/// Represents a function reference into the supervisor environment.
	type SupervisorFuncRef;

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
/// [`Externals`]: ../wasmi/trait.Externals.html
pub struct GuestExternals<'a, FE: SandboxCapabilities + 'a> {
	supervisor_externals: &'a mut FE,
	sandbox_instance: &'a SandboxInstance<FE::SupervisorFuncRef>,
	state: u32,
}

fn trap(msg: &'static str) -> Trap {
	TrapKind::Host(Box::new(Error::Other(msg.into()))).into()
}

fn deserialize_result(serialized_result: &[u8]) -> std::result::Result<Option<RuntimeValue>, Trap> {
	use self::sandbox_primitives::HostError;
	use sp_wasm_interface::ReturnValue;
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
			.map(sp_wasm_interface::Value::from)
			.collect::<Vec<_>>()
			.encode();

		let state = self.state;

		// Move serialized arguments inside the memory and invoke dispatch thunk and
		// then free allocated memory.
		let invoke_args_len = invoke_args_data.len() as WordSize;
		let invoke_args_ptr = self
			.supervisor_externals
			.allocate_memory(invoke_args_len)
			.map_err(|_| trap("Can't allocate memory in supervisor for the arguments"))?;

		let deallocate = |this: &mut GuestExternals<FE>, ptr, fail_msg| {
			this
				.supervisor_externals
				.deallocate_memory(ptr)
				.map_err(|_| trap(fail_msg))
		};

		if self
			.supervisor_externals
			.write_memory(invoke_args_ptr, &invoke_args_data)
			.is_err()
		{
			deallocate(self, invoke_args_ptr, "Failed dealloction after failed write of invoke arguments")?;
			return Err(trap("Can't write invoke args into memory"));
		}

		let result = self.supervisor_externals.invoke(
			&self.sandbox_instance.dispatch_thunk,
			invoke_args_ptr,
			invoke_args_len,
			state,
			func_idx,
		);

		deallocate(self, invoke_args_ptr, "Can't deallocate memory for dispatch thunk's invoke arguments")?;
		let result = result?;

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
			.read_memory(serialized_result_val_ptr, serialized_result_val_len)
			.map_err(|_| trap("Can't read the serialized result from dispatch thunk"));

		deallocate(self, serialized_result_val_ptr, "Can't deallocate memory for dispatch thunk's result")
			.and_then(|_| serialized_result_val)
			.and_then(|serialized_result_val| deserialize_result(&serialized_result_val))
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

	/// Get the value from a global with the given `name`.
	///
	/// Returns `Some(_)` if the global could be found.
	pub fn get_global_val(&self, name: &str) -> Option<sp_wasm_interface::Value> {
		let global = self.instance
			.export_by_name(name)?
			.as_global()?
			.get();

		Some(global.into())
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

/// An environment in which the guest module is instantiated.
pub struct GuestEnvironment {
	imports: Imports,
	guest_to_supervisor_mapping: GuestToSupervisorFunctionMapping,
}

impl GuestEnvironment {
	/// Decodes an environment definition from the given raw bytes.
	///
	/// Returns `Err` if the definition cannot be decoded.
	pub fn decode<FR>(
		store: &Store<FR>,
		raw_env_def: &[u8],
	) -> std::result::Result<Self, InstantiationError> {
		let (imports, guest_to_supervisor_mapping) =
			decode_environment_definition(raw_env_def, &store.memories)?;
		Ok(Self {
			imports,
			guest_to_supervisor_mapping,
		})
	}
}

/// An unregistered sandboxed instance.
///
/// To finish off the instantiation the user must call `register`.
#[must_use]
pub struct UnregisteredInstance<FR> {
	sandbox_instance: Rc<SandboxInstance<FR>>,
}

impl<FR> UnregisteredInstance<FR> {
	/// Finalizes instantiation of this module.
	pub fn register(self, store: &mut Store<FR>) -> u32 {
		// At last, register the instance.
		let instance_idx = store.register_sandbox_instance(self.sandbox_instance);
		instance_idx
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
/// [`EnvironmentDefinition`]: ../sandbox/struct.EnvironmentDefinition.html
pub fn instantiate<'a, FE: SandboxCapabilities>(
	supervisor_externals: &mut FE,
	dispatch_thunk: FE::SupervisorFuncRef,
	wasm: &[u8],
	host_env: GuestEnvironment,
	state: u32,
) -> std::result::Result<UnregisteredInstance<FE::SupervisorFuncRef>, InstantiationError> {
	let module = Module::from_buffer(wasm).map_err(|_| InstantiationError::ModuleDecoding)?;
	let instance = ModuleInstance::new(&module, &host_env.imports)
		.map_err(|_| InstantiationError::Instantiation)?;

	let sandbox_instance = Rc::new(SandboxInstance {
		// In general, it's not a very good idea to use `.not_started_instance()` for anything
		// but for extracting memory and tables. But in this particular case, we are extracting
		// for the purpose of running `start` function which should be ok.
		instance: instance.not_started_instance().clone(),
		dispatch_thunk,
		guest_to_supervisor_mapping: host_env.guest_to_supervisor_mapping,
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

	Ok(UnregisteredInstance { sandbox_instance })
}

/// This struct keeps track of all sandboxed components.
///
/// This is generic over a supervisor function reference type.
pub struct Store<FR> {
	// Memories and instances are `Some` until torn down.
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
