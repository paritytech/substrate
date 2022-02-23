// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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
//! Sandboxing is backed by wasmi and wasmer, depending on the configuration.

#[cfg(feature = "wasmer-sandbox")]
mod wasmer_backend;

mod wasmi_backend;

use crate::{
	error::{self, Result},
	util,
};
use codec::Decode;
use sp_core::sandbox as sandbox_primitives;
use sp_wasm_interface::{FunctionContext, Pointer, WordSize};
use std::{collections::HashMap, rc::Rc};

#[cfg(feature = "wasmer-sandbox")]
use wasmer_backend::{
	instantiate as wasmer_instantiate, invoke as wasmer_invoke, new_memory as wasmer_new_memory,
	Backend as WasmerBackend, MemoryWrapper as WasmerMemoryWrapper,
};

use wasmi_backend::{
	instantiate as wasmi_instantiate, invoke as wasmi_invoke, new_memory as wasmi_new_memory,
	MemoryWrapper as WasmiMemoryWrapper,
};

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
/// This index is supposed to be used as index for `Externals`.
#[derive(Copy, Clone, Debug, PartialEq)]
struct GuestFuncIndex(usize);

/// This struct holds a mapping from guest index space to supervisor.
struct GuestToSupervisorFunctionMapping {
	/// Position of elements in this vector are interpreted
	/// as indices of guest functions and are mapped to
	/// corresponding supervisor function indices.
	funcs: Vec<SupervisorFuncIndex>,
}

impl GuestToSupervisorFunctionMapping {
	/// Create an empty function mapping
	fn new() -> GuestToSupervisorFunctionMapping {
		GuestToSupervisorFunctionMapping { funcs: Vec::new() }
	}

	/// Add a new supervisor function to the mapping.
	/// Returns a newly assigned guest function index.
	fn define(&mut self, supervisor_func: SupervisorFuncIndex) -> GuestFuncIndex {
		let idx = self.funcs.len();
		self.funcs.push(supervisor_func);
		GuestFuncIndex(idx)
	}

	/// Find supervisor function index by its corresponding guest function index
	fn func_by_guest_index(&self, guest_func_idx: GuestFuncIndex) -> Option<SupervisorFuncIndex> {
		self.funcs.get(guest_func_idx.0).cloned()
	}
}

/// Holds sandbox function and memory imports and performs name resolution
struct Imports {
	/// Maps qualified function name to its guest function index
	func_map: HashMap<(Vec<u8>, Vec<u8>), GuestFuncIndex>,

	/// Maps qualified field name to its memory reference
	memories_map: HashMap<(Vec<u8>, Vec<u8>), Memory>,
}

impl Imports {
	fn func_by_name(&self, module_name: &str, func_name: &str) -> Option<GuestFuncIndex> {
		self.func_map
			.get(&(module_name.as_bytes().to_owned(), func_name.as_bytes().to_owned()))
			.cloned()
	}

	fn memory_by_name(&self, module_name: &str, memory_name: &str) -> Option<Memory> {
		self.memories_map
			.get(&(module_name.as_bytes().to_owned(), memory_name.as_bytes().to_owned()))
			.cloned()
	}
}

/// The sandbox context used to execute sandboxed functions.
pub trait SandboxContext {
	/// Invoke a function in the supervisor environment.
	///
	/// This first invokes the dispatch thunk function, passing in the function index of the
	/// desired function to call and serialized arguments. The thunk calls the desired function
	/// with the deserialized arguments, then serializes the result into memory and returns
	/// reference. The pointer to and length of the result in linear memory is encoded into an
	/// `i64`, with the upper 32 bits representing the pointer and the lower 32 bits representing
	/// the length.
	///
	/// # Errors
	///
	/// Returns `Err` if the dispatch_thunk function has an incorrect signature or traps during
	/// execution.
	fn invoke(
		&mut self,
		invoke_args_ptr: Pointer<u8>,
		invoke_args_len: WordSize,
		state: u32,
		func_idx: SupervisorFuncIndex,
	) -> Result<i64>;

	/// Returns the supervisor context.
	fn supervisor_context(&mut self) -> &mut dyn FunctionContext;
}

/// Implementation of [`Externals`] that allows execution of guest module with
/// [externals][`Externals`] that might refer functions defined by supervisor.
///
/// [`Externals`]: ../wasmi/trait.Externals.html
pub struct GuestExternals<'a> {
	/// Instance of sandboxed module to be dispatched
	sandbox_instance: &'a SandboxInstance,

	/// External state passed to guest environment, see the `instantiate` function
	state: u32,
}

/// Module instance in terms of selected backend
enum BackendInstance {
	/// Wasmi module instance
	Wasmi(wasmi::ModuleRef),

	/// Wasmer module instance
	#[cfg(feature = "wasmer-sandbox")]
	Wasmer(wasmer::Instance),
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
pub struct SandboxInstance {
	backend_instance: BackendInstance,
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
	pub fn invoke(
		&self,
		export_name: &str,
		args: &[sp_wasm_interface::Value],
		state: u32,
		sandbox_context: &mut dyn SandboxContext,
	) -> std::result::Result<Option<sp_wasm_interface::Value>, error::Error> {
		match &self.backend_instance {
			BackendInstance::Wasmi(wasmi_instance) =>
				wasmi_invoke(self, wasmi_instance, export_name, args, state, sandbox_context),

			#[cfg(feature = "wasmer-sandbox")]
			BackendInstance::Wasmer(wasmer_instance) =>
				wasmer_invoke(wasmer_instance, export_name, args, state, sandbox_context),
		}
	}

	/// Get the value from a global with the given `name`.
	///
	/// Returns `Some(_)` if the global could be found.
	pub fn get_global_val(&self, name: &str) -> Option<sp_wasm_interface::Value> {
		match &self.backend_instance {
			BackendInstance::Wasmi(wasmi_instance) => {
				let wasmi_global = wasmi_instance.export_by_name(name)?.as_global()?.get();

				Some(wasmi_global.into())
			},

			#[cfg(feature = "wasmer-sandbox")]
			BackendInstance::Wasmer(wasmer_instance) => {
				use sp_wasm_interface::Value;

				let global = wasmer_instance.exports.get_global(name).ok()?;
				let wasmtime_value = match global.get() {
					wasmer::Val::I32(val) => Value::I32(val),
					wasmer::Val::I64(val) => Value::I64(val),
					wasmer::Val::F32(val) => Value::F32(f32::to_bits(val)),
					wasmer::Val::F64(val) => Value::F64(f64::to_bits(val)),
					_ => None?,
				};

				Some(wasmtime_value)
			},
		}
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
	mut raw_env_def: &[u8],
	memories: &[Option<Memory>],
) -> std::result::Result<(Imports, GuestToSupervisorFunctionMapping), InstantiationError> {
	let env_def = sandbox_primitives::EnvironmentDefinition::decode(&mut raw_env_def)
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
			},
			sandbox_primitives::ExternEntity::Memory(memory_idx) => {
				let memory_ref = memories
					.get(memory_idx as usize)
					.cloned()
					.ok_or_else(|| InstantiationError::EnvironmentDefinitionCorrupted)?
					.ok_or_else(|| InstantiationError::EnvironmentDefinitionCorrupted)?;
				memories_map.insert((module, field), memory_ref);
			},
		}
	}

	Ok((Imports { func_map, memories_map }, guest_to_supervisor_mapping))
}

/// An environment in which the guest module is instantiated.
pub struct GuestEnvironment {
	/// Function and memory imports of the guest module
	imports: Imports,

	/// Supervisor functinons mapped to guest index space
	guest_to_supervisor_mapping: GuestToSupervisorFunctionMapping,
}

impl GuestEnvironment {
	/// Decodes an environment definition from the given raw bytes.
	///
	/// Returns `Err` if the definition cannot be decoded.
	pub fn decode<DT>(
		store: &Store<DT>,
		raw_env_def: &[u8],
	) -> std::result::Result<Self, InstantiationError> {
		let (imports, guest_to_supervisor_mapping) =
			decode_environment_definition(raw_env_def, &store.memories)?;
		Ok(Self { imports, guest_to_supervisor_mapping })
	}
}

/// An unregistered sandboxed instance.
///
/// To finish off the instantiation the user must call `register`.
#[must_use]
pub struct UnregisteredInstance {
	sandbox_instance: Rc<SandboxInstance>,
}

impl UnregisteredInstance {
	/// Finalizes instantiation of this module.
	pub fn register<DT>(self, store: &mut Store<DT>, dispatch_thunk: DT) -> u32 {
		// At last, register the instance.
		store.register_sandbox_instance(self.sandbox_instance, dispatch_thunk)
	}
}

/// Sandbox backend to use
pub enum SandboxBackend {
	/// Wasm interpreter
	Wasmi,

	/// Wasmer environment
	#[cfg(feature = "wasmer-sandbox")]
	Wasmer,

	/// Use wasmer backend if available. Fall back to wasmi otherwise.
	TryWasmer,
}

/// Memory reference in terms of a selected backend
#[derive(Clone, Debug)]
pub enum Memory {
	/// Wasmi memory reference
	Wasmi(WasmiMemoryWrapper),

	/// Wasmer memory refernce
	#[cfg(feature = "wasmer-sandbox")]
	Wasmer(WasmerMemoryWrapper),
}

impl Memory {
	/// View as wasmi memory
	pub fn as_wasmi(&self) -> Option<WasmiMemoryWrapper> {
		match self {
			Memory::Wasmi(memory) => Some(memory.clone()),

			#[cfg(feature = "wasmer-sandbox")]
			Memory::Wasmer(_) => None,
		}
	}

	/// View as wasmer memory
	#[cfg(feature = "wasmer-sandbox")]
	pub fn as_wasmer(&self) -> Option<WasmerMemoryWrapper> {
		match self {
			Memory::Wasmer(memory) => Some(memory.clone()),
			Memory::Wasmi(_) => None,
		}
	}
}

impl util::MemoryTransfer for Memory {
	fn read(&self, source_addr: Pointer<u8>, size: usize) -> Result<Vec<u8>> {
		match self {
			Memory::Wasmi(sandboxed_memory) => sandboxed_memory.read(source_addr, size),

			#[cfg(feature = "wasmer-sandbox")]
			Memory::Wasmer(sandboxed_memory) => sandboxed_memory.read(source_addr, size),
		}
	}

	fn read_into(&self, source_addr: Pointer<u8>, destination: &mut [u8]) -> Result<()> {
		match self {
			Memory::Wasmi(sandboxed_memory) => sandboxed_memory.read_into(source_addr, destination),

			#[cfg(feature = "wasmer-sandbox")]
			Memory::Wasmer(sandboxed_memory) => sandboxed_memory.read_into(source_addr, destination),
		}
	}

	fn write_from(&self, dest_addr: Pointer<u8>, source: &[u8]) -> Result<()> {
		match self {
			Memory::Wasmi(sandboxed_memory) => sandboxed_memory.write_from(dest_addr, source),

			#[cfg(feature = "wasmer-sandbox")]
			Memory::Wasmer(sandboxed_memory) => sandboxed_memory.write_from(dest_addr, source),
		}
	}
}

/// Information specific to a particular execution backend
enum BackendContext {
	/// Wasmi specific context
	Wasmi,

	/// Wasmer specific context
	#[cfg(feature = "wasmer-sandbox")]
	Wasmer(WasmerBackend),
}

impl BackendContext {
	pub fn new(backend: SandboxBackend) -> BackendContext {
		match backend {
			SandboxBackend::Wasmi => BackendContext::Wasmi,

			#[cfg(not(feature = "wasmer-sandbox"))]
			SandboxBackend::TryWasmer => BackendContext::Wasmi,

			#[cfg(feature = "wasmer-sandbox")]
			SandboxBackend::Wasmer | SandboxBackend::TryWasmer =>
				BackendContext::Wasmer(WasmerBackend::new()),
		}
	}
}

/// This struct keeps track of all sandboxed components.
///
/// This is generic over a supervisor function reference type.
pub struct Store<DT> {
	/// Stores the instance and the dispatch thunk associated to per instance.
	///
	/// Instances are `Some` until torn down.
	instances: Vec<Option<(Rc<SandboxInstance>, DT)>>,
	/// Memories are `Some` until torn down.
	memories: Vec<Option<Memory>>,
	backend_context: BackendContext,
}

impl<DT: Clone> Store<DT> {
	/// Create a new empty sandbox store.
	pub fn new(backend: SandboxBackend) -> Self {
		Store {
			instances: Vec::new(),
			memories: Vec::new(),
			backend_context: BackendContext::new(backend),
		}
	}

	/// Create a new memory instance and return it's index.
	///
	/// # Errors
	///
	/// Returns `Err` if the memory couldn't be created.
	/// Typically happens if `initial` is more than `maximum`.
	pub fn new_memory(&mut self, initial: u32, maximum: u32) -> Result<u32> {
		let memories = &mut self.memories;
		let backend_context = &self.backend_context;

		let maximum = match maximum {
			sandbox_primitives::MEM_UNLIMITED => None,
			specified_limit => Some(specified_limit),
		};

		let memory = match &backend_context {
			BackendContext::Wasmi => wasmi_new_memory(initial, maximum)?,

			#[cfg(feature = "wasmer-sandbox")]
			BackendContext::Wasmer(context) => wasmer_new_memory(context, initial, maximum)?,
		};

		let mem_idx = memories.len();
		memories.push(Some(memory.clone()));

		Ok(mem_idx as u32)
	}

	/// Returns `SandboxInstance` by `instance_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `instance_idx` isn't a valid index of an instance or
	/// instance is already torndown.
	pub fn instance(&self, instance_idx: u32) -> Result<Rc<SandboxInstance>> {
		self.instances
			.get(instance_idx as usize)
			.ok_or_else(|| "Trying to access a non-existent instance")?
			.as_ref()
			.map(|v| v.0.clone())
			.ok_or_else(|| "Trying to access a torndown instance".into())
	}

	/// Returns dispatch thunk by `instance_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `instance_idx` isn't a valid index of an instance or
	/// instance is already torndown.
	pub fn dispatch_thunk(&self, instance_idx: u32) -> Result<DT> {
		self.instances
			.get(instance_idx as usize)
			.as_ref()
			.ok_or_else(|| "Trying to access a non-existent instance")?
			.as_ref()
			.map(|v| v.1.clone())
			.ok_or_else(|| "Trying to access a torndown instance".into())
	}

	/// Returns reference to a memory instance by `memory_idx`.
	///
	/// # Errors
	///
	/// Returns `Err` If `memory_idx` isn't a valid index of an memory or
	/// if memory has been torn down.
	pub fn memory(&self, memory_idx: u32) -> Result<Memory> {
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
			},
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
			},
		}
	}

	/// Instantiate a guest module and return it's index in the store.
	///
	/// The guest module's code is specified in `wasm`. Environment that will be available to
	/// guest module is specified in `guest_env`. A dispatch thunk is used as function that
	/// handle calls from guests. `state` is an opaque pointer to caller's arbitrary context
	/// normally created by `sp_sandbox::Instance` primitive.
	///
	/// Note: Due to borrowing constraints dispatch thunk is now propagated using DTH
	///
	/// Returns uninitialized sandboxed module instance or an instantiation error.
	pub fn instantiate(
		&mut self,
		wasm: &[u8],
		guest_env: GuestEnvironment,
		state: u32,
		sandbox_context: &mut dyn SandboxContext,
	) -> std::result::Result<UnregisteredInstance, InstantiationError> {
		let sandbox_instance = match self.backend_context {
			BackendContext::Wasmi => wasmi_instantiate(wasm, guest_env, state, sandbox_context)?,

			#[cfg(feature = "wasmer-sandbox")]
			BackendContext::Wasmer(ref context) =>
				wasmer_instantiate(&context, wasm, guest_env, state, sandbox_context)?,
		};

		Ok(UnregisteredInstance { sandbox_instance })
	}
}

// Private routines
impl<DT> Store<DT> {
	fn register_sandbox_instance(
		&mut self,
		sandbox_instance: Rc<SandboxInstance>,
		dispatch_thunk: DT,
	) -> u32 {
		let instance_idx = self.instances.len();
		self.instances.push(Some((sandbox_instance, dispatch_thunk)));
		instance_idx as u32
	}
}
