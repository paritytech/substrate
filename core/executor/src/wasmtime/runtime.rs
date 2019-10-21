// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Defines the compiled Wasm runtime that uses Wasmtime internally.

use crate::error::{Error, Result, WasmError};
use crate::host_interface::SubstrateExternals;
use crate::wasm_runtime::WasmRuntime;
use crate::wasmtime::function_executor::FunctionExecutorState;
use crate::wasmtime::trampoline::{TrampolineState, make_trampoline};
use crate::wasmtime::util::{cranelift_ir_signature, read_memory_into};
use crate::{Externalities, RuntimeVersion};

use codec::Decode;
use cranelift_codegen::isa::TargetIsa;
use cranelift_entity::{EntityRef, PrimaryMap};
use cranelift_frontend::FunctionBuilderContext;
use cranelift_wasm::DefinedFuncIndex;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::mem;
use std::rc::Rc;
use wasm_interface::{HostFunctions, Pointer};
use wasmtime_environ::{Module, translate_signature};
use wasmtime_jit::{
	ActionOutcome, ActionError, CodeMemory, CompilationStrategy, CompiledModule, Compiler, Context,
	SetupError, RuntimeValue,
};
use wasmtime_runtime::{Export, Imports, InstanceHandle, VMFunctionBody};

/// A `WasmRuntime` implementation using the Wasmtime JIT to compile the runtime module to native
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	module: CompiledModule,
	context: Context,
	max_heap_pages: Option<u32>,
	heap_pages: u32,
	version: Option<RuntimeVersion>,
}

impl WasmRuntime for WasmtimeRuntime {
	fn update_heap_pages(&mut self, heap_pages: u64) -> bool {
		match heap_pages_valid(heap_pages, self.max_heap_pages) {
			Some(heap_pages) => {
				self.heap_pages = heap_pages;
				true
			}
			None => false,
		}
	}

	fn call(&mut self, ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&mut self.context,
			&mut self.module,
			ext,
			method,
			data,
			self.heap_pages,
		)
	}

	fn version(&self) -> Option<RuntimeVersion> {
		self.version.clone()
	}
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
pub fn create_instance<E: Externalities>(ext: &mut E, code: &[u8], heap_pages: u64)
	-> std::result::Result<WasmtimeRuntime, WasmError>
{
	let (mut compiled_module, mut context) = create_compiled_unit(code)?;

	// Inspect the module for the min and max memory sizes.
	let (min_memory_size, max_memory_size) = {
		let module = compiled_module.module_ref();
		let memory_index = match module.exports.get("memory") {
			Some(wasmtime_environ::Export::Memory(memory_index)) => *memory_index,
			_ => return Err(WasmError::InvalidMemory),
		};
		let memory_plan = module.memory_plans.get(memory_index)
			.expect("memory_index is retrieved from the module's exports map; qed");
		(memory_plan.memory.minimum, memory_plan.memory.maximum)
	};

	// Check that heap_pages is within the allowed range.
	let max_heap_pages = max_memory_size.map(|max| max.saturating_sub(min_memory_size));
	let heap_pages = heap_pages_valid(heap_pages, max_heap_pages)
		.ok_or_else(|| WasmError::InvalidHeapPages)?;

	// Call to determine runtime version.
	let version_result = call_method(
		&mut context,
		&mut compiled_module,
		ext,
		"Core_version",
		&[],
		heap_pages
	);
	let version = version_result
		.ok()
		.and_then(|v| RuntimeVersion::decode(&mut v.as_slice()).ok());
	Ok(WasmtimeRuntime {
		module: compiled_module,
		context,
		max_heap_pages,
		heap_pages,
		version,
	})
}

fn create_compiled_unit(code: &[u8])
	-> std::result::Result<(CompiledModule, Context), WasmError>
{
	let isa = target_isa()?;
	let mut context = Context::with_isa(isa, CompilationStrategy::Cranelift);

	// Enable/disable producing of debug info.
	context.set_debug_info(false);

	// Instantiate and link the env module.
	let global_exports = context.get_global_exports();
	let env_module = instantiate_env_module(global_exports)?;
	context.name_instance("env".to_owned(), env_module);

	// Compile the wasm module.
	let module = context.compile_module(&code)
		.map_err(WasmError::WasmtimeSetup)?;

	Ok((module, context))
}

/// Call a function inside a precompiled Wasm module.
fn call_method(
	context: &mut Context,
	module: &mut CompiledModule,
	ext: &mut dyn Externalities,
	method: &str,
	data: &[u8],
	heap_pages: u32,
) -> Result<Vec<u8>> {
	// Old exports get clobbered in `InstanceHandle::new` if we don't explicitly remove them first.
	//
	// The global exports mechanism is temporary in Wasmtime and expected to be removed.
	// https://github.com/CraneStation/wasmtime/issues/332
	clear_globals(&mut *context.get_global_exports().borrow_mut());

	let mut instance = module.instantiate()
		.map_err(SetupError::Instantiate)
		.map_err(ActionError::Setup)
		.map_err(Error::Wasmtime)?;

	unsafe {
		// Ideally there would be a way to set the heap pages during instantiation rather than
		// growing the memory after the fact. Current this may require an additional mmap and copy.
		// However, the wasmtime API doesn't support modifying the size of memory on instantiation
		// at this time.
		grow_memory(&mut instance, heap_pages)?;

		// Initialize the function executor state.
		let executor_state = FunctionExecutorState::new(
			// Unsafely extend the reference lifetime to static. This is necessary because the
			// host state must be `Any`. This is OK as we will drop this object either before
			// exiting the function in the happy case or in the worst case on the next runtime
			// call, which also resets the host state. Thus this reference can never actually
			// outlive the Context.
			mem::transmute::<_, &'static mut Compiler>(context.compiler_mut()),
			get_heap_base(&instance)?,
		);
		reset_host_state(context, Some(executor_state))?;
	}

	// TODO: Construct arguments properly by allocating heap space with data.
	let args = [];

	// Invoke the function in the runtime.
	let outcome = externalities::set_and_run_with_externalities(ext, || {
		context
			.invoke(&mut instance, method, &args[..])
			.map_err(Error::Wasmtime)
	})?;
	let trap_error = reset_host_state(context, None)?;
	let (output_ptr, output_len) = match outcome {
		ActionOutcome::Returned { values } => {
			if values.len()	!= 1 {
				return Err(Error::InvalidReturn);
			}
			if let RuntimeValue::I64(val) = values[0] {
				let output_ptr = <Pointer<u8>>::new(val as u32);
				let output_len = ((val as u64) >> 32) as usize;
				(output_ptr, output_len)
			} else {
				return Err(Error::InvalidReturn);
			}
		}
		ActionOutcome::Trapped { message } =>
			return Err(trap_error.unwrap_or_else(||
				format!("Wasm execution trapped: {}", message).into()
			)),
	};

	// Read the output data from guest memory.
	let mut output = vec![0; output_len];
	let memory = unsafe { get_memory_mut(&mut instance)? };
	read_memory_into(memory, output_ptr, &mut output)?;
	Ok(output)
}

/// The implementation is based on wasmtime_wasi::instantiate_wasi.
fn instantiate_env_module(global_exports: Rc<RefCell<HashMap<String, Option<Export>>>>)
	-> std::result::Result<InstanceHandle, WasmError>
{
	let isa = target_isa()?;
	let pointer_type = isa.pointer_type();
	let call_conv = isa.default_call_conv();

	let mut fn_builder_ctx = FunctionBuilderContext::new();
	let mut module = Module::new();
	let mut finished_functions = <PrimaryMap<DefinedFuncIndex, *const VMFunctionBody>>::new();
	let mut code_memory = CodeMemory::new();

	for function in SubstrateExternals::functions().iter() {
		let sig = translate_signature(
			cranelift_ir_signature(function.signature(), &call_conv),
			pointer_type
		);
		let sig_id = module.signatures.push(sig.clone());
		let func_id = module.functions.push(sig_id);
		module
			.exports
			.insert(function.name().to_string(), wasmtime_environ::Export::Function(func_id));

		let trampoline = make_trampoline(
			isa.as_ref(),
			&mut code_memory,
			&mut fn_builder_ctx,
			func_id.index() as u32,
			&sig,
		);
		finished_functions.push(trampoline);
	}

	code_memory.publish();

	let imports = Imports::none();
	let data_initializers = Vec::new();
	let signatures = PrimaryMap::new();
	let host_state = TrampolineState::new::<SubstrateExternals>(code_memory);

	let result = InstanceHandle::new(
		Rc::new(module),
		global_exports,
		finished_functions.into_boxed_slice(),
		imports,
		&data_initializers,
		signatures.into_boxed_slice(),
		None,
		Box::new(host_state),
	);
	result.map_err(|e| WasmError::WasmtimeSetup(SetupError::Instantiate(e)))
}

/// Build a new TargetIsa for the host machine.
fn target_isa() -> std::result::Result<Box<dyn TargetIsa>, WasmError> {
	let isa_builder = cranelift_native::builder()
		.map_err(WasmError::MissingCompilerSupport)?;
	let flag_builder = cranelift_codegen::settings::builder();
	Ok(isa_builder.finish(cranelift_codegen::settings::Flags::new(flag_builder)))
}

fn clear_globals(global_exports: &mut HashMap<String, Option<Export>>) {
	global_exports.remove("memory");
	global_exports.remove("__heap_base");
	global_exports.remove("__indirect_function_table");
}

unsafe fn grow_memory(instance: &mut InstanceHandle, pages: u32) -> Result<()> {
	let memory_index = match instance.lookup_immutable("memory") {
		Some(Export::Memory { definition, vmctx: _, memory: _ }) =>
			instance.memory_index(&*definition),
		_ => return Err(Error::InvalidMemoryReference),
	};
	instance.memory_grow(memory_index, pages)
		.map(|_| ())
		.ok_or_else(|| "requested heap_pages would exceed maximum memory size".into())
}

fn get_host_state(context: &mut Context) -> Result<&mut TrampolineState> {
	let env_instance = context.get_instance("env")
		.map_err(|err| format!("cannot find \"env\" module: {}", err))?;
	env_instance
		.host_state()
		.downcast_mut::<TrampolineState>()
		.ok_or_else(|| "cannot get \"env\" module host state".into())
}

fn reset_host_state(context: &mut Context, executor_state: Option<FunctionExecutorState>)
	-> Result<Option<Error>>
{
	let trampoline_state = get_host_state(context)?;
	trampoline_state.executor_state = executor_state;
	Ok(trampoline_state.reset_trap())
}

unsafe fn get_memory_mut(instance: &mut InstanceHandle) -> Result<&mut [u8]> {
	match instance.lookup("memory") {
		Some(Export::Memory { definition, vmctx: _, memory: _ }) =>
			Ok(std::slice::from_raw_parts_mut(
				(*definition).base,
				(*definition).current_length,
			)),
		_ => Err(Error::InvalidMemoryReference),
	}
}

unsafe fn get_heap_base(instance: &InstanceHandle) -> Result<u32> {
	match instance.lookup_immutable("__heap_base") {
		Some(Export::Global { definition, vmctx: _, global: _ }) =>
			Ok(*(*definition).as_u32()),
		_ => return Err(Error::HeapBaseNotFoundOrInvalid),
	}
}

/// Checks whether the heap_pages parameter is within the valid range and converts it to a u32.
/// Returns None if heaps_pages in not in range.
fn heap_pages_valid(heap_pages: u64, max_heap_pages: Option<u32>)
	-> Option<u32>
{
	let heap_pages = u32::try_from(heap_pages).ok()?;
	if let Some(max_heap_pages) = max_heap_pages {
		if heap_pages > max_heap_pages {
			return None;
		}
	}
	Some(heap_pages)
}
