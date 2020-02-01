// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::function_executor::FunctionExecutorState;
use crate::trampoline::{EnvState, make_trampoline};
use crate::util::{
	cranelift_ir_signature,
	convert_parity_wasm_signature,
	read_memory_into,
	write_memory_from
};

use sc_executor_common::{
	error::{Error, Result, WasmError},
	wasm_runtime::WasmRuntime,
};
use sp_wasm_interface::{Pointer, WordSize, Function};
use sp_runtime_interface::unpack_ptr_and_len;

use std::{cell::RefCell, collections::HashMap, convert::TryFrom, rc::Rc};

use cranelift_codegen::ir;
use cranelift_codegen::isa::TargetIsa;
use cranelift_entity::{EntityRef, PrimaryMap};
use cranelift_frontend::FunctionBuilderContext;
use cranelift_wasm::{DefinedFuncIndex, MemoryIndex};
use wasmtime_environ::{Module, translate_signature};
use wasmtime_jit::{
	ActionOutcome, CodeMemory, CompilationStrategy, CompiledModule, Compiler, Context, RuntimeValue,
};
use wasmtime_runtime::{Export, Imports, InstanceHandle, VMFunctionBody};

/// TODO: We should remove this in https://github.com/paritytech/substrate/pull/4686
/// Currently there is no way to extract this with wasmtime.
const INITIAL_HEAP_PAGES: u32 = 17;

/// A `WasmRuntime` implementation using the Wasmtime JIT to compile the runtime module to native
/// and execute the compiled code.
pub struct WasmtimeRuntime {
	module: CompiledModule,
	context: Context,
	heap_pages: u32,
	/// The host functions registered for this instance.
	host_functions: Vec<&'static dyn Function>,
	/// The index of the memory in the module.
	memory_index: MemoryIndex,
}

impl WasmRuntime for WasmtimeRuntime {
	fn update_heap_pages(&mut self, heap_pages: u64) -> bool {
		self.heap_pages as u64 == heap_pages
	}

	fn host_functions(&self) -> &[&'static dyn Function] {
		&self.host_functions
	}

	fn call(&mut self, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		call_method(
			&mut self.context,
			&mut self.module,
			method,
			data,
			self.memory_index,
			self.heap_pages,
		)
	}
}

/// Create a new `WasmtimeRuntime` given the code. This function performs translation from Wasm to
/// machine code, which can be computationally heavy.
pub fn create_instance(
	code: &[u8],
	heap_pages: u64,
	host_functions: Vec<&'static dyn Function>,
	allow_missing_func_imports: bool,
) -> std::result::Result<WasmtimeRuntime, WasmError> {
	let heap_pages = u32::try_from(heap_pages)
		.map_err(|e|
			WasmError::Other(format!("Heap pages can not be converted into `u32`: {:?}", e))
		)?;

	let (compiled_module, context, memory_index) = create_compiled_unit(
		code,
		&host_functions,
		heap_pages,
		allow_missing_func_imports,
	)?;

	let module = compiled_module.module_ref();
	if !module.is_imported_memory(memory_index) {
		// Inspect the module for the min and max memory sizes.
		let (min_memory_size, max_memory_size) = {
			let memory_plan = module.memory_plans
				.get(memory_index)
				.ok_or_else(|| WasmError::InvalidMemory)?;
			(memory_plan.memory.minimum, memory_plan.memory.maximum)
		};

		// Check that heap_pages is within the allowed range.
		let max_heap_pages = max_memory_size.map(|max| max.saturating_sub(min_memory_size));

		if max_heap_pages.map(|m| heap_pages > m).unwrap_or(false) {
			return Err(WasmError::InvalidHeapPages)
		}
	}

	Ok(WasmtimeRuntime {
		module: compiled_module,
		context,
		heap_pages,
		host_functions,
		memory_index,
	})
}

#[derive(Debug)]
struct MissingFunction {
	name: String,
	sig: cranelift_codegen::ir::Signature,
}

#[derive(Debug)]
struct MissingFunctionStubs {
	stubs: HashMap<String, Vec<MissingFunction>>,
}

impl MissingFunctionStubs {
	fn new() -> Self {
		Self {
			stubs: HashMap::new(),
		}
	}

	fn insert(&mut self, module: String, name: String, sig: cranelift_codegen::ir::Signature) {
		self.stubs.entry(module).or_insert_with(Vec::new).push(MissingFunction {
			name,
			sig,
		});
	}
}

fn scan_missing_functions(
	code: &[u8],
	host_functions: &[&'static dyn Function],
) -> std::result::Result<MissingFunctionStubs, WasmError> {
	let isa = target_isa()?;
	let call_conv = isa.default_call_conv();

	let module = parity_wasm::elements::Module::from_bytes(code)
		.map_err(|e| WasmError::Other(format!("cannot deserialize error: {}", e)))?;

	let types = module.type_section().map(|ts| ts.types()).unwrap_or(&[]);
	let import_entries = module
		.import_section()
		.map(|is| is.entries())
		.unwrap_or(&[]);

	let mut missing_functions = MissingFunctionStubs::new();
	for import_entry in import_entries {
		let func_ty = match import_entry.external() {
			parity_wasm::elements::External::Function(func_ty_idx) => {
				let parity_wasm::elements::Type::Function(ref func_ty) =
					types.get(*func_ty_idx as usize).ok_or_else(|| {
						WasmError::Other(format!("corrupted module, type out of bounds"))
					})?;
				func_ty
			}
			_ => {
				// We are looking only for missing **functions** here. Any other items, be they
				// missing or not, will be handled at the resolution stage later.
				continue;
			}
		};
		let signature = convert_parity_wasm_signature(func_ty);

		if import_entry.module() == "env" {
			if let Some(hf) = host_functions
				.iter()
				.find(|hf| hf.name() == import_entry.field())
			{
				if signature == hf.signature() {
					continue;
				}
			}
		}

		// This function is either not from the env module, or doesn't have a corresponding host
		// function, or the signature is not matching. Add it to the list.
		let sig = cranelift_ir_signature(signature, &call_conv);

		missing_functions.insert(
			import_entry.module().to_string(),
			import_entry.field().to_string(),
			sig,
		);
	}

	Ok(missing_functions)
}

fn create_compiled_unit(
	code: &[u8],
	host_functions: &[&'static dyn Function],
	heap_pages: u32,
	allow_missing_func_imports: bool,
) -> std::result::Result<(CompiledModule, Context, MemoryIndex), WasmError> {
	let compilation_strategy = CompilationStrategy::Cranelift;

	let compiler = new_compiler(compilation_strategy)?;
	let mut context = Context::new(Box::new(compiler));

	// Enable/disable producing of debug info.
	context.set_debug_info(false);

	// Instantiate and link the env module.
	let global_exports = context.get_global_exports();
	let compiler = new_compiler(compilation_strategy)?;

	let mut missing_functions_stubs = if allow_missing_func_imports {
		scan_missing_functions(code, host_functions)?
	} else {
		// If there are in fact missing functions they will be detected at the instantiation time
		// and the module will be rejected.
		MissingFunctionStubs::new()
	};

	let env_missing_functions = missing_functions_stubs.stubs
		.remove("env")
		.unwrap_or_else(|| Vec::new());

	let (module, memory_index) = instantiate_env_module(
		global_exports,
		compiler,
		host_functions,
		heap_pages,
		env_missing_functions,
		true,
	)?;

	context.name_instance("env".to_owned(), module);

	for (module, missing_functions_stubs) in missing_functions_stubs.stubs {
		let compiler = new_compiler(compilation_strategy)?;
		let global_exports = context.get_global_exports();
		let instance = instantiate_env_module(
			global_exports,
			compiler,
			&[],
			heap_pages,
			missing_functions_stubs,
			false,
		)?.0;
		context.name_instance(module, instance);
	}

	// Compile the wasm module.
	let module = context.compile_module(&code)
		.map_err(|e| WasmError::Other(format!("module compile error: {}", e)))?;

	Ok((module, context, memory_index.expect("Memory is added on request; qed")))
}

/// Call a function inside a precompiled Wasm module.
fn call_method(
	context: &mut Context,
	module: &mut CompiledModule,
	method: &str,
	data: &[u8],
	memory_index: MemoryIndex,
	heap_pages: u32,
) -> Result<Vec<u8>> {
	let is_imported_memory = module.module().is_imported_memory(memory_index);
	// Old exports get clobbered in `InstanceHandle::new` if we don't explicitly remove them first.
	//
	// The global exports mechanism is temporary in Wasmtime and expected to be removed.
	// https://github.com/CraneStation/wasmtime/issues/332
	clear_globals(&mut *context.get_global_exports().borrow_mut(), is_imported_memory);

	let mut instance = module.instantiate().map_err(|e| Error::Other(e.to_string()))?;

	if !is_imported_memory {
		grow_memory(&mut instance, heap_pages)?;
	}

	// Initialize the function executor state.
	let heap_base = get_heap_base(&instance)?;
	let executor_state = FunctionExecutorState::new(heap_base);
	reset_env_state_and_take_trap(context, Some(executor_state))?;

	// Write the input data into guest memory.
	let (data_ptr, data_len) = inject_input_data(context, &mut instance, data, memory_index)?;
	let args = [RuntimeValue::I32(u32::from(data_ptr) as i32), RuntimeValue::I32(data_len as i32)];

	// Invoke the function in the runtime.
	let outcome = context
		.invoke(&mut instance, method, &args[..])
		.map_err(|e| Error::Other(format!("error calling runtime: {}", e)))?;
	let trap_error = reset_env_state_and_take_trap(context, None)?;
	let (output_ptr, output_len) = match outcome {
		ActionOutcome::Returned { values } => match values.as_slice() {
			[RuntimeValue::I64(retval)] => unpack_ptr_and_len(*retval as u64),
			_ => return Err(Error::InvalidReturn),
		}
		ActionOutcome::Trapped { message } => return Err(trap_error.unwrap_or_else(
			|| format!("Wasm execution trapped: {}", message).into()
		)),
	};

	// Read the output data from guest memory.
	let mut output = vec![0; output_len as usize];
	let memory = get_memory_mut(&mut instance, memory_index)?;
	read_memory_into(memory, Pointer::new(output_ptr), &mut output)?;
	Ok(output)
}

/// The implementation is based on wasmtime_wasi::instantiate_wasi.
fn instantiate_env_module(
	global_exports: Rc<RefCell<HashMap<String, Option<Export>>>>,
	compiler: Compiler,
	host_functions: &[&'static dyn Function],
	heap_pages: u32,
	missing_functions_stubs: Vec<MissingFunction>,
	add_memory: bool,
) -> std::result::Result<(InstanceHandle, Option<MemoryIndex>), WasmError> {
	let isa = target_isa()?;
	let pointer_type = isa.pointer_type();
	let call_conv = isa.default_call_conv();

	let mut fn_builder_ctx = FunctionBuilderContext::new();
	let mut module = Module::new();
	let mut finished_functions = <PrimaryMap<DefinedFuncIndex, *const VMFunctionBody>>::new();
	let mut code_memory = CodeMemory::new();

	for function in host_functions {
		let sig = translate_signature(
			cranelift_ir_signature(function.signature(), &call_conv),
			pointer_type,
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
		)?;
		finished_functions.push(trampoline);
	}

	for MissingFunction { name, sig } in missing_functions_stubs {
		let sig = translate_signature(
			sig,
			pointer_type,
		);
		let sig_id = module.signatures.push(sig.clone());
		let func_id = module.functions.push(sig_id);
		module
			.exports
			.insert(name, wasmtime_environ::Export::Function(func_id));
		let trampoline = make_trampoline(
			isa.as_ref(),
			&mut code_memory,
			&mut fn_builder_ctx,
			func_id.index() as u32,
			&sig,
		)?;
		finished_functions.push(trampoline);
	}

	code_memory.publish();

	let memory_id = if add_memory {
		let memory = cranelift_wasm::Memory {
			minimum: heap_pages + INITIAL_HEAP_PAGES,
			maximum: Some(heap_pages + INITIAL_HEAP_PAGES),
			shared: false,
		};
		let memory_plan = wasmtime_environ::MemoryPlan::for_memory(memory, &Default::default());

		let memory_id = module.memory_plans.push(memory_plan);
		module.exports.insert("memory".into(), wasmtime_environ::Export::Memory(memory_id));

		Some(memory_id)
	} else {
		None
	};

	let imports = Imports::none();
	let data_initializers = Vec::new();
	let signatures = PrimaryMap::new();
	let env_state = EnvState::new(code_memory, compiler, host_functions);

	let result = InstanceHandle::new(
		Rc::new(module),
		global_exports,
		finished_functions.into_boxed_slice(),
		imports,
		&data_initializers,
		signatures.into_boxed_slice(),
		None,
		Box::new(env_state),
	);

	result
		.map_err(|e| WasmError::Other(format!("cannot instantiate env: {}", e)))
		.map(|r| (r, memory_id))
}

/// Build a new TargetIsa for the host machine.
fn target_isa() -> std::result::Result<Box<dyn TargetIsa>, WasmError> {
	let isa_builder = cranelift_native::builder()
		.map_err(|e| WasmError::Other(format!("missing compiler support: {}", e)))?;
	let flag_builder = cranelift_codegen::settings::builder();
	Ok(isa_builder.finish(cranelift_codegen::settings::Flags::new(flag_builder)))
}

fn new_compiler(strategy: CompilationStrategy) -> std::result::Result<Compiler, WasmError> {
	let isa = target_isa()?;
	Ok(Compiler::new(isa, strategy))
}

fn clear_globals(global_exports: &mut HashMap<String, Option<Export>>, is_imported_memory: bool) {
	// When memory is imported, we can not delete the global export.
	if !is_imported_memory {
		global_exports.remove("memory");
	}
	global_exports.remove("__heap_base");
	global_exports.remove("__indirect_function_table");
}

fn grow_memory(instance: &mut InstanceHandle, pages: u32) -> Result<()> {
	// This is safe to wrap in an unsafe block as:
	// - The result of the `lookup_immutable` call is not mutated
	// - The definition pointer is returned by a lookup on a valid instance
	let memory_index = unsafe {
		match instance.lookup_immutable("memory") {
			Some(Export::Memory { definition, vmctx: _, memory: _ }) =>
				instance.memory_index(&*definition),
			_ => return Err(Error::InvalidMemoryReference),
		}
	};
	instance.memory_grow(memory_index, pages)
		.map(|_| ())
		.ok_or_else(|| "requested heap_pages would exceed maximum memory size".into())
}

fn get_env_state(context: &mut Context) -> Result<&mut EnvState> {
	let env_instance = context.get_instance("env")
		.map_err(|err| format!("cannot find \"env\" module: {}", err))?;
	env_instance
		.host_state()
		.downcast_mut::<EnvState>()
		.ok_or_else(|| "cannot get \"env\" module host state".into())
}

fn reset_env_state_and_take_trap(
	context: &mut Context,
	executor_state: Option<FunctionExecutorState>,
) -> Result<Option<Error>>
{
	let env_state = get_env_state(context)?;
	env_state.executor_state = executor_state;
	Ok(env_state.take_trap())
}

fn inject_input_data(
	context: &mut Context,
	instance: &mut InstanceHandle,
	data: &[u8],
	memory_index: MemoryIndex,
) -> Result<(Pointer<u8>, WordSize)> {
	let env_state = get_env_state(context)?;
	let executor_state = env_state.executor_state
		.as_mut()
		.ok_or_else(|| "cannot get \"env\" module executor state")?;

	let memory = get_memory_mut(instance, memory_index)?;

	let data_len = data.len() as WordSize;
	let data_ptr = executor_state.heap().allocate(memory, data_len)?;
	write_memory_from(memory, data_ptr, data)?;
	Ok((data_ptr, data_len))
}

fn get_memory_mut(instance: &mut InstanceHandle, memory_index: MemoryIndex) -> Result<&mut [u8]> {
	match instance.lookup_by_declaration(&wasmtime_environ::Export::Memory(memory_index)) {
		// This is safe to wrap in an unsafe block as:
		// - The definition pointer is returned by a lookup on a valid instance and thus points to
		//   a valid memory definition
		Export::Memory { definition, vmctx: _, memory: _ } => unsafe {
			Ok(std::slice::from_raw_parts_mut(
				(*definition).base,
				(*definition).current_length,
			))
		},
		_ => Err(Error::InvalidMemoryReference),
	}
}

fn get_heap_base(instance: &InstanceHandle) -> Result<u32> {
	// This is safe to wrap in an unsafe block as:
	// - The result of the `lookup_immutable` call is not mutated
	// - The definition pointer is returned by a lookup on a valid instance
	// - The defined value is checked to be an I32, which can be read safely as a u32
	unsafe {
		match instance.lookup_immutable("__heap_base") {
			Some(Export::Global { definition, vmctx: _, global })
				if global.ty == ir::types::I32 =>
				Ok(*(*definition).as_u32()),
			_ => return Err(Error::HeapBaseNotFoundOrInvalid),
		}
	}
}
