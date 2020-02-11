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

//! The trampoline is the dynamically generated entry point to a runtime host call.
//!
//! This code is based on and large parts are copied from wasmtime's
//! wasmtime-api/src/trampoline/func.rs.

use crate::function_executor::{FunctionExecutorState, FunctionExecutor};
use sc_executor_common::error::{Error, WasmError};

use cranelift_codegen::{Context, binemit, ir, isa};
use cranelift_codegen::ir::{InstBuilder, StackSlotData, StackSlotKind, TrapCode};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_codegen::print_errors::pretty_error;
use wasmtime_jit::{CodeMemory, Compiler};
use wasmtime_environ::CompiledFunction;
use wasmtime_runtime::{VMContext, VMFunctionBody};
use sp_wasm_interface::{Function, Value, ValueType};
use std::{cmp, panic::{self, AssertUnwindSafe}, ptr};

const CALL_SUCCESS: u32 = 0;
const CALL_FAILED_WITH_ERROR: u32 = 1;
const CALL_WITH_BAD_HOST_STATE: u32 = 2;

/// A code to trap with that indicates a host call error.
const TRAP_USER_CODE: u16 = 0;

/// The only Wasm types allowed in host function signatures (I32, I64, F32, F64) are all
/// represented in at most 8 bytes.
const MAX_WASM_TYPE_SIZE: usize = 8;

/// The top-level host state of the "env" module. This state is used by the trampoline function to
/// construct a `FunctionExecutor` which can execute the host call.
pub struct EnvState {
	host_functions: Vec<&'static dyn Function>,
	compiler: Compiler,
	// The code memory must be kept around on the state to prevent it from being dropped.
	#[allow(dead_code)]
	code_memory: CodeMemory,
	trap: Option<Error>,
	/// The executor state stored across host calls during a single Wasm runtime call.
	/// During a runtime call, this MUST be `Some`.
	pub executor_state: Option<FunctionExecutorState>,
}

impl EnvState {
	/// Construct a new `EnvState` which owns the given code memory.
	pub fn new(
		code_memory: CodeMemory,
		compiler: Compiler,
		host_functions: &[&'static dyn Function],
	) -> Self {
		EnvState {
			trap: None,
			compiler,
			code_memory,
			executor_state: None,
			host_functions: host_functions.to_vec(),
		}
	}

	/// Resets the trap error to None and returns the current value.
	pub fn take_trap(&mut self) -> Option<Error> {
		self.trap.take()
	}
}

/// This is called by the dynamically generated trampoline taking the function index and reference
/// to the call arguments on the stack as arguments. Returns zero on success and a non-zero value
/// on failure.
unsafe extern "C" fn stub_fn(vmctx: *mut VMContext, func_index: u32, values_vec: *mut i64) -> u32 {
	if let Some(state) = (*vmctx).host_state().downcast_mut::<EnvState>() {
			match stub_fn_inner(
				vmctx,
				&state.host_functions,
				&mut state.compiler,
				state.executor_state.as_mut(),
				func_index,
				values_vec,
			) {
				Ok(()) => CALL_SUCCESS,
				Err(err) => {
					state.trap = Some(err);
					CALL_FAILED_WITH_ERROR
				}
			}
	} else {
		// Well, we can't even set a trap message, so we'll just exit without one.
		CALL_WITH_BAD_HOST_STATE
	}
}

/// Implements most of the logic in `stub_fn` but returning a `Result` instead of an integer error
/// for the sake of readability.
unsafe fn stub_fn_inner(
	vmctx: *mut VMContext,
	externals: &[&dyn Function],
	compiler: &mut Compiler,
	executor_state: Option<&mut FunctionExecutorState>,
	func_index: u32,
	values_vec: *mut i64,
) -> Result<(), Error> {
	let func = externals.get(func_index as usize)
		.ok_or_else(|| format!("call to undefined external function with index {}", func_index))?;
	let executor_state = executor_state
		.ok_or_else(|| "executor state is None during call to external function")?;

	// Build the external function context.
	let mut context = FunctionExecutor::new(vmctx, compiler, executor_state)?;
	let mut context = AssertUnwindSafe(&mut context);

	// Execute and write output back to the stack.
	let return_val = panic::catch_unwind(move || {
		let signature = func.signature();

		// Read the arguments from the stack.
		let mut args = signature.args.iter()
			.enumerate()
			.map(|(i, &param_type)| read_value_from(values_vec.offset(i as isize), param_type));

		func.execute(&mut **context, &mut args)
	});

	match return_val {
		Ok(ret_val) => {
			if let Some(val) = ret_val
				.map_err(|e| Error::FunctionExecution(func.name().to_string(), e))? {
				write_value_to(values_vec, val);
			}

			Ok(())
		},
		Err(e) => {
			let message = if let Some(err) = e.downcast_ref::<String>() {
				err.to_string()
			} else if let Some(err) = e.downcast_ref::<&str>() {
				err.to_string()
			} else {
				"Panicked without any further information!".into()
			};

			Err(Error::FunctionExecution(func.name().to_string(), message))
		}
	}
}

/// Create a trampoline for invoking a host function.
///
/// The trampoline is a dynamically generated entry point to a runtime host call. The function is
/// generated by manually constructing Cranelift IR and using the Cranelift compiler. The
/// trampoline embeds the function index as a constant and delegates to a stub function in Rust,
/// which takes the function index and a memory reference to the stack arguments and return value
/// slots.
///
/// This code is of modified copy of wasmtime's wasmtime-api/src/trampoline/func.rs.
pub fn make_trampoline(
	isa: &dyn isa::TargetIsa,
	code_memory: &mut CodeMemory,
	fn_builder_ctx: &mut FunctionBuilderContext,
	func_index: u32,
	signature: &ir::Signature,
) -> Result<*const VMFunctionBody, WasmError> {
	// Mostly reverse copy of the similar method from wasmtime's
	// wasmtime-jit/src/compiler.rs.
	let pointer_type = isa.pointer_type();
	let mut stub_sig = ir::Signature::new(isa.frontend_config().default_call_conv);

	// Ensure that the first parameter of the generated function is the `VMContext` pointer.
	assert_eq!(
		signature.params[0],
		ir::AbiParam::special(pointer_type, ir::ArgumentPurpose::VMContext)
	);

	// Add the `vmctx` parameter.
	stub_sig.params.push(ir::AbiParam::special(
		pointer_type,
		ir::ArgumentPurpose::VMContext,
	));

	// Add the `func_index` parameter.
	stub_sig.params.push(ir::AbiParam::new(ir::types::I32));

	// Add the `values_vec` parameter.
	stub_sig.params.push(ir::AbiParam::new(pointer_type));

	// Add error/trap return.
	stub_sig.returns.push(ir::AbiParam::new(ir::types::I32));

	// Each parameter and return value gets a 64-bit (8-byte) wide slot on the stack, as that is
	// large enough to fit all Wasm primitive types that can be used in host function signatures.
	// The `VMContext` pointer, which is a parameter of the function signature, is excluded as it
	// is passed directly to the stub function rather than being looked up on the caller stack from
	// the `values_vec` pointer.
	let values_vec_len = cmp::max(signature.params.len() - 1, signature.returns.len());
	let values_vec_size = (MAX_WASM_TYPE_SIZE * values_vec_len) as u32;

	let mut context = Context::new();
	context.func =
		ir::Function::with_name_signature(ir::ExternalName::user(0, 0), signature.clone());

	let ss = context.func.create_stack_slot(StackSlotData::new(
		StackSlotKind::ExplicitSlot,
		values_vec_size,
	));

	{
		let mut builder = FunctionBuilder::new(&mut context.func, fn_builder_ctx);
		let block0 = builder.create_ebb();

		builder.append_ebb_params_for_function_params(block0);
		builder.switch_to_block(block0);
		builder.seal_block(block0);

		let values_vec_ptr_val = builder.ins().stack_addr(pointer_type, ss, 0);
		let mflags = ir::MemFlags::trusted();
		for i in 1..signature.params.len() {
			let val = builder.func.dfg.ebb_params(block0)[i];
			builder.ins().store(
				mflags,
				val,
				values_vec_ptr_val,
				((i - 1) * MAX_WASM_TYPE_SIZE) as i32,
			);
		}

		let vmctx_ptr_val = builder.func.dfg.ebb_params(block0)[0];
		let func_index_val = builder.ins().iconst(ir::types::I32, func_index as i64);

		let callee_args = vec![vmctx_ptr_val, func_index_val, values_vec_ptr_val];

		let new_sig = builder.import_signature(stub_sig.clone());

		let callee_value = builder
			.ins()
			.iconst(pointer_type, stub_fn as *const VMFunctionBody as i64);
		let call = builder
			.ins()
			.call_indirect(new_sig, callee_value, &callee_args);

		let call_result = builder.func.dfg.inst_results(call)[0];
		builder.ins().trapnz(call_result, TrapCode::User(TRAP_USER_CODE));

		let mflags = ir::MemFlags::trusted();
		let mut results = Vec::new();
		for (i, r) in signature.returns.iter().enumerate() {
			let load = builder.ins().load(
				r.value_type,
				mflags,
				values_vec_ptr_val,
				(i * MAX_WASM_TYPE_SIZE) as i32,
			);
			results.push(load);
		}
		builder.ins().return_(&results);
		builder.finalize()
	}

	let mut code_buf: Vec<u8> = Vec::new();
	let mut reloc_sink = RelocSink;
	let mut trap_sink = binemit::NullTrapSink {};
	let mut stackmap_sink = binemit::NullStackmapSink {};
	context
		.compile_and_emit(
			isa,
			&mut code_buf,
			&mut reloc_sink,
			&mut trap_sink,
			&mut stackmap_sink,
		)
		.map_err(|e| {
			WasmError::Instantiation(format!(
				"failed to compile trampoline: {}",
				pretty_error(&context.func, Some(isa), e)
			))
		})?;

	let mut unwind_info = Vec::new();
	context.emit_unwind_info(isa, &mut unwind_info);

	let func_ref = code_memory
		.allocate_for_function(&CompiledFunction {
			body: code_buf,
			jt_offsets: context.func.jt_offsets,
			unwind_info,
		})
		.map_err(|e| WasmError::Instantiation(format!("failed to allocate code memory: {}", e)))?;

	Ok(func_ref.as_ptr())
}

/// We don't expect trampoline compilation to produce any relocations, so
/// this `RelocSink` just asserts that it doesn't recieve any.
struct RelocSink;

impl binemit::RelocSink for RelocSink {
	fn reloc_ebb(
		&mut self,
		_offset: binemit::CodeOffset,
		_reloc: binemit::Reloc,
		_ebb_offset: binemit::CodeOffset,
	) {
		panic!("trampoline compilation should not produce ebb relocs");
	}
	fn reloc_external(
		&mut self,
		_offset: binemit::CodeOffset,
		_reloc: binemit::Reloc,
		_name: &ir::ExternalName,
		_addend: binemit::Addend,
	) {
		panic!("trampoline compilation should not produce external symbol relocs");
	}
	fn reloc_constant(
		&mut self,
		_code_offset: binemit::CodeOffset,
		_reloc: binemit::Reloc,
		_constant_offset: ir::ConstantOffset,
	) {
		panic!("trampoline compilation should not produce constant relocs");
	}
	fn reloc_jt(
		&mut self,
		_offset: binemit::CodeOffset,
		_reloc: binemit::Reloc,
		_jt: ir::JumpTable,
	) {
		panic!("trampoline compilation should not produce jump table relocs");
	}
}

unsafe fn write_value_to(p: *mut i64, val: Value) {
	match val {
		Value::I32(i) => ptr::write(p as *mut i32, i),
		Value::I64(i) => ptr::write(p as *mut i64, i),
		Value::F32(u) => ptr::write(p as *mut u32, u),
		Value::F64(u) => ptr::write(p as *mut u64, u),
	}
}

unsafe fn read_value_from(p: *const i64, ty: ValueType) -> Value {
	match ty {
		ValueType::I32 => Value::I32(ptr::read(p as *const i32)),
		ValueType::I64 => Value::I64(ptr::read(p as *const i64)),
		ValueType::F32 => Value::F32(ptr::read(p as *const u32)),
		ValueType::F64 => Value::F64(ptr::read(p as *const u64)),
	}
}
