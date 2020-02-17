use crate::state_holder::StateHolder;
use parity_wasm::elements::{deserialize_buffer, External, ImportEntry, Module, Type};
use sp_wasm_interface::{Function, Value, ValueType};
use std::collections::HashMap;
use std::sync::Arc;
use wasmer_runtime_core::trampoline::{
	CallContext as OpaqueCallContext, TrampolineBuffer, TrampolineBufferBuilder,
};
use wasmer_runtime_core::{
	export::{Context, Export, FuncPointer},
	import::{ImportObject, Namespace},
	memory::Memory,
	types::{FuncSig, MemoryDescriptor},
	units::Pages,
};

enum CallCtx {
	Missing,
	Resolved {
		host_func: &'static dyn Function,
		state_holder: StateHolder,
	},
}

pub struct Imports {
	pub import_object: ImportObject,
	pub memory: Option<Memory>,
	_call_ctx_vec: Vec<Box<CallCtx>>,
	_trampoline_bufs: Vec<TrampolineBuffer>,
}

pub fn resolve_imports(
	state_holder: &StateHolder,
	host_functions: &[&'static dyn Function],
	wasm_bytes: &[u8],
	allow_missing_func_imports: bool,
	heap_pages: u32,
) -> Imports {
	let module: Module = deserialize_buffer(wasm_bytes).unwrap();
	let imports = module
		.import_section()
		.map(|is| is.entries())
		.unwrap_or(&[]);
	let types = module.type_section().map(|ts| ts.types()).unwrap_or(&[]);

	let mut import_object = ImportObject::new();
	let mut namespaces = HashMap::new();
	let mut call_ctx_vec = Vec::new();
	let mut trampoline_bufs = Vec::new();
	let mut memory = None;
	for import in imports {
		if import.module() != "env" {
			todo!();
		}

		let namespace = namespaces
			.entry(import.module())
			.or_insert_with(Namespace::new);

		let export = match import.field() {
			"memory" => {
				let resolved_memory = resolve_memory_import(import, heap_pages);
				memory = Some(resolved_memory.clone());
				Export::Memory(resolved_memory)
			}
			_ => resolve_func_import(
				types,
				import,
				state_holder,
				host_functions,
				allow_missing_func_imports,
				&mut call_ctx_vec,
				&mut trampoline_bufs,
			),
		};
		namespace.insert(import.field().to_string(), export);
	}

	for (module_name, namespace) in namespaces.into_iter() {
		import_object.register(module_name, namespace);
	}

	Imports {
		import_object,
		_call_ctx_vec: call_ctx_vec,
		_trampoline_bufs: trampoline_bufs,
		memory,
	}
}

fn resolve_memory_import(import: &ImportEntry, heap_pages: u32) -> Memory {
	let requested_memory_ty = match import.external() {
		External::Memory(memory_ty) => memory_ty,
		_ => todo!(),
	};

	let initial = requested_memory_ty.limits().initial() + heap_pages;
	if let Some(max) = requested_memory_ty.limits().maximum() {
		if initial > max {
			todo!();
		}
	}

	let descriptor = MemoryDescriptor::new(
		Pages(initial),
		requested_memory_ty.limits().maximum().map(Pages),
		false,
	)
	.unwrap();
	Memory::new(descriptor).unwrap()
}

unsafe extern "C" fn stub(ctx: *const OpaqueCallContext, raw_args: *const u64) -> u64 {
	let ctx = ctx as *const CallCtx;
	let (host_func, state_holder) = match *ctx {
		CallCtx::Missing => return 0,
		CallCtx::Resolved {
			ref host_func,
			ref state_holder,
		} => (host_func, state_holder),
	};

	let num_params = host_func.signature().args.len();
	let mut args = Vec::with_capacity(num_params);

	host_func
		.signature()
		.args
		.iter()
		.enumerate()
		.for_each(|(idx, arg_ty)| {
			// Ignore the implicit context argument.
			let idx = idx + 1;
			let arg_val = match arg_ty {
				ValueType::I32 => Value::I32(*raw_args.offset(idx as isize) as u32 as i32),
				ValueType::I64 => Value::I64(*raw_args.offset(idx as isize) as u64 as i64),
				ValueType::F32 => Value::F32((*raw_args.offset(idx as isize) as f32).to_bits()),
				ValueType::F64 => Value::F64((*raw_args.offset(idx as isize) as f64).to_bits()),
			};
			args.push(arg_val);
		});

	let unwind_result = state_holder.with_context(|host_ctx| {
		let mut host_ctx = host_ctx.unwrap();
		std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			host_func.execute(&mut host_ctx, &mut args.into_iter())
		}))
	});

	// TODO: How to Trap?
	let execution_result = match unwind_result {
		Ok(execution_result) => execution_result,
		Err(_err) => return 0,
	};

	match execution_result {
		Ok(Some(ret_val)) => {
			let raw_args = raw_args as *mut u64;
			match ret_val {
				Value::I32(v) => raw_args.write(v as u32 as u64),
				Value::I64(v) => raw_args.write(v as u64),
				Value::F32(v) => raw_args.write(v as u64),
				Value::F64(v) => raw_args.write(v),
			}
			1
		}
		Ok(None) => 1,
		Err(_msg) => 0,
	}
}

fn resolve_func_import(
	types: &[Type],
	import: &ImportEntry,
	state_holder: &StateHolder,
	host_functions: &[&'static dyn Function],
	allow_missing_func_imports: bool,
	call_ctx_vec: &mut Vec<Box<CallCtx>>,
	trampoline_bufs: &mut Vec<TrampolineBuffer>,
) -> Export {
	let func_ty = match import.external() {
		External::Function(type_idx) => {
			let Type::Function(ref func_ty) = types[*type_idx as usize];
			func_ty
		}
		_ => {
			todo!();
		}
	};

	let call_ctx = match host_functions
		.iter()
		.find(|host_func| host_func.name() == import.field())
	{
		Some(host_func) => CallCtx::Resolved {
			host_func: *host_func,
			state_holder: state_holder.clone(),
		},
		None => CallCtx::Missing, // TODO: check allow_missing
	};

	// Wrap call_ctx to get a stable address.
	let call_ctx = Box::new(call_ctx);
	let call_ctx_ptr = call_ctx.as_ref() as *const CallCtx;
	call_ctx_vec.push(call_ctx);

	// It seems that the arguments that the stub gets has 1 implicit argument.
	let num_params = func_ty.params().len() + 1;

	let mut tbb = TrampolineBufferBuilder::new();
	let idx = tbb.add_callinfo_trampoline(
		stub,
		call_ctx_ptr as *const OpaqueCallContext,
		num_params as u32,
	);
	let buf = tbb.build();
	let trampoline_ptr = buf.get_trampoline(idx);
	trampoline_bufs.push(buf);

	let params = func_ty
		.params()
		.iter()
		.cloned()
		.map(into_wasmer_ty)
		.collect::<Vec<_>>();
	let returns = func_ty
		.return_type()
		.iter()
		.cloned()
		.map(into_wasmer_ty)
		.collect::<Vec<_>>();

	Export::Function {
		func: unsafe { FuncPointer::new(trampoline_ptr as _) },
		ctx: Context::Internal,
		signature: Arc::new(FuncSig::new(params, returns)),
	}
}

fn into_wasmer_ty(value_ty: parity_wasm::elements::ValueType) -> wasmer_runtime_core::types::Type {
	match value_ty {
		parity_wasm::elements::ValueType::I32 => wasmer_runtime_core::types::Type::I32,
		parity_wasm::elements::ValueType::I64 => wasmer_runtime_core::types::Type::I64,
		parity_wasm::elements::ValueType::F32 => wasmer_runtime_core::types::Type::F32,
		parity_wasm::elements::ValueType::F64 => wasmer_runtime_core::types::Type::F64,
	}
}
