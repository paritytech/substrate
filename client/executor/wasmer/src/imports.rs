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
	import::{ImportObject, IsExport, Namespace},
	memory::Memory,
	typed_func::DynamicFunc,
	types::{FuncSig, MemoryDescriptor},
	units::Pages,
};

enum CallCtx {
	Missing,
	Resolved {
		host_func: &'static dyn Function,
		state_holder: StateHolder,
		name: String,
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
			name: format!("{}!{}", import.module(), import.field()),
		},
		None => CallCtx::Missing, // TODO: check allow_missing
	};

	// Wrap call_ctx to get a stable address.
	let call_ctx = Box::new(call_ctx);
	let call_ctx_ptr = call_ctx.as_ref() as *const CallCtx;
	call_ctx_vec.push(call_ctx);

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

	DynamicFunc::new(
		Arc::new(FuncSig::new(params, returns)),
		move |ctx, args| -> Vec<wasmer_runtime_core::types::Value> {
			dbg!();
			vec![]
		},
	)
	.to_export()
}

fn from_wasmer_val(val: wasmer_runtime_core::types::Value) -> Value {
	match val {
		wasmer_runtime_core::types::Value::I32(v) => Value::I32(v),
		wasmer_runtime_core::types::Value::I64(v) => Value::I64(v),
		wasmer_runtime_core::types::Value::F32(v) => Value::F32(f32::to_bits(v)),
		wasmer_runtime_core::types::Value::F64(v) => Value::F64(f64::to_bits(v)),
		_ => panic!(),
	}
}

fn into_wasmer_val(val: Value) -> wasmer_runtime_core::types::Value {
	match val {
		Value::I32(v) => wasmer_runtime_core::types::Value::I32(v),
		Value::I64(v) => wasmer_runtime_core::types::Value::I64(v),
		Value::F32(v) => wasmer_runtime_core::types::Value::F32(f32::from_bits(v)),
		Value::F64(v) => wasmer_runtime_core::types::Value::F64(f64::from_bits(v)),
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

/// Attempt to convert a opaque panic payload to a string.
fn stringify_panic_payload(payload: Box<dyn std::any::Any + Send + 'static>) -> String {
	match payload.downcast::<&'static str>() {
		Ok(msg) => msg.to_string(),
		Err(payload) => match payload.downcast::<String>() {
			Ok(msg) => *msg,
			// At least we tried...
			Err(_) => "Box<Any>".to_string(),
		},
	}
}
