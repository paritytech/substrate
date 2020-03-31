use crate::state_holder;
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
		name: String,
	},
}

pub struct Imports {
	memory_descriptor: Option<MemoryDescriptor>,
	namespaces: HashMap<String, HashMap<String, Export>>,
	_call_ctx_vec: Vec<Box<CallCtx>>,
	_dynamic_funcs: Vec<Box<DynamicFunc<'static>>>,
	_trampoline_bufs: Vec<TrampolineBuffer>,
}

impl Imports {
	pub fn materialize(&self) -> (ImportObject, Option<Memory>) {
		let mut import_object = ImportObject::new();
		let mut imported_memory = None;

		let mut namespaces = self.namespaces.clone();
		if let Some(ref memory_desc) = self.memory_descriptor {
			// there is a memory descriptor for the imported memory. That means we need to create
			// a memory instance and register it under "env:memory".
			let memory = Memory::new(memory_desc.clone()).unwrap();

			namespaces
				.entry("env".to_string())
				.or_insert_with(HashMap::new)
				.insert("memory".to_string(), Export::Memory(memory.clone()));

			imported_memory = Some(memory);
		}

		// register the namespaces into the import object.
		for (module_name, namespace_members) in namespaces {
			let mut namespace = Namespace::new();
			for (name, member) in namespace_members {
				namespace.insert(name, member);
			}
			import_object.register(module_name, namespace);
		}

		(import_object, imported_memory)
	}
}

pub fn resolve_imports(
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

	let mut namespaces = HashMap::new();
	let mut call_ctx_vec = Vec::new();
	let mut trampoline_bufs = Vec::new();
	let mut dynamic_funcs = Vec::new();
	let mut memory_descriptor = None;
	for import in imports {
		if import.module() != "env" {
			todo!();
		}

		let namespace = namespaces
			.entry(import.module().to_string())
			.or_insert_with(HashMap::new);

		let export = match import.field() {
			"memory" => {
				let resolved_memory_desc = resolve_memory_import(import, heap_pages);
				memory_descriptor = Some(resolved_memory_desc);
				continue;
			}
			_ => resolve_func_import(
				types,
				import,
				host_functions,
				allow_missing_func_imports,
				&mut call_ctx_vec,
				&mut dynamic_funcs,
				&mut trampoline_bufs,
			),
		};
		namespace.insert(import.field().to_string(), export);
	}

	Imports {
		namespaces,
		_call_ctx_vec: call_ctx_vec,
		_trampoline_bufs: trampoline_bufs,
		_dynamic_funcs: dynamic_funcs,
		memory_descriptor,
	}
}

fn resolve_memory_import(import: &ImportEntry, heap_pages: u32) -> MemoryDescriptor {
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

	MemoryDescriptor::new(
		Pages(initial),
		requested_memory_ty.limits().maximum().map(Pages),
		false,
	)
	.unwrap()
}

fn resolve_func_import(
	types: &[Type],
	import: &ImportEntry,
	host_functions: &[&'static dyn Function],
	allow_missing_func_imports: bool,
	call_ctx_vec: &mut Vec<Box<CallCtx>>,
	dynamic_funcs: &mut Vec<Box<DynamicFunc<'static>>>,
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
			name: format!("{}!{}", import.module(), import.field()), // TODO: We can use `host_func.name()` here.
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

	let boxed_func = Box::new(DynamicFunc::new(
		Arc::new(FuncSig::new(params, returns)),
		move |ctx, args| -> Vec<wasmer_runtime_core::types::Value> {
			let call_ctx = unsafe { &*call_ctx_ptr };
			let host_func = match call_ctx {
				CallCtx::Missing => panic!("calling missing function"),
				CallCtx::Resolved {
					ref host_func,
					..
				} => host_func,
			};

			let num_params = host_func.signature().args.len();
			let args = args.iter().cloned().map(from_wasmer_val);

			let execution_result = state_holder::with_context(|host_ctx| {
				let mut host_ctx = host_ctx.unwrap();
				host_func.execute(&mut host_ctx, &mut args.into_iter())
			});

			match execution_result {
				Ok(Some(ret_val)) => {
					vec![into_wasmer_val(ret_val)]
				}
				Ok(None) => vec![],
				Err(_msg) => panic!("host function returned an error"),
			}
		},
	));
	let export = boxed_func.to_export();
	dynamic_funcs.push(boxed_func);
	export
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
