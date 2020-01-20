// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::state_holder::StateHolder;
use sc_executor_common::error::WasmError;
use sp_wasm_interface::{Function, Value, ValueType};
use std::any::Any;
use std::rc::Rc;
use wasmtime::{Callable, Extern, ExternType, Func, Module, Store, Trap, Val};

/// Goes over all imports of a module and prepares a vector of `Extern`s that can be used for
/// instantiation of the module. Returns an error if there are imports that cannot be satisfied.
pub fn resolve_imports(
	state_holder: &StateHolder,
	module: &Module,
	host_functions: &[&'static dyn Function],
) -> Result<Vec<Extern>, WasmError> {
	let mut externs = vec![];
	for import_ty in module.imports() {
		if import_ty.module() != "env" {
			return Err(WasmError::Other(format!(
				"host doesn't provide any imports from non-env module: {}:{}",
				import_ty.module(),
				import_ty.name()
			)));
		}

		let host_func = host_functions
			.iter()
			.find(|host_func| host_func.name() == import_ty.name())
			.ok_or_else(|| {
				WasmError::Other(format!(
					"host doesn't provide such function: {}:{}",
					import_ty.module(),
					import_ty.name()
				))
			})?;

		let func_ty = match import_ty.ty() {
			ExternType::Func(func_ty) => func_ty,
			_ => {
				return Err(WasmError::Other(format!(
					"host doesn't provide any non function imports: {}:{}",
					import_ty.module(),
					import_ty.name()
				)));
			}
		};
		if !signature_matches(&func_ty, &wasmtime_func_sig(*host_func)) {
			return Err(WasmError::Other(format!(
				"signature mismatch for: {}:{}",
				import_ty.module(),
				import_ty.name()
			)));
		}

		externs.push(create_host_func_handler(
			*host_func,
			module.store(),
			state_holder.clone(),
		));
	}
	Ok(externs)
}

/// Returns `true` if `lhs` and `rhs` represent the same signature.
fn signature_matches(lhs: &wasmtime::FuncType, rhs: &wasmtime::FuncType) -> bool {
	lhs.params() == rhs.params() && lhs.results() == rhs.results()
}

/// Wraps the given `host_func` as a wasmtime's `Extern` suitable for passing it as an import.
fn create_host_func_handler(
	host_func: &'static dyn Function,
	store: &Store,
	state_holder: StateHolder,
) -> Extern {
	let func_ty = wasmtime_func_sig(host_func);
	let callable = HostFuncHandler::new(state_holder, host_func);
	let func = Func::new(store, func_ty, Rc::new(callable));
	Extern::Func(func)
}

struct HostFuncHandler {
	state_holder: StateHolder,
	host_func: &'static dyn Function,
}

impl HostFuncHandler {
	fn new(state_holder: StateHolder, host_func: &'static dyn Function) -> Self {
		Self {
			state_holder,
			host_func,
		}
	}
}

impl Callable for HostFuncHandler {
	fn call(
		&self,
		wasmtime_params: &[Val],
		wasmtime_results: &mut [Val],
	) -> Result<(), wasmtime::Trap> {
		let unwind_result = self.state_holder.with_context(|mut host_ctx| {
			let mut params = wasmtime_params.iter().cloned().map(into_value);

			std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
				self.host_func.execute(&mut host_ctx, &mut params)
			}))
		});

		let execution_result = match unwind_result {
			Ok(execution_result) => execution_result,
			Err(err) => return Err(Trap::new(stringify_panic_payload(err))),
		};

		match execution_result {
			Ok(Some(ret_val)) => {
				// TODO: Should we check the return type?
				wasmtime_results[0] = into_wasmtime_val(ret_val);
				Ok(())
			}
			Ok(None) => {
				// TODO: Should we check the return type?
				Ok(())
			}
			Err(msg) => Err(Trap::new(msg)),
		}
	}
}

fn wasmtime_func_sig(func: &dyn Function) -> wasmtime::FuncType {
	let params = func
		.signature()
		.args
		.iter()
		.cloned()
		.map(into_wasmtime_val_type)
		.collect::<Vec<_>>()
		.into_boxed_slice();
	let results = func
		.signature()
		.return_value
		.iter()
		.cloned()
		.map(into_wasmtime_val_type)
		.collect::<Vec<_>>()
		.into_boxed_slice();
	wasmtime::FuncType::new(params, results)
}

fn into_wasmtime_val_type(val_ty: ValueType) -> wasmtime::ValType {
	match val_ty {
		ValueType::I32 => wasmtime::ValType::I32,
		ValueType::I64 => wasmtime::ValType::I64,
		ValueType::F32 => wasmtime::ValType::F32,
		ValueType::F64 => wasmtime::ValType::F64,
	}
}

fn into_value(val: Val) -> Value {
	match val {
		Val::I32(v) => Value::I32(v),
		Val::I64(v) => Value::I64(v),
		Val::F32(f_bits) => Value::F32(f_bits),
		Val::F64(f_bits) => Value::F64(f_bits),
		_ => todo!(), // TODO:
	}
}

fn into_wasmtime_val(value: Value) -> wasmtime::Val {
	match value {
		Value::I32(v) => Val::I32(v),
		Value::I64(v) => Val::I64(v),
		Value::F32(f_bits) => Val::F32(f_bits),
		Value::F64(f_bits) => Val::F64(f_bits),
	}
}

/// Attempt to convert a opaque panic payload to a string.
fn stringify_panic_payload(payload: Box<dyn Any + Send + 'static>) -> String {
	match payload.downcast::<&'static str>() {
		Ok(msg) => msg.to_string(),
		Err(payload) => match payload.downcast::<String>() {
			Ok(msg) => *msg,
			// At least we tried...
			Err(_) => "Box<Any>".to_string(),
		},
	}
}
