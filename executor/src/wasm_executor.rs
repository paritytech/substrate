// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Rust implementation of Polkadot contracts.

use parity_wasm;

use primitives::contract::{CallData, OutData};
//use serializer::{from_slice as de, to_vec as ser};
use state_machine::{Externalities, CodeExecutor};

use error::{Error, ErrorKind, Result};

pub trait ConvertibleToWasm { const VALUE_TYPE: parity_wasm::elements::ValueType; }
impl ConvertibleToWasm for i32 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }
impl ConvertibleToWasm for u32 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }
impl ConvertibleToWasm for i64 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I64; }
impl ConvertibleToWasm for u64 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I64; }
impl ConvertibleToWasm for f32 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::F32; }
impl ConvertibleToWasm for f64 { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::F64; }
impl ConvertibleToWasm for isize { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }
impl ConvertibleToWasm for usize { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }
impl<T> ConvertibleToWasm for *const T { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }
impl<T> ConvertibleToWasm for *mut T { const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; }

#[macro_export]
macro_rules! convert_args {
    () => ([]);
    ( $( $t:ty ),* ) => ( [ $( <$t> :: VALUE_TYPE, )* ] );
}

#[macro_export]
macro_rules! convert_fn {
    ( $name:ident ( $($params:tt)* ) ) => ( UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params)*), None) );
    ( $name:ident ( $( $params:ty ),* ) -> $returns:ty ) => ( UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), Some(<$returns>::VALUE_TYPE) ) );
}

/// Dummy rust executor for contracts.
///
/// Instead of actually executing the provided code it just
/// dispatches the calls to pre-defined hardcoded implementations in rust.
#[derive(Debug, Default)]
pub struct WasmExecutor {
}

impl CodeExecutor for WasmExecutor {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		method: &str,
		data: &CallData,
	) -> Result<OutData> {

		// TODO: avoid copying code by requiring code to remain immutable through execution,
		// splitting it off from potentially mutable externalities.
		let code = match ext.code() {
			Ok(e) => e.to_owned(),
			Err(e) => Err(ErrorKind::Externalities(Box::new(e)))?,
		};

		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};
		let program = parity_wasm::ProgramInstance::new();
		let module = parity_wasm::deserialize_buffer(code).expect("Failed to load module");
		let module = program.add_module("main", module, None).expect("Failed to initialize module");
		module.execute_export(method, vec![I64(data.0.len() as i64)].into())
			.map(|o| OutData(vec![1; if let Some(I64(l)) = o { l as usize } else { 0 }]))
			.map_err(|_| ErrorKind::Runtime.into())
	}
}

#[cfg(test)]
mod tests {

	use super::*;
	use std::collections::HashMap;
	use state_machine::StaticExternalities;

	#[derive(Debug, Default)]
	struct TestExternalities;
	impl Externalities for TestExternalities {
		fn set_code(&mut self, _code: Vec<u8>) {
			unimplemented!()
		}

		fn set_storage(&mut self, _object: u64, _key: Vec<u8>, _value: Vec<u8>) {
			unimplemented!()
		}
	}

	impl StaticExternalities for TestExternalities {
		type Error = Error;

		fn code(&self) -> Result<&[u8]> {
			unimplemented!()
		}

		fn storage(&self, _object: u64, _key: &[u8]) -> Result<&[u8]> {
			unimplemented!()
		}
	}

	use std::result;
	use std::sync::{Arc, Weak};
	use parity_wasm::interpreter::{CallerContext};
	use parity_wasm::interpreter::{UserDefinedElements, UserFunctionExecutor, UserFunctionDescriptor};
	use parity_wasm::interpreter::{RuntimeValue};

	// user function executor
	struct FunctionExecutor;

	fn imported(n: u64) {
		println!("imported {:?}", n);
	}

//	marshalled!(imported)

	impl UserFunctionExecutor for FunctionExecutor {
		fn execute(&mut self, name: &str, context: CallerContext) -> result::Result<Option<RuntimeValue>, parity_wasm::interpreter::Error> {
			match name {
				"imported" => {
					let n = context.value_stack.pop_as()?;
					imported(n);
					Ok(None)
				}
				_ => Err(parity_wasm::interpreter::Error::Trap(format!("not implemented: {}", name)).into())
			}
		}
	}

	const SIGNATURES: &'static [UserFunctionDescriptor] = &[
		convert_fn!(imported(u64)),
		convert_fn!(ext_memcpy(*mut u8, *const u8, usize) -> *mut u8),
		convert_fn!(ext_memmove(*mut u8, *const u8, usize) -> *mut u8),
		convert_fn!(ext_memset(*mut u8, i32, usize) -> *mut u8),
		convert_fn!(ext_malloc(usize) -> *mut u8),
		convert_fn!(ext_free(*mut u8)),
	];

	fn program_with_externals<E: UserFunctionExecutor + 'static>(externals: UserDefinedElements<E>, module_name: &str) -> result::Result<parity_wasm::ProgramInstance, parity_wasm::interpreter::Error> {
		let program = parity_wasm::ProgramInstance::new();
		let instance = {
			let module = parity_wasm::builder::module().build();
			let mut instance = parity_wasm::ModuleInstance::new(Weak::default(), module_name.into(), module)?;
			instance.instantiate(None)?;
			instance
		};
		let other_instance = parity_wasm::interpreter::native_module(Arc::new(instance), externals)?;
		program.insert_loaded_module(module_name, other_instance)?;
		Ok(program)
	}

	#[test]
	fn should_provide_externalities() {
		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};

		let externals = UserDefinedElements {
			executor: Some(FunctionExecutor{}),
			globals: HashMap::new(),
			functions: ::std::borrow::Cow::from(SIGNATURES),
		};

		let program = program_with_externals(externals, "env").unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.wasm");
		let module_code = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module_code, None).expect("Failed to initialize module");

//		module.exports.push_function("add", &[ValueType::I64, ValueType::I64], Some(ValueType::I64), marshall!(|a: u64, b: u64| a + b));

		let argument: u64 = 42;
		assert_eq!(Some(I64((argument * 2) as i64)), module.execute_export("test", vec![I64(argument as i64)].into()).unwrap());
	}

	#[test]
	fn should_run_wasm() {
		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};

		let program = parity_wasm::ProgramInstance::new();
		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");
		let argument: i64 = 42;
		assert_eq!(Some(I64(argument * 2)), module.execute_export("test", vec![I64(argument)].into()).unwrap());
	}
}
