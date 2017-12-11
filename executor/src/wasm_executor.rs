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

use std::sync::{Weak};

fn program_with_externals<E: parity_wasm::interpreter::UserFunctionExecutor + 'static>(externals: parity_wasm::interpreter::UserDefinedElements<E>, module_name: &str) -> result::Result<parity_wasm::ProgramInstance, parity_wasm::interpreter::Error> {
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

pub trait ConvertibleToWasm { const VALUE_TYPE: parity_wasm::elements::ValueType; type NativeType; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue; }
impl ConvertibleToWasm for i32 { type NativeType = i32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self) } }
impl ConvertibleToWasm for u32 { type NativeType = u32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for i64 { type NativeType = i64; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I64; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I64(self) } }
impl ConvertibleToWasm for u64 { type NativeType = u64; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I64; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I64(self as i64) } }
impl ConvertibleToWasm for f32 { type NativeType = f32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::F32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::F32(self) } }
impl ConvertibleToWasm for f64 { type NativeType = f64; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::F64; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::F64(self) } }
impl ConvertibleToWasm for isize { type NativeType = i32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for usize { type NativeType = u32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self as u32 as i32) } }
impl<T> ConvertibleToWasm for *const T { type NativeType = u32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self as isize as i32) } }
impl<T> ConvertibleToWasm for *mut T { type NativeType = u32; const VALUE_TYPE: parity_wasm::elements::ValueType = parity_wasm::elements::ValueType::I32; fn to_runtime_value(self) -> parity_wasm::interpreter::RuntimeValue { parity_wasm::interpreter::RuntimeValue::I32(self as isize as i32) } }

#[macro_export]
macro_rules! convert_args {
	() => ([]);
	( $( $t:ty ),* ) => ( [ $( <$t> :: VALUE_TYPE, )* ] );
}

#[macro_export]
macro_rules! convert_fn {
	( $name:ident ( $( $params:ty ),* ) ) => ( parity_wasm::interpreter::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), None) );
	( $name:ident ( $( $params:ty ),* ) -> $returns:ty ) => ( parity_wasm::interpreter::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), Some(<$returns>::VALUE_TYPE) ) );
}

#[macro_export]
macro_rules! reverse_params {
	// Entry point, use brackets to recursively reverse above.
	($body:tt, $self:ident, $context:ident, $( $names:ident : $params:ty ),*) => (
		reverse_params!($body $self $context [ $( $names : $params ),* ]);
	);
	($body:tt $self:ident $context:ident [] $( $names:ident : $params:ty ),*) => ({
		$(
			let $names : <$params as ConvertibleToWasm>::NativeType = match $context.value_stack.pop_as() {
				Ok(value) => value,
				Err(error) => return Err(error.into()),
			};
		)*
		$body
	});
	($body:tt $self:ident $context:ident [ $name:ident : $param:ty $(, $names:ident : $params:ty )* ] $( $reversed_names:ident : $reversed_params:ty ),*) => (
		reverse_params!($body $self $context [ $( $names : $params ),* ] $name : $param $( , $reversed_names : $reversed_params )*);
	);
}

#[macro_export]
macro_rules! marshall {
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let r : <$returns as ConvertibleToWasm>::NativeType = reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(Some(r.to_runtime_value()))
	});
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(None)
	})
}

#[macro_export]
macro_rules! dispatch {
	( $objectname:ident, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* ) => (
		fn execute(&mut self, name: &str, context: parity_wasm::interpreter::CallerContext)
			-> result::Result<Option<parity_wasm::interpreter::RuntimeValue>, parity_wasm::interpreter::Error> {
			let $objectname = self;
			match name {
				$(
					stringify!($name) => marshall!(context, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body),
				)*
				n => Err(parity_wasm::interpreter::Error::Trap(format!("not implemented: {}", n)).into())
			}
		}
	);
}

#[macro_export]
macro_rules! signatures {
	( $( $name:ident ( $( $params:ty ),* ) $( -> $returns:ty )* ),* ) => (
		const SIGNATURES: &'static [parity_wasm::interpreter::UserFunctionDescriptor] = &[
			$(
				convert_fn!( $name ( $( $params ),* ) $( -> $returns )* ),
			)*
		];
	);
}

#[macro_export]
macro_rules! function_executor {
	( $objectname:ident : $structname:ident, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* ) => (
		impl parity_wasm::interpreter::UserFunctionExecutor for $structname {
			dispatch!($objectname, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
		}
		impl $structname {
			signatures!($( $name( $( $params ),* ) $( -> $returns )* ),*);
		}
	);
}

use std::result;
use std::sync::{Arc, Mutex};

// user function executor
#[derive(Default)]
struct FunctionExecutor {
	context: Arc<Mutex<Option<FEContext>>>,
}

struct FEContext {
	heap_end: u32,
	memory: Arc<parity_wasm::interpreter::MemoryInstance>,
}

impl FEContext {
	fn new(m: &Arc<parity_wasm::interpreter::ModuleInstance>) -> Self {
		use parity_wasm::ModuleInstanceInterface;
		FEContext { heap_end: 1024, memory: Arc::clone(&m.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap()) }
	}
	fn allocate(&mut self, size: u32) -> u32 {
		let r = self.heap_end;
		self.heap_end += size;
		r
	}
	fn deallocate(&mut self, _offset: u32) {
	}
}

function_executor!(this: FunctionExecutor,
	imported(n: u64) -> u64 => { println!("imported {:?}", n); n + 1 },
	ext_memcpy(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
		let mut context = this.context.lock().unwrap();
		context.as_mut().unwrap().memory.copy_nonoverlapping(src as usize, dest as usize, count as usize).unwrap();
		println!("memcpy {} from {}, {} bytes", dest, src, count);
		dest
	},
	ext_memmove(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => { println!("memmove {} from {}, {} bytes", dest, src, count); dest },
	ext_memset(dest: *mut u8, val: i32, count: usize) -> *mut u8 => { println!("memset {} with {}, {} bytes", dest, val, count); dest },
	ext_malloc(size: usize) -> *mut u8 => {
		let mut context = this.context.lock().unwrap();
		let r = context.as_mut().unwrap().allocate(size);
		println!("malloc {} bytes at {}", size, r);
		r
	},
	ext_free(addr: *mut u8) => {
		let mut context = this.context.lock().unwrap();
		context.as_mut().unwrap().deallocate(addr);
		println!("free {}", addr)
	}
);


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
		use parity_wasm::interpreter::UserDefinedElements;
		use parity_wasm::RuntimeValue::I32;
		use std::collections::HashMap;

		let fe_context = Arc::new(Mutex::new(None));
		let externals = UserDefinedElements {
			executor: Some(FunctionExecutor { context: Arc::clone(&fe_context) }),
			globals: HashMap::new(),
			functions: ::std::borrow::Cow::from(FunctionExecutor::SIGNATURES),
		};

		let program = program_with_externals(externals, "env").unwrap();
		let module = parity_wasm::deserialize_buffer(code).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");
		*fe_context.lock().unwrap() = Some(FEContext::new(&module));

		let size = data.0.len() as u32;
		let offset = fe_context.lock().unwrap().as_mut().unwrap().allocate(size);
		module.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap().set(offset, &data.0).unwrap();

		module.execute_export(method, vec![I32(offset as i32), I32(size as i32)].into())
			.map(|o| {
				// TODO: populate vec properly
				OutData(vec![1; if let Some(I32(l)) = o { l as usize } else { 0 }])
			})
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
	use std::sync::{Arc, Mutex};
	use std::mem::transmute;
	use parity_wasm::interpreter::{MemoryInstance, UserDefinedElements};
	use parity_wasm::ModuleInstanceInterface;
	use parity_wasm::RuntimeValue::{I32, I64};

	// user function executor
	#[derive(Default)]
	struct FunctionExecutor {
		context: Arc<Mutex<Option<FEContext>>>,
	}

	struct FEContext {
		heap_end: u32,
		memory: Arc<MemoryInstance>,
	}

	impl FEContext {
		fn allocate(&mut self, size: u32) -> u32 {
			let r = self.heap_end;
			self.heap_end += size;
			r
		}
		fn deallocate(&mut self, _offset: u32) {
		}
	}

	function_executor!(this: FunctionExecutor,
		imported(n: u64) -> u64 => { println!("imported {:?}", n); n + 1 },
		ext_memcpy(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
			let mut context = this.context.lock().unwrap();
			context.as_mut().unwrap().memory.copy_nonoverlapping(src as usize, dest as usize, count as usize).unwrap();
			println!("memcpy {} from {}, {} bytes", dest, src, count);
			dest
		},
		ext_memmove(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => { println!("memmove {} from {}, {} bytes", dest, src, count); dest },
		ext_memset(dest: *mut u8, val: i32, count: usize) -> *mut u8 => { println!("memset {} with {}, {} bytes", dest, val, count); dest },
		ext_malloc(size: usize) -> *mut u8 => {
			let mut context = this.context.lock().unwrap();
			let r = context.as_mut().unwrap().allocate(size);
			println!("malloc {} bytes at {}", size, r);
			r
		},
		ext_free(addr: *mut u8) => {
			let mut context = this.context.lock().unwrap();
			context.as_mut().unwrap().deallocate(addr);
			println!("free {}", addr)
		}
	);

	#[test]
	fn should_pass_freeable_data() {
		let fe_context = Arc::new(Mutex::new(None));
		let externals = UserDefinedElements {
			executor: Some(FunctionExecutor { context: Arc::clone(&fe_context) }),
			globals: HashMap::new(),
			functions: ::std::borrow::Cow::from(FunctionExecutor::SIGNATURES),
		};

		let program = program_with_externals(externals, "env").unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.compact.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");

		*fe_context.lock().unwrap() = Some(FEContext { heap_end: 1024, memory: Arc::clone(&module.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap()) });

		let data = b"Hello world";
		let size = data.len() as u32;
		let offset = fe_context.lock().unwrap().as_mut().unwrap().allocate(size);
		module.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap().set(offset, data).unwrap();

		module.execute_export("test_data_in", vec![I32(offset as i32), I32(size as i32)].into()).unwrap();

		panic!();
	}

	#[test]
	fn should_provide_externalities() {
		let fe_context = Arc::new(Mutex::new(None));
		let externals = UserDefinedElements {
			executor: Some(FunctionExecutor { context: Arc::clone(&fe_context) }),
			globals: HashMap::new(),
			functions: ::std::borrow::Cow::from(FunctionExecutor::SIGNATURES),
		};

		let program = program_with_externals(externals, "env").unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");

		*fe_context.lock().unwrap() = Some(FEContext { heap_end: 1024, memory: Arc::clone(&module.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap()) });

		let argument: u64 = 20;
		assert_eq!(Some(I64(((argument + 1) * 2) as i64)), module.execute_export("test", vec![I64(argument as i64)].into()).unwrap());

		let mut x = [0u64; 2];
		module.memory(parity_wasm::interpreter::ItemIndex::Internal(0)).unwrap().get_into(1024, unsafe { transmute::<_, &mut [u8; 8]>(&mut x) }).unwrap();
		println!("heap: {:?}", x);
		panic!();
	}

	#[test]
	fn should_run_wasm() {
		let program = parity_wasm::ProgramInstance::new();
		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");
		let argument: i64 = 20;
		assert_eq!(Some(I64((argument + 1) * 2)), module.execute_export("test", vec![I64(argument)].into()).unwrap());
	}
}
