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

use parity_wasm::{deserialize_buffer, ModuleInstanceInterface, ProgramInstance};
use parity_wasm::interpreter::{ItemIndex};
use parity_wasm::RuntimeValue::{I32, I64};
use std::collections::HashMap;
use primitives::contract::CallData;
use state_machine::{Externalities, CodeExecutor};
use error::{Error, ErrorKind, Result};
use std::sync::{Arc};
use wasm_utils::{ModuleInstance, MemoryInstance, UserDefinedElements, AddModuleWithoutFullDependentInstance};

struct FunctionExecutor {
	heap_end: u32,
	memory: Arc<MemoryInstance>,
}

impl FunctionExecutor {
	fn new(m: &Arc<ModuleInstance>) -> Self {
		FunctionExecutor {
			heap_end: 1024,
			memory: Arc::clone(&m.memory(ItemIndex::Internal(0)).unwrap()),
		}
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
		this.memory.copy_nonoverlapping(src as usize, dest as usize, count as usize).unwrap();
		println!("memcpy {} from {}, {} bytes", dest, src, count);
		dest
	},
	ext_memmove(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => { println!("memmove {} from {}, {} bytes", dest, src, count); dest },
	ext_memset(dest: *mut u8, val: i32, count: usize) -> *mut u8 => { println!("memset {} with {}, {} bytes", dest, val, count); dest },
	ext_malloc(size: usize) -> *mut u8 => {
		let r = this.allocate(size);
		println!("malloc {} bytes at {}", size, r);
		r
	},
	ext_free(addr: *mut u8) => {
		this.deallocate(addr);
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
	) -> Result<u64> {
		// TODO: avoid copying code by requiring code to remain immutable through execution,
		// splitting it off from potentially mutable externalities.
		let code = match ext.code() {
			Ok(e) => e.to_owned(),
			Err(e) => Err(ErrorKind::Externalities(Box::new(e)))?,
		};

		let program = ProgramInstance::new().unwrap();

		let module = deserialize_buffer(code).expect("Failed to load module");
		let module = program.add_module_by_sigs("test", module, map!["env" => FunctionExecutor::SIGNATURES]).expect("Failed to initialize module");

		let mut fec = FunctionExecutor::new(&module);

		let size = data.0.len() as u32;
		let offset = fec.allocate(size);
		module.memory(ItemIndex::Internal(0)).unwrap().set(offset, &data.0).unwrap();

		let r = module.execute_export(method,
			program.params_with_external("env", &mut fec)
				.add_argument(I32(offset as i32))
				.add_argument(I32(size as i32)))
			.map_err(|_| ErrorKind::Runtime.into())
			.and_then(|i| if let Some(I64(r)) = i { Ok(r as u64) } else { Err(ErrorKind::InvalidReturn.into()) });
		r
	}
}

#[cfg(test)]
mod tests {

	use super::*;

	#[derive(Debug, Default)]
	struct TestExternalities;
	impl Externalities for TestExternalities {
		type Error = Error;

		fn code(&self) -> Result<&[u8]> {
			unimplemented!()
		}

		fn storage(&self, _object: u64, _key: &[u8]) -> Result<&[u8]> {
			unimplemented!()
		}

		fn set_code(&mut self, _code: Vec<u8>) {
			unimplemented!()
		}

		fn set_storage(&mut self, _object: u64, _key: Vec<u8>, _value: Vec<u8>) {
			unimplemented!()
		}
	}

	#[test]
	fn should_pass_externalities_at_call() {
		let program = ProgramInstance::new().unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.compact.wasm");
		let module = deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module_by_sigs("test", module, map!["env" => FunctionExecutor::SIGNATURES]).expect("Failed to initialize module");

		let mut fec = FunctionExecutor {
			heap_end: 1024,
			memory: Arc::clone(&module.memory(ItemIndex::Internal(0)).unwrap())
		};

		let data = b"Hello world";
		let size = data.len() as u32;
		let offset = fec.allocate(size);
		module.memory(ItemIndex::Internal(0)).unwrap().set(offset, data).unwrap();

		module.execute_export("test_data_in",
			program.params_with_external("env", &mut fec)
				.add_argument(I32(offset as i32))
				.add_argument(I32(size as i32))
		).unwrap();

		// TODO: program.execute(module, "test_data_in", map!["env" => &mut fec], [I32(offset as i32), I32(size as i32)]);

		panic!();
	}
/*
	#[test]
	fn should_provide_externalities() {
		let fe_context = Arc::new(Mutex::new(None));
		let mut fex = FunctionExecutor { context: Arc::clone(&fe_context) };
		let externals = UserDefinedElements {
			executor: Some(&mut fex),
			globals: HashMap::new(),
			functions: ::std::borrow::Cow::from(FunctionExecutor::SIGNATURES),
		};

		let program = program_with_externals::<FunctionExecutor>(externals, "env").unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.wasm");
		let module = deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");

		*fe_context.lock().unwrap() = Some(FunctionExecutor { heap_end: 1024, memory: Arc::clone(&module.memory(ItemIndex::Internal(0)).unwrap()) });

		let argument: u64 = 20;
		assert_eq!(Some(I64(((argument + 1) * 2) as i64)), module.execute_export("test", vec![I64(argument as i64)].into()).unwrap());

		let mut x = [0u64; 2];
		module.memory(ItemIndex::Internal(0)).unwrap().get_into(1024, unsafe { transmute::<_, &mut [u8; 8]>(&mut x) }).unwrap();
		println!("heap: {:?}", x);
		panic!();
	}*/
}
