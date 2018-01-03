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

use std::sync::Arc;
use std::collections::HashMap;
use parity_wasm::{deserialize_buffer, ModuleInstanceInterface, ProgramInstance};
use parity_wasm::interpreter::{ItemIndex};
use parity_wasm::RuntimeValue::{I32, I64};
use primitives::contract::CallData;
use state_machine::{Externalities, CodeExecutor};
use error::{Error, ErrorKind, Result};
use wasm_utils::{MemoryInstance, UserDefinedElements,
	AddModuleWithoutFullDependentInstance};

struct Heap {
	end: u32,
}

impl Heap {
	fn new() -> Self {
		Heap {
			end: 1024,
		}
	}
	fn allocate(&mut self, size: u32) -> u32 {
		let r = self.end;
		self.end += size;
		r
	}
	fn deallocate(&mut self, _offset: u32) {
	}
}

struct FunctionExecutor<'e, E: Externalities + 'e> {
	heap: Heap,
	memory: Arc<MemoryInstance>,
	ext: &'e mut E,
}

impl<'e, E: Externalities> FunctionExecutor<'e, E> {
	fn new(m: &Arc<MemoryInstance>, e: &'e mut E) -> Self {
		FunctionExecutor {
			heap: Heap::new(),
			memory: Arc::clone(m),
			ext: e,
		}
	}
}

impl_function_executor!(this: FunctionExecutor<'e, E>,
	imported(n: u64) -> u64 => { println!("imported {:?}", n); n + 1 },
	ext_memcpy(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
		this.memory.copy_nonoverlapping(src as usize, dest as usize, count as usize).unwrap();
		println!("memcpy {} from {}, {} bytes", dest, src, count);
		dest
	},
	ext_memmove(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => { println!("memmove {} from {}, {} bytes", dest, src, count); dest },
	ext_memset(dest: *mut u8, val: i32, count: usize) -> *mut u8 => { println!("memset {} with {}, {} bytes", dest, val, count); dest },
	ext_malloc(size: usize) -> *mut u8 => {
		let r = this.heap.allocate(size);
		println!("malloc {} bytes at {}", size, r);
		r
	},
	ext_free(addr: *mut u8) => {
		this.heap.deallocate(addr);
		println!("free {}", addr)
	},
	set_storage(key_data: *const u8, key_len: i32, value_data: *const u8, value_len: i32) => {
		if let (Ok(key), Ok(value)) = (this.memory.get(key_data, key_len as usize), this.memory.get(value_data, value_len as usize)) {
			this.ext.set_storage(0, key, value);
		}
	},
	get_allocated_storage(key_data: *const u8, key_len: i32, written_out: *mut i32) -> *mut u8 => {
		let (offset, written) = if let Ok(key) = this.memory.get(key_data, key_len as usize) {
			if let Ok(value) = this.ext.storage(0, &key) {
				let offset = this.heap.allocate(value.len() as u32) as u32;
				let _ = this.memory.set(offset, &value);
				(offset, value.len() as u32)
			} else { (0, 0) }
		} else { (0, 0) };

		if written > 0 {
			use byteorder::{LittleEndian, ByteOrder};
			let mut r = [0u8; 4];
			LittleEndian::write_u32(&mut r, written);
			let _ = this.memory.set(written_out, &r);
		}
		offset as u32
	}
	=> <'e, E: Externalities + 'e>
);

/// Dummy rust executor for contracts.
///
/// Instead of actually executing the provided code it just
/// dispatches the calls to pre-defined hardcoded implementations in rust.
#[derive(Debug, Default)]
pub struct WasmExecutor;

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

		// TODO: handle all expects as errors to be returned.

		let program = ProgramInstance::new().expect("this really shouldn't be able to fail; qed");

		let module = deserialize_buffer(code).expect("all modules compiled with rustc are valid wasm code; qed");
		let module = program.add_module_by_sigs("test", module, map!["env" => FunctionExecutor::<E>::SIGNATURES]).expect("runtime signatures always provided; qed");

		let memory = module.memory(ItemIndex::Internal(0)).expect("all modules compiled with rustc include memory segments; qed");
		let mut fec = FunctionExecutor::new(&memory, ext);

		let size = data.0.len() as u32;
		let offset = fec.heap.allocate(size);
		memory.set(offset, &data.0).expect("heap always gives a sensible offset to write");

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
	struct TestExternalities {
		data: HashMap<Vec<u8>, Vec<u8>>,
	}
	impl Externalities for TestExternalities {
		type Error = Error;

		fn code(&self) -> Result<Vec<u8>> {
			unimplemented!()
		}

		fn storage(&self, _object: u64, _key: &[u8]) -> Result<Vec<u8>> {
			Ok(self.data.get(_key).map(|v| v.clone()).unwrap_or_else(|| vec![]))
		}

		fn set_code(&mut self, _code: Vec<u8>) {
			unimplemented!()
		}

		fn set_storage(&mut self, _object: u64, _key: Vec<u8>, _value: Vec<u8>) {
			self.data.insert(_key, _value);
		}
	}

	#[test]
	fn should_pass_externalities_at_call() {
		let mut ext = TestExternalities::default();

		let program = ProgramInstance::new().unwrap();

		let test_module = include_bytes!("../../runtime/target/wasm32-unknown-unknown/release/runtime.compact.wasm");
		let module = deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module_by_sigs("test", module, map!["env" => FunctionExecutor::<TestExternalities>::SIGNATURES]).expect("Failed to initialize module");

		{
			let memory = module.memory(ItemIndex::Internal(0)).unwrap();
			let mut fec = FunctionExecutor::new(&memory, &mut ext);

			let data = b"Hello world";
			let size = data.len() as u32;
			let offset = fec.heap.allocate(size);
			memory.set(offset, data).unwrap();

			module.execute_export("test_data_in",
				program.params_with_external("env", &mut fec)
					.add_argument(I32(offset as i32))
					.add_argument(I32(size as i32))
			).unwrap();
		}

		println!("storage: {:?}", ext.data);

		panic!();
	}
}
