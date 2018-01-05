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

trait WritePrimitive<T: Sized> {
	fn write_primitive(&self, offset: u32, t: T);
}

impl WritePrimitive<u32> for MemoryInstance {
	fn write_primitive(&self, offset: u32, t: u32) {
		use byteorder::{LittleEndian, ByteOrder};
		let mut r = [0u8; 4];
		LittleEndian::write_u32(&mut r, t);
		let _ = self.set(offset, &r);
	}
}

impl_function_executor!(this: FunctionExecutor<'e, E>,
	imported(n: u64) -> u64 => { println!("imported {:?}", n); n + 1 },
	ext_memcpy(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
		let _ = this.memory.copy_nonoverlapping(src as usize, dest as usize, count as usize);
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
			this.ext.set_storage(key, value);
		}
	},
	get_allocated_storage(key_data: *const u8, key_len: i32, written_out: *mut i32) -> *mut u8 => {
		let (offset, written) = if let Ok(key) = this.memory.get(key_data, key_len as usize) {
			if let Ok(value) = this.ext.storage(&key) {
				let offset = this.heap.allocate(value.len() as u32) as u32;
				let _ = this.memory.set(offset, &value);
				(offset, value.len() as u32)
			} else { (0, 0) }
		} else { (0, 0) };

		this.memory.write_primitive(written_out, written);
		offset as u32
	},
	set_code(code_data: *const u8, code_len: i32) => {
		if let Ok(code) = this.memory.get(code_data, code_len as usize) {
			this.ext.set_code(code);
		}
	},
	get_allocated_code(written_out: *mut i32) -> *mut u8 => {
		let (offset, written) = if let Ok(code) = this.ext.code() {
			let offset = this.heap.allocate(code.len() as u32) as u32;
			let _ = this.memory.set(offset, &code);
			(offset, code.len() as u32)
		} else { (0, 0) };
		this.memory.write_primitive(written_out, written);
		offset as u32
	},
	get_validator_count() -> i32 => {
		this.ext.validator_count() as i32
	},
	get_allocated_validator(index: i32, written_out: *mut i32) -> *mut u8 => {
		let (offset, written) = if let Ok(v) = this.ext.validator(index as usize) {
			let offset = this.heap.allocate(v.len() as u32) as u32;
			let _ = this.memory.set(offset, &v);
			(offset, v.len() as u32)
		} else { (0, 0) };
		this.memory.write_primitive(written_out, written);
		offset as u32
	},
	set_validator_count(validator_count: i32) => {
		this.ext.set_validator_count(validator_count as usize);
	},
	set_validator(index: i32, validator_data: *const u8, validator_len: i32) => {
		if let Ok(validator) = this.memory.get(validator_data, validator_len as usize) {
			this.ext.set_validator(index as usize, validator);
		}
	}
	=> <'e, E: Externalities + 'e>
);

/// Wasm rust executor for contracts.
///
/// Executes the provided code in a sandboxed wasm runtime.
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
		code: Vec<u8>,
		validators: Vec<Vec<u8>>,
	}
	impl Externalities for TestExternalities {
		type Error = Error;

		fn code(&self) -> Result<&[u8]> {
			Ok(self.code.as_slice())
		}

		fn storage(&self, key: &[u8]) -> Result<&[u8]> {
			Ok(self.data.get(&key.to_vec()).map_or(&[] as &[u8], Vec::as_slice))
		}

		fn validator(&self, index: usize) -> Result<&[u8]> {
			if index < self.validators.len() {
				Ok(self.validators[index].as_slice())
			} else {
				Err(ErrorKind::InvalidIndex.into())
			}
		}

		fn validator_count(&self) -> usize {
			self.validators.len()
		}

		fn set_code(&mut self, code: Vec<u8>) {
			self.code = code;
		}

		fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
			self.data.insert(key, value);
		}

		fn set_validator(&mut self, index: usize, value: Vec<u8>) {
			if index < self.validators.len() {
				self.validators[index] = value;
			}
		}

		fn set_validator_count(&mut self, count: usize) {
			self.validators.resize(count, vec![]);
		}
	}

	#[test]
	fn should_pass_externalities_at_call() {
		let mut ext = TestExternalities::default();
		ext.code = b"The code".to_vec();

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

		let expected: HashMap<_, _> = map![
			vec![105, 110, 112, 117, 116] => vec![72, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100],
			vec![99, 111, 100, 101] => vec![84, 104, 101, 32, 99, 111, 100, 101]
		];
		assert_eq!(expected, ext.data);

		let expected = vec![ b"Hello world".to_vec() ];
		assert_eq!(expected, ext.validators);
	}
}
