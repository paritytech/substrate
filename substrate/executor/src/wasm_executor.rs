// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Rust implementation of Substrate contracts.

use std::cmp::Ordering;
use std::collections::HashMap;
use wasmi::{
	Module, ModuleInstance,  MemoryInstance, MemoryRef, TableRef, ImportsBuilder,
};
use wasmi::RuntimeValue::{I32, I64};
use wasmi::memory_units::{Pages, Bytes};
use state_machine::{Externalities, CodeExecutor};
use error::{Error, ErrorKind, Result};
use wasm_utils::{DummyUserError};
use primitives::{blake2_256, twox_128, twox_256};
use primitives::hexdisplay::HexDisplay;
use primitives::sandbox as sandbox_primitives;
use triehash::ordered_trie_root;
use sandbox;

struct Heap {
	end: u32,
}

impl Heap {
	/// Construct new `Heap` struct.
	///
	/// Returns `Err` if the heap couldn't allocate required
	/// number of pages.
	///
	/// This could mean that wasm binary specifies memory
	/// limit and we are trying to allocate beyond that limit.
	fn new(memory: &MemoryRef) -> Result<Self> {
		const HEAP_SIZE_IN_PAGES: usize = 8;

		let prev_page_count = memory
			.grow(Pages(HEAP_SIZE_IN_PAGES))
			.map_err(|_| Error::from(ErrorKind::Runtime))?;
		Ok(Heap {
			end: Bytes::from(prev_page_count).0 as u32,
		})
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
	sandbox_store: sandbox::Store,
	heap: Heap,
	memory: MemoryRef,
	table: Option<TableRef>,
	ext: &'e mut E,
	hash_lookup: HashMap<Vec<u8>, Vec<u8>>,
}

impl<'e, E: Externalities> FunctionExecutor<'e, E> {
	fn new(m: MemoryRef, t: Option<TableRef>, e: &'e mut E) -> Result<Self> {
		Ok(FunctionExecutor {
			sandbox_store: sandbox::Store::new(),
			heap: Heap::new(&m)?,
			memory: m,
			table: t,
			ext: e,
			hash_lookup: HashMap::new(),
		})
	}
}

impl<'e, E: Externalities> sandbox::SandboxCapabilities for FunctionExecutor<'e, E> {
	fn store(&self) -> &sandbox::Store {
		&self.sandbox_store
	}
	fn store_mut(&mut self) -> &mut sandbox::Store {
		&mut self.sandbox_store
	}
	fn allocate(&mut self, len: u32) -> u32 {
		self.heap.allocate(len)
	}
	fn deallocate(&mut self, ptr: u32) {
		self.heap.deallocate(ptr)
	}
	fn write_memory(&mut self, ptr: u32, data: &[u8]) -> ::std::result::Result<(), DummyUserError> {
		self.memory.set(ptr, data).map_err(|_| DummyUserError)
	}
	fn read_memory(&self, ptr: u32, len: u32) -> ::std::result::Result<Vec<u8>, DummyUserError> {
		self.memory.get(ptr, len as usize).map_err(|_| DummyUserError)
	}
}

trait WritePrimitive<T: Sized> {
	fn write_primitive(&self, offset: u32, t: T) -> ::std::result::Result<(), DummyUserError>;
}

impl WritePrimitive<u32> for MemoryInstance {
	fn write_primitive(&self, offset: u32, t: u32) -> ::std::result::Result<(), DummyUserError> {
		use byteorder::{LittleEndian, ByteOrder};
		let mut r = [0u8; 4];
		LittleEndian::write_u32(&mut r, t);
		self.set(offset, &r).map_err(|_| DummyUserError)
	}
}

trait ReadPrimitive<T: Sized> {
	fn read_primitive(&self, offset: u32) -> ::std::result::Result<T, DummyUserError>;
}

impl ReadPrimitive<u32> for MemoryInstance {
	fn read_primitive(&self, offset: u32) -> ::std::result::Result<u32, DummyUserError> {
		use byteorder::{LittleEndian, ByteOrder};
		Ok(LittleEndian::read_u32(&self.get(offset, 4).map_err(|_| DummyUserError)?))
	}
}

fn ascii_format(asciish: &[u8]) -> String {
	let mut r = String::new();
	let mut latch = false;
	for c in asciish {
		match (latch, *c) {
			(false, 32...127) => r.push(*c as char),
			_ => {
				if !latch {
					r.push('#');
					latch = true;
				}
				r.push_str(&format!("{:02x}", *c));
			}
		}
	}
	r
}

impl_function_executor!(this: FunctionExecutor<'e, E>,
	ext_print_utf8(utf8_data: *const u8, utf8_len: u32) => {
		if let Ok(utf8) = this.memory.get(utf8_data, utf8_len as usize) {
			if let Ok(message) = String::from_utf8(utf8) {
				println!("{}", message);
			}
		}
		Ok(())
	},
	ext_print_hex(data: *const u8, len: u32) => {
		if let Ok(hex) = this.memory.get(data, len as usize) {
			println!("{}", HexDisplay::from(&hex));
		}
		Ok(())
	},
	ext_print_num(number: u64) => {
		println!("{}", number);
		Ok(())
	},
	ext_memcmp(s1: *const u8, s2: *const u8, n: usize) -> i32 => {
		let sl1 = this.memory.get(s1, n as usize).map_err(|_| DummyUserError)?;
		let sl2 = this.memory.get(s2, n as usize).map_err(|_| DummyUserError)?;
		Ok(match sl1.cmp(&sl2) {
			Ordering::Greater => 1,
			Ordering::Less => -1,
			Ordering::Equal => 0,
		})
	},
	ext_memcpy(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
		this.memory.copy_nonoverlapping(src as usize, dest as usize, count as usize)
			.map_err(|_| DummyUserError)?;
		trace!(target: "runtime-io", "memcpy {} from {}, {} bytes", dest, src, count);
		Ok(dest)
	},
	ext_memmove(dest: *mut u8, src: *const u8, count: usize) -> *mut u8 => {
		this.memory.copy(src as usize, dest as usize, count as usize)
			.map_err(|_| DummyUserError)?;
		trace!(target: "runtime-io", "memmove {} from {}, {} bytes", dest, src, count);
		Ok(dest)
	},
	ext_memset(dest: *mut u8, val: u32, count: usize) -> *mut u8 => {
		this.memory.clear(dest as usize, val as u8, count as usize)
			.map_err(|_| DummyUserError)?;
		trace!(target: "runtime-io", "memset {} with {}, {} bytes", dest, val, count);
		Ok(dest)
	},
	ext_malloc(size: usize) -> *mut u8 => {
		let r = this.heap.allocate(size);
		trace!(target: "runtime-io", "malloc {} bytes at {}", size, r);
		Ok(r)
	},
	ext_free(addr: *mut u8) => {
		this.heap.deallocate(addr);
		trace!(target: "runtime-io", "free {}", addr);
		Ok(())
	},
	ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32) => {
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| DummyUserError)?;
		let value = this.memory.get(value_data, value_len as usize).map_err(|_| DummyUserError)?;
		if let Some(preimage) = this.hash_lookup.get(&key) {
			trace!(target: "wasm-trace", "*** Setting storage: %{} -> {}   [k={}]", ascii_format(&preimage), HexDisplay::from(&value), HexDisplay::from(&key));
		} else {
			trace!(target: "wasm-trace", "*** Setting storage:  {} -> {}   [k={}]", ascii_format(&key), HexDisplay::from(&value), HexDisplay::from(&key));
		}
		this.ext.set_storage(key, value);
		Ok(())
	},
	ext_clear_storage(key_data: *const u8, key_len: u32) => {
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| DummyUserError)?;
		if let Some(preimage) = this.hash_lookup.get(&key) {
			trace!(target: "wasm-trace", "*** Clearing storage: %{}   [k={}]", ascii_format(&preimage), HexDisplay::from(&key));
		} else {
			trace!(target: "wasm-trace", "*** Clearing storage:  {}   [k={}]", ascii_format(&key), HexDisplay::from(&key));
		}
		this.ext.clear_storage(&key);
		Ok(())
	},
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8 => {
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| DummyUserError)?;
		let maybe_value = this.ext.storage(&key);

		if let Some(preimage) = this.hash_lookup.get(&key) {
			trace!(target: "wasm-trace", "    Getting storage: %{} == {}   [k={}]", ascii_format(&preimage), if let Some(ref b) = maybe_value { format!("{}", HexDisplay::from(b)) } else { "<empty>".to_owned() }, HexDisplay::from(&key));
		} else {
			trace!(target: "wasm-trace", "    Getting storage:  {} == {}   [k={}]", ascii_format(&key), if let Some(ref b) = maybe_value { format!("{}", HexDisplay::from(b)) } else { "<empty>".to_owned() }, HexDisplay::from(&key));
		}

		if let Some(value) = maybe_value {
			let offset = this.heap.allocate(value.len() as u32) as u32;
			this.memory.set(offset, &value).map_err(|_| DummyUserError)?;
			this.memory.write_primitive(written_out, value.len() as u32)?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())?;
			Ok(0)
		}
	},
	// return u32::max_value() if no value exists for the key.
	ext_get_storage_into(key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32 => {
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| DummyUserError)?;
		let maybe_value = this.ext.storage(&key);
		if let Some(preimage) = this.hash_lookup.get(&key) {
			trace!(target: "wasm-trace", "    Getting storage: %{} == {}   [k={}]", ascii_format(&preimage), if let Some(ref b) = maybe_value { format!("{}", HexDisplay::from(b)) } else { "<empty>".to_owned() }, HexDisplay::from(&key));
		} else {
			trace!(target: "wasm-trace", "    Getting storage:  {} == {}   [k={}]", ascii_format(&key), if let Some(ref b) = maybe_value { format!("{}", HexDisplay::from(b)) } else { "<empty>".to_owned() }, HexDisplay::from(&key));
		}
		if let Some(value) = maybe_value {
			let value = &value[value_offset as usize..];
			let written = ::std::cmp::min(value_len as usize, value.len());
			this.memory.set(value_data, &value[..written]).map_err(|_| DummyUserError)?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	ext_storage_root(result: *mut u8) => {
		let r = this.ext.storage_root();
		this.memory.set(result, &r[..]).map_err(|_| DummyUserError)?;
		Ok(())
	},
	ext_enumerated_trie_root(values_data: *const u8, lens_data: *const u32, lens_len: u32, result: *mut u8) => {
		let values = (0..lens_len)
			.map(|i| this.memory.read_primitive(lens_data + i * 4))
			.collect::<::std::result::Result<Vec<u32>, DummyUserError>>()?
			.into_iter()
			.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
			.map(|(offset, len)|
				this.memory.get(values_data + offset, len as usize)
					.map_err(|_| DummyUserError)
			)
			.collect::<::std::result::Result<Vec<_>, DummyUserError>>()?;
		let r = ordered_trie_root(values.into_iter());
		this.memory.set(result, &r[..]).map_err(|_| DummyUserError)?;
		Ok(())
	},
	ext_chain_id() -> u64 => {
		Ok(this.ext.chain_id())
	},
	ext_twox_128(data: *const u8, len: u32, out: *mut u8) => {
		let result = if len == 0 {
			let hashed = twox_128(&[0u8; 0]);
			trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
			this.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = this.memory.get(data, len as usize).map_err(|_| DummyUserError)?;
			let hashed_key = twox_128(&key);
			if let Ok(skey) = ::std::str::from_utf8(&key) {
				trace!(target: "xxhash", "XXhash: {} -> {}", skey, HexDisplay::from(&hashed_key));
			} else {
				trace!(target: "xxhash", "XXhash: {} -> {}", HexDisplay::from(&key), HexDisplay::from(&hashed_key));
			}
			this.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		this.memory.set(out, &result).map_err(|_| DummyUserError)?;
		Ok(())
	},
	ext_twox_256(data: *const u8, len: u32, out: *mut u8) => {
		let result = if len == 0 {
			twox_256(&[0u8; 0])
		} else {
			twox_256(&this.memory.get(data, len as usize).map_err(|_| DummyUserError)?)
		};
		this.memory.set(out, &result).map_err(|_| DummyUserError)?;
		Ok(())
	},
	ext_blake2_256(data: *const u8, len: u32, out: *mut u8) => {
		let result = if len == 0 {
			blake2_256(&[0u8; 0])
		} else {
			blake2_256(&this.memory.get(data, len as usize).map_err(|_| DummyUserError)?)
		};
		this.memory.set(out, &result).map_err(|_| DummyUserError)?;
		Ok(())
	},
	ext_ed25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32 => {
		let mut sig = [0u8; 64];
		this.memory.get_into(sig_data, &mut sig[..]).map_err(|_| DummyUserError)?;
		let mut pubkey = [0u8; 32];
		this.memory.get_into(pubkey_data, &mut pubkey[..]).map_err(|_| DummyUserError)?;
		let msg = this.memory.get(msg_data, msg_len as usize).map_err(|_| DummyUserError)?;

		Ok(if ::ed25519::verify(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	},
	ext_sandbox_instantiate(dispatch_thunk_idx: usize, wasm_ptr: *const u8, wasm_len: usize, imports_ptr: *const u8, imports_len: usize, state: usize) -> u32 => {
		let wasm = this.memory.get(wasm_ptr, wasm_len as usize).map_err(|_| DummyUserError)?;
		let raw_env_def = this.memory.get(imports_ptr, imports_len as usize).map_err(|_| DummyUserError)?;

		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = this.table.as_ref().ok_or_else(|| DummyUserError)?;
			table.get(dispatch_thunk_idx)
				.map_err(|_| DummyUserError)?
				.ok_or_else(|| DummyUserError)?
				.clone()
		};

		let instance_idx = sandbox::instantiate(this, dispatch_thunk, &wasm, &raw_env_def, state)?;

		Ok(instance_idx as u32)
	},
	ext_sandbox_instance_teardown(instance_idx: u32) => {
		this.sandbox_store.instance_teardown(instance_idx)?;
		Ok(())
	},
	ext_sandbox_invoke(instance_idx: u32, export_ptr: *const u8, export_len: usize, args_ptr: *const u8, args_len: usize, state: usize) -> u32 => {
		trace!(target: "runtime-sandbox", "invoke, instance_idx={}", instance_idx);
		let export = this.memory.get(export_ptr, export_len as usize)
			.map_err(|_| DummyUserError)
			.and_then(|b|
				String::from_utf8(b)
					.map_err(|_| DummyUserError)
			)?;
		let serialized_args = this.memory.get(args_ptr, args_len as usize)
			.map_err(|_| DummyUserError)?;
		let args: Vec<sandbox_primitives::TypedValue> = ::codec::Slicable::decode(&mut &serialized_args[..]).ok_or_else(|| DummyUserError)?;
		let args = args.into_iter().map(|e| e.into()).collect::<Vec<_>>();

		let instance = this.sandbox_store.instance(instance_idx)?;
		let result = instance.invoke(&export, &args, this, state);

		match result {
			Ok(None) => Ok(sandbox_primitives::ERR_OK),
			Ok(Some(_val)) => unimplemented!(),
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	},
	ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32 => {
		let mem_idx = this.sandbox_store.new_memory(initial, maximum)?;
		Ok(mem_idx)
	},
	ext_sandbox_memory_get(memory_idx: u32, offset: u32, buf_ptr: *mut u8, buf_len: usize) -> u32 => {
		let dst_memory = this.sandbox_store.memory(memory_idx)?;

		let data: Vec<u8> = match dst_memory.get(offset, buf_len as usize) {
			Ok(data) => data,
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		};
		match this.memory.set(buf_ptr, &data) {
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
			_ => {},
		}

		Ok(sandbox_primitives::ERR_OK)
	},
	ext_sandbox_memory_set(memory_idx: u32, offset: u32, val_ptr: *const u8, val_len: usize) -> u32 => {
		let dst_memory = this.sandbox_store.memory(memory_idx)?;

		let data = match this.memory.get(offset, val_len as usize) {
			Ok(data) => data,
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		};
		match dst_memory.set(val_ptr, &data) {
			Err(_) => return Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
			_ => {},
		}

		Ok(sandbox_primitives::ERR_OK)
	},
	ext_sandbox_memory_teardown(memory_idx: u32) => {
		this.sandbox_store.memory_teardown(memory_idx)?;
		Ok(())
	},
	=> <'e, E: Externalities + 'e>
);

/// Wasm rust executor for contracts.
///
/// Executes the provided code in a sandboxed wasm runtime.
#[derive(Debug, Default, Clone)]
pub struct WasmExecutor;

impl CodeExecutor for WasmExecutor {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &[u8],
	) -> Result<Vec<u8>> {
		let module = Module::from_buffer(code).expect("all modules compiled with rustc are valid wasm code; qed");

		// start module instantiation. Don't run 'start' function yet.
		let intermediate_instance = ModuleInstance::new(
			&module,
			&ImportsBuilder::new()
				.with_resolver("env", FunctionExecutor::<E>::resolver())
		)?;

		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = intermediate_instance
			.not_started_instance()
			.export_by_name("memory")
			.expect("all modules compiled with rustc should have an export named 'memory'; qed")
			.as_memory()
			.expect("in module generated by rustc export named 'memory' should be a memory; qed")
			.clone();
		let table: Option<TableRef> = intermediate_instance
			.not_started_instance()
			.export_by_name("table")
			.and_then(|e| e.as_table().cloned());
		let mut fec = FunctionExecutor::new(memory.clone(), table, ext)?;

		// finish instantiation by running 'start' function (if any).
		let instance = intermediate_instance.run_start(&mut fec)?;

		let size = data.len() as u32;
		let offset = fec.heap.allocate(size);
		memory.set(offset, &data).expect("heap always gives a sensible offset to write");

		let returned = instance.invoke_export(
			method,
			&[
				I32(offset as i32),
				I32(size as i32)
			],
			&mut fec
		)?;

		if let Some(I64(r)) = returned {
			let offset = r as u32;
			let length = (r >> 32) as u32 as usize;
			memory.get(offset, length)
				.map_err(|_| ErrorKind::Runtime.into())
		} else {
			Err(ErrorKind::InvalidReturn.into())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use rustc_hex::FromHex;
	use codec::Slicable;
	use state_machine::TestExternalities;

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn returning_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor.call(&mut ext, &test_code[..], "test_empty_return", &[]).unwrap();
		assert_eq!(output, vec![0u8; 0]);
	}

	#[test]
	fn panicking_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor.call(&mut ext, &test_code[..], "test_panic", &[]);
		assert!(output.is_err());

		let output = WasmExecutor.call(&mut ext, &test_code[..], "test_conditional_panic", &[2]);
		assert!(output.is_err());
	}

	#[test]
	fn storage_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"foo".to_vec(), b"bar".to_vec());
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor.call(&mut ext, &test_code[..], "test_data_in", b"Hello world").unwrap();

		assert_eq!(output, b"all ok!".to_vec());

		let expected: HashMap<_, _> = map![
			b"input".to_vec() => b"Hello world".to_vec(),
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		];
		assert_eq!(expected, ext);
	}

	#[test]
	fn blake2_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_blake2_256", &[]).unwrap(),
			blake2_256(&b""[..]).encode()
		);
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_blake2_256", b"Hello world!").unwrap(),
			blake2_256(&b"Hello world!"[..]).encode()
		);
	}

	#[test]
	fn twox_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_twox_256", &[]).unwrap(),
			FromHex::from_hex("99e9d85137db46ef4bbea33613baafd56f963c64b1f3685a4eb4abd67ff6203a").unwrap()
		);
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_twox_256", b"Hello world!").unwrap(),
			FromHex::from_hex("b27dfd7f223f177f2a13647b533599af0c07f68bda23d96d059da2b451a35a74").unwrap()
		);
	}

	#[test]
	fn twox_128_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_twox_128", &[]).unwrap(),
			FromHex::from_hex("99e9d85137db46ef4bbea33613baafd5").unwrap()
		);
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_twox_128", b"Hello world!").unwrap(),
			FromHex::from_hex("b27dfd7f223f177f2a13647b533599af").unwrap()
		);
	}

	#[test]
	fn ed25519_verify_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		let key = ::ed25519::Pair::from_seed(&blake2_256(b"test"));
		let sig = key.sign(b"all ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(sig.as_ref());

		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![1]
		);

		let other_sig = key.sign(b"all is not ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(other_sig.as_ref());

		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![0]
		);
	}

	#[test]
	fn enumerated_trie_root_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor.call(&mut ext, &test_code[..], "test_enumerated_trie_root", &[]).unwrap(),
			ordered_trie_root(vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()]).0.encode()
		);
	}


}
