// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use std::fmt;

use wasmi::{
	Module, ModuleInstance, MemoryInstance, MemoryRef, TableRef, ImportsBuilder, ModuleRef, HostError,
};
use wasmi::RuntimeValue::{I32, I64};
use wasmi::memory_units::{Bytes, Pages};
use state_machine::Externalities;
use error::{self, Error, ErrorKind};
use primitives::{blake2_256, twox_128, twox_256, ed25519};
use primitives::hexdisplay::HexDisplay;
use primitives::sandbox as sandbox_primitives;
use primitives::{H256, Blake2Hasher};
use trie::ordered_trie_root;
use sandbox;
use heap;

#[cfg(feature="wasm-extern-trace")]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ( trace!( $( $x )* ) )
}
#[cfg(not(feature="wasm-extern-trace"))]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ()
}

#[derive(Debug)]
pub struct UserError(pub &'static str);
impl fmt::Display for UserError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UserError: {}", self.0)
	}
}
impl HostError for UserError {
}

struct FunctionExecutor<'e, E: Externalities<Blake2Hasher> + 'e> {
	sandbox_store: sandbox::Store,
	heap: heap::Heap,
	memory: MemoryRef,
	table: Option<TableRef>,
	ext: &'e mut E,
	hash_lookup: HashMap<Vec<u8>, Vec<u8>>,
}

impl<'e, E: Externalities<Blake2Hasher>> FunctionExecutor<'e, E> {
	fn new(m: MemoryRef, t: Option<TableRef>, e: &'e mut E) -> error::Result<Self> {
		let current_size: Bytes = m.current_size().into();
		let current_size = current_size.0 as u32;
		let used_size = m.used_size().0 as u32;
		let heap_size = current_size - used_size;

		Ok(FunctionExecutor {
			sandbox_store: sandbox::Store::new(),
			heap: heap::Heap::new(used_size, heap_size),
			memory: m,
			table: t,
			ext: e,
			hash_lookup: HashMap::new(),
		})
	}
}

impl<'e, E: Externalities<Blake2Hasher>> sandbox::SandboxCapabilities for FunctionExecutor<'e, E> {
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
	fn write_memory(&mut self, ptr: u32, data: &[u8]) -> Result<(), UserError> {
		self.memory.set(ptr, data).map_err(|_| UserError("Invalid attempt to write_memory"))
	}
	fn read_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>, UserError> {
		self.memory.get(ptr, len as usize).map_err(|_| UserError("Invalid attempt to write_memory"))
	}
}

trait WritePrimitive<T: Sized> {
	fn write_primitive(&self, offset: u32, t: T) -> Result<(), UserError>;
}

impl WritePrimitive<u32> for MemoryInstance {
	fn write_primitive(&self, offset: u32, t: u32) -> Result<(), UserError> {
		use byteorder::{LittleEndian, ByteOrder};
		let mut r = [0u8; 4];
		LittleEndian::write_u32(&mut r, t);
		self.set(offset, &r).map_err(|_| UserError("Invalid attempt to write_primitive"))
	}
}

trait ReadPrimitive<T: Sized> {
	fn read_primitive(&self, offset: u32) -> Result<T, UserError>;
}

impl ReadPrimitive<u32> for MemoryInstance {
	fn read_primitive(&self, offset: u32) -> Result<u32, UserError> {
		use byteorder::{LittleEndian, ByteOrder};
		Ok(LittleEndian::read_u32(&self.get(offset, 4).map_err(|_| UserError("Invalid attempt to read_primitive"))?))
	}
}

// TODO: this macro does not support `where` clauses and that seems somewhat tricky to add
#[wasmi_derive::derive_externals]
impl<'e, E: Externalities<Blake2Hasher> + 'e> FunctionExecutor<'e, E> {
	fn ext_print_utf8(&self, utf8_data: u32, utf8_len: u32) {
		if let Ok(utf8) = self.memory.get(utf8_data, utf8_len as usize) {
			if let Ok(message) = String::from_utf8(utf8) {
				println!("{}", message);
			}
		}
	}
	fn ext_print_hex(&self, data: u32, len: u32) {
		if let Ok(hex) = self.memory.get(data, len as usize) {
			println!("{}", HexDisplay::from(&hex));
		}
	}
	fn ext_print_num(&self, number: u64) {
		println!("{}", number);
	}
	fn ext_malloc(&mut self, size: u32) -> u32 {
		let r = self.heap.allocate(size);
		debug_trace!(target: "sr-io", "malloc {} bytes at {}", size, r);
		r
	}
	fn ext_free(&mut self, addr: u32) {
		self.heap.deallocate(addr);
		debug_trace!(target: "sr-io", "free {}", addr);
	}
	fn ext_set_storage(&mut self, key_data: u32, key_len: u32, value_data: u32, value_len: u32) -> Result<(), UserError> {
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_set_storage"))?;
		let value = self.memory.get(value_data, value_len as usize).map_err(|_| UserError("Invalid attempt to determine value in ext_set_storage"))?;
		if let Some(_preimage) = self.hash_lookup.get(&key) {
			debug_trace!(target: "wasm-trace", "*** Setting storage: %{} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&_preimage), HexDisplay::from(&value), HexDisplay::from(&key));
		} else {
			debug_trace!(target: "wasm-trace", "*** Setting storage:  {} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&key), HexDisplay::from(&value), HexDisplay::from(&key));
		}
		self.ext.set_storage(key, value);
		Ok(())
	}
	fn ext_set_child_storage(&mut self, storage_key_data: u32, storage_key_len: u32, key_data: u32, key_len: u32, value_data: u32, value_len: u32) -> Result<(), UserError> {
		let storage_key = self.memory.get(storage_key_data, storage_key_len as usize).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_set_child_storage"))?;
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_set_child_storage"))?;
		let value = self.memory.get(value_data, value_len as usize).map_err(|_| UserError("Invalid attempt to determine value in ext_set_child_storage"))?;
		if let Some(_preimage) = self.hash_lookup.get(&key) {
			debug_trace!(
				target: "wasm-trace", "*** Setting child storage: {} -> %{} -> {}   [k={}]",
				::primitives::hexdisplay::ascii_format(&storage_key),
				::primitives::hexdisplay::ascii_format(&_preimage),
				HexDisplay::from(&value),
				HexDisplay::from(&key)
			);
		} else {
			debug_trace!(
				target: "wasm-trace", "*** Setting child storage: {} ->  {} -> {}   [k={}]",
				::primitives::hexdisplay::ascii_format(&storage_key),
				::primitives::hexdisplay::ascii_format(&key),
				HexDisplay::from(&value),
				HexDisplay::from(&key)
			);
		}
		self.ext.set_child_storage(storage_key, key, value);
		Ok(())
	}
	fn ext_clear_child_storage(&mut self, storage_key_data: u32, storage_key_len: u32, key_data: u32, key_len: u32) -> Result<(), UserError> {
		let storage_key = self.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_clear_child_storage"))?;
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_clear_child_storage"))?;
		debug_trace!(target: "wasm-trace", "*** Clearing child storage: {} -> {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			}, HexDisplay::from(&key));
		self.ext.clear_child_storage(&storage_key, &key);
		Ok(())
	}
	fn ext_clear_storage(&mut self, key_data: u32, key_len: u32) -> Result<(), UserError> {
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_clear_storage"))?;
		debug_trace!(target: "wasm-trace", "*** Clearing storage: {}   [k={}]",
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			}, HexDisplay::from(&key));
		self.ext.clear_storage(&key);
		Ok(())
	}
	fn ext_exists_storage(&self, key_data: u32, key_len: u32) -> Result<u32, UserError> {
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_exists_storage"))?;
		Ok(if self.ext.exists_storage(&key) { 1 } else { 0 })
	}
	fn ext_exists_child_storage(&self, storage_key_data: u32, storage_key_len: u32, key_data: u32, key_len: u32) -> Result<u32, UserError> {
		let storage_key = self.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_exists_child_storage"))?;
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_exists_child_storage"))?;
		Ok(if self.ext.exists_child_storage(&storage_key, &key) { 1 } else { 0 })
	}
	fn ext_clear_prefix(&mut self, prefix_data: u32, prefix_len: u32) -> Result<(), UserError> {
		let prefix = self.memory.get(prefix_data, prefix_len as usize).map_err(|_| UserError("Invalid attempt to determine prefix in ext_clear_prefix"))?;
		self.ext.clear_prefix(&prefix);
		Ok(())
	}
	fn ext_kill_child_storage(&mut self, storage_key_data: u32, storage_key_len: u32) -> Result<(), UserError> {
		let storage_key = self.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_kill_child_storage"))?;
		self.ext.kill_child_storage(&storage_key);
		Ok(())
	}
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	fn ext_get_allocated_storage(&mut self, key_data: u32, key_len: u32, written_out: u32) -> Result<u32, UserError> {
		let key = self.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine key in ext_get_allocated_storage"))?;
		let maybe_value = self.ext.storage(&key);

		debug_trace!(target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			},
			if let Some(ref b) = maybe_value {
				&format!("{}", HexDisplay::from(b))
			} else {
				"<empty>"
			},
			HexDisplay::from(&key)
		);

		if let Some(value) = maybe_value {
			let offset = self.heap.allocate(value.len() as u32) as u32;
			self.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_get_allocated_storage"))?;
			self.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_get_allocated_storage"))?;
			Ok(offset)
		} else {
			self.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_get_allocated_storage"))?;
			Ok(0)
		}
	}
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	fn ext_get_allocated_child_storage(&mut self, storage_key_data: u32, storage_key_len: u32, key_data: u32, key_len: u32, written_out: u32) -> Result<u32, UserError> {
		let storage_key = self.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_get_allocated_child_storage"))?;
		let key = self.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine key in ext_get_allocated_child_storage"))?;
		let maybe_value = self.ext.child_storage(&storage_key, &key);

		debug_trace!(target: "wasm-trace", "*** Getting child storage: {} -> {} == {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			},
			if let Some(ref b) = maybe_value {
				&format!("{}", HexDisplay::from(b))
			} else {
				"<empty>"
			},
			HexDisplay::from(&key)
		);

		if let Some(value) = maybe_value {
			let offset = self.heap.allocate(value.len() as u32) as u32;
			self.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_get_allocated_child_storage"))?;
			self.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_get_allocated_child_storage"))?;
			Ok(offset)
		} else {
			self.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_get_allocated_child_storage"))?;
			Ok(0)
		}
	}
	// return u32::max_value() if no value exists for the key.
	fn ext_get_storage_into(&mut self, key_data: u32, key_len: u32, value_data: u32, value_len: u32, value_offset: u32) -> Result<u32, UserError> {
		let key = self.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to get key in ext_get_storage_into"))?;
		let maybe_value = self.ext.storage(&key);
		debug_trace!(target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			},
			if let Some(ref b) = maybe_value {
				&format!("{}", HexDisplay::from(b))
			} else {
				"<empty>"
			},
			HexDisplay::from(&key)
		);

		if let Some(value) = maybe_value {
			let value = &value[value_offset as usize..];
			let written = ::std::cmp::min(value_len as usize, value.len());
			self.memory.set(value_data, &value[..written]).map_err(|_| UserError("Invalid attempt to set value in ext_get_storage_into"))?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	}
	// return u32::max_value() if no value exists for the key.
	fn ext_get_child_storage_into(&mut self, storage_key_data: u32, storage_key_len: u32, key_data: u32, key_len: u32, value_data: u32, value_len: u32, value_offset: u32) -> Result<u32, UserError> {
		let storage_key = self.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_get_child_storage_into"))?;
		let key = self.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to get key in ext_get_child_storage_into"))?;
		let maybe_value = self.ext.child_storage(&storage_key, &key);
		debug_trace!(target: "wasm-trace", "*** Getting storage: {} -> {} == {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = self.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			},
			if let Some(ref b) = maybe_value {
				&format!("{}", HexDisplay::from(b))
			} else {
				"<empty>"
			},
			HexDisplay::from(&key)
		);

		if let Some(value) = maybe_value {
			let value = &value[value_offset as usize..];
			let written = ::std::cmp::min(value_len as usize, value.len());
			self.memory.set(value_data, &value[..written]).map_err(|_| UserError("Invalid attempt to set value in ext_get_child_storage_into"))?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	}
	fn ext_storage_root(&mut self, result: u32) -> Result<(), UserError> {
		let r = self.ext.storage_root();
		self.memory.set(result, r.as_ref()).map_err(|_| UserError("Invalid attempt to set memory in ext_storage_root"))?;
		Ok(())
	}
	fn ext_child_storage_root(&mut self, storage_key_data: u32, storage_key_len: u32, written_out: u32) -> Result<u32, UserError> {
		let storage_key = self.memory.get(storage_key_data, storage_key_len as usize).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_child_storage_root"))?;
		let r = self.ext.child_storage_root(&storage_key);
		if let Some(value) = r {
			let offset = self.heap.allocate(value.len() as u32) as u32;
			self.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_child_storage_root"))?;
			self.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_child_storage_root"))?;
			Ok(offset)
		} else {
			self.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_child_storage_root"))?;
			Ok(0)
		}
	}
	fn ext_storage_changes_root(&mut self, parent_hash_data: u32, parent_hash_len: u32, parent_number: u64, result: u32) -> Result<u32, UserError> {
		let mut parent_hash = H256::default();
		if parent_hash_len != parent_hash.as_ref().len() as u32 {
			return Err(UserError("Invalid parent_hash_len in ext_storage_changes_root").into());
		}
		let raw_parent_hash = self.memory.get(parent_hash_data, parent_hash_len as usize)
			.map_err(|_| UserError("Invalid attempt to get parent_hash in ext_storage_changes_root"))?;
		parent_hash.as_mut().copy_from_slice(&raw_parent_hash[..]);
		let r = self.ext.storage_changes_root(parent_hash, parent_number);
		if let Some(ref r) = r {
			self.memory.set(result, &r[..]).map_err(|_| UserError("Invalid attempt to set memory in ext_storage_changes_root"))?;
		}
		Ok(if r.is_some() { 1u32 } else { 0u32 })
	}
	fn ext_blake2_256_enumerated_trie_root(&mut self, values_data: u32, lens_data: u32, lens_len: u32, result: u32) -> Result<(), UserError> {
		let values = (0..lens_len)
			.map(|i| self.memory.read_primitive(lens_data + i * 4))
			.collect::<Result<Vec<u32>, UserError>>()?
			.into_iter()
			.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
			.map(|(offset, len)|
				self.memory.get(values_data + offset, len as usize)
					.map_err(|_| UserError("Invalid attempt to get memory in ext_blake2_256_enumerated_trie_root"))
			)
			.collect::<Result<Vec<_>, UserError>>()?;
		let r = ordered_trie_root::<Blake2Hasher, _, _>(values.into_iter());
		self.memory.set(result, &r[..]).map_err(|_| UserError("Invalid attempt to set memory in ext_blake2_256_enumerated_trie_root"))?;
		Ok(())
	}
	fn ext_chain_id(&self) -> Result<u64, UserError> {
		Ok(self.ext.chain_id())
	}
	fn ext_twox_128(&mut self, data: u32, len: u32, out: u32) -> Result<(), UserError> {
		let result = if len == 0 {
			let hashed = twox_128(&[0u8; 0]);
			debug_trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
			self.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = self.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get key in ext_twox_128"))?;
			let hashed_key = twox_128(&key);
			debug_trace!(target: "xxhash", "XXhash: {} -> {}",
				if let Ok(_skey) = ::std::str::from_utf8(&key) {
					_skey
				} else {
					&format!("{}", HexDisplay::from(&key))
				},
				HexDisplay::from(&hashed_key)
			);
			self.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		self.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_twox_128"))?;
		Ok(())
	}
	fn ext_twox_256(&mut self, data: u32, len: u32, out: u32) -> Result<(), UserError> {
		let result = if len == 0 {
			twox_256(&[0u8; 0])
		} else {
			twox_256(&self.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get data in ext_twox_256"))?)
		};
		self.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_twox_256"))?;
		Ok(())
	}
	fn ext_blake2_256(&mut self, data: u32, len: u32, out: u32) -> Result<(), UserError> {
		let result = if len == 0 {
			blake2_256(&[0u8; 0])
		} else {
			blake2_256(&self.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get data in ext_blake2_256"))?)
		};
		self.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_blake2_256"))?;
		Ok(())
	}
	fn ext_ed25519_verify(&mut self, msg_data: u32, msg_len: u32, sig_data: u32, pubkey_data: u32) -> Result<u32, UserError> {
		let mut sig = [0u8; 64];
		self.memory.get_into(sig_data, &mut sig[..]).map_err(|_| UserError("Invalid attempt to get signature in ext_ed25519_verify"))?;
		let mut pubkey = [0u8; 32];
		self.memory.get_into(pubkey_data, &mut pubkey[..]).map_err(|_| UserError("Invalid attempt to get pubkey in ext_ed25519_verify"))?;
		let msg = self.memory.get(msg_data, msg_len as usize).map_err(|_| UserError("Invalid attempt to get message in ext_ed25519_verify"))?;

		Ok(if ed25519::verify(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	}
	fn ext_sandbox_instantiate(
		&mut self,
		dispatch_thunk_idx: u32,
		wasm_ptr: u32,
		wasm_len: u32,
		imports_ptr: u32,
		imports_len: u32,
		state: u32
	) -> Result<u32, UserError> {
		let wasm = self.memory.get(wasm_ptr, wasm_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_instantiate: wasm"))?;
		let raw_env_def = self.memory.get(imports_ptr, imports_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_instantiate: imports"))?;

		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = self.table.as_ref()
				.ok_or_else(|| UserError("Runtime doesn't have a table; sandbox is unavailable"))?;
			table.get(dispatch_thunk_idx)
				.map_err(|_| UserError("dispatch_thunk_idx is out of the table bounds"))?
				.ok_or_else(|| UserError("dispatch_thunk_idx points on an empty table entry"))?
				.clone()
		};

		let instance_idx_or_err_code =
			match sandbox::instantiate(self, dispatch_thunk, &wasm, &raw_env_def, state) {
				Ok(instance_idx) => instance_idx,
				Err(sandbox::InstantiationError::StartTrapped) => sandbox_primitives::ERR_EXECUTION,
				Err(_) => sandbox_primitives::ERR_MODULE,
			};

		Ok(instance_idx_or_err_code as u32)
	}
	fn ext_sandbox_instance_teardown(&mut self, instance_idx: u32) -> Result<(), UserError> {
		self.sandbox_store.instance_teardown(instance_idx)?;
		Ok(())
	}
	fn ext_sandbox_invoke(&mut self, instance_idx: u32, export_ptr: u32, export_len: u32, args_ptr: u32, args_len: u32, return_val_ptr: u32, return_val_len: u32, state: u32) -> Result<u32, UserError> {
		use codec::{Decode, Encode};

		trace!(target: "sr-sandbox", "invoke, instance_idx={}", instance_idx);
		let export = self.memory.get(export_ptr, export_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_invoke: export"))
			.and_then(|b|
				String::from_utf8(b)
					.map_err(|_| UserError("export name should be a valid utf-8 sequence"))
			)?;

		// Deserialize arguments and convert them into wasmi types.
		let serialized_args = self.memory.get(args_ptr, args_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_invoke: args"))?;
		let args = Vec::<sandbox_primitives::TypedValue>::decode(&mut &serialized_args[..])
			.ok_or_else(|| UserError("Can't decode serialized arguments for the invocation"))?
			.into_iter()
			.map(Into::into)
			.collect::<Vec<_>>();

		let instance = self.sandbox_store.instance(instance_idx)?;
		let result = instance.invoke(&export, &args, self, state);

		match result {
			Ok(None) => Ok(sandbox_primitives::ERR_OK),
			Ok(Some(val)) => {
				// Serialize return value and write it back into the memory.
				sandbox_primitives::ReturnValue::Value(val.into()).using_encoded(|val| {
					if val.len() > return_val_len as usize {
						Err(UserError("Return value buffer is too small"))?;
					}
					self.memory
						.set(return_val_ptr, val)
						.map_err(|_| UserError("Return value buffer is OOB"))?;
					Ok(sandbox_primitives::ERR_OK)
				})
			}
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	}
	fn ext_sandbox_memory_new(&mut self, initial: u32, maximum: u32) -> Result<u32, UserError> {
		let mem_idx = self.sandbox_store.new_memory(initial, maximum)?;
		Ok(mem_idx)
	}
	fn ext_sandbox_memory_get(&mut self, memory_idx: u32, offset: u32, buf_ptr: u32, buf_len: u32) -> Result<u32, UserError> {
		let sandboxed_memory = self.sandbox_store.memory(memory_idx)?;

		match MemoryInstance::transfer(
			&sandboxed_memory,
			offset as usize,
			&self.memory,
			buf_ptr as usize,
			buf_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	}
	fn ext_sandbox_memory_set(&mut self, memory_idx: u32, offset: u32, val_ptr: u32, val_len: u32) -> Result<u32, UserError> {
		let sandboxed_memory = self.sandbox_store.memory(memory_idx)?;

		match MemoryInstance::transfer(
			&self.memory,
			val_ptr as usize,
			&sandboxed_memory,
			offset as usize,
			val_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	}
	fn ext_sandbox_memory_teardown(&mut self, memory_idx: u32) -> Result<(), UserError> {
		self.sandbox_store.memory_teardown(memory_idx)?;
		Ok(())
	}
}

/// Wasm rust executor for contracts.
///
/// Executes the provided code in a sandboxed wasm runtime.
#[derive(Debug, Clone)]
pub struct WasmExecutor {
}

impl WasmExecutor {

	/// Create a new instance.
	pub fn new() -> Self {
		WasmExecutor{}
	}

	/// Call a given method in the given code.
	/// This should be used for tests only.
	pub fn call<E: Externalities<Blake2Hasher>>(
		&self,
		ext: &mut E,
		heap_pages: usize,
		code: &[u8],
		method: &str,
		data: &[u8],
	) -> error::Result<Vec<u8>> {
		let module = ::wasmi::Module::from_buffer(code)?;
		let module = self.prepare_module(ext, heap_pages, &module)?;
		self.call_in_wasm_module(ext, &module, method, data)
	}

	fn get_mem_instance(module: &ModuleRef) -> error::Result<MemoryRef> {
		Ok(module
			.export_by_name("memory")
			.ok_or_else(|| Error::from(ErrorKind::InvalidMemoryReference))?
			.as_memory()
			.ok_or_else(|| Error::from(ErrorKind::InvalidMemoryReference))?
			.clone())
	}

	/// Call a given method in the given wasm-module runtime.
	pub fn call_in_wasm_module<E: Externalities<Blake2Hasher>>(
		&self,
		ext: &mut E,
		module_instance: &ModuleRef,
		method: &str,
		data: &[u8],
	) -> error::Result<Vec<u8>> {
		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(module_instance)?;
		let table: Option<TableRef> = module_instance
			.export_by_name("__indirect_function_table")
			.and_then(|e| e.as_table().cloned());

		let low = memory.lowest_used();
		let used_mem = memory.used_size();
		let mut fec = FunctionExecutor::new(memory.clone(), table, ext)?;
		let size = data.len() as u32;
		let offset = fec.heap.allocate(size);
		memory.set(offset, &data)?;

		let result = module_instance.invoke_export(
			method,
			&[
				I32(offset as i32),
				I32(size as i32)
			],
			&mut fec
		);
		let result = match result {
			Ok(Some(I64(r))) => {
				let offset = r as u32;
				let length = (r >> 32) as u32 as usize;
				memory.get(offset, length)
					.map_err(|_| ErrorKind::Runtime.into())
			},
			Ok(_) => Err(ErrorKind::InvalidReturn.into()),
			Err(e) => {
				trace!(target: "wasm-executor", "Failed to execute code with {} pages", memory.current_size().0);
				Err(e.into())
			},
		};

		// cleanup module instance for next use
		let new_low = memory.lowest_used();
		if new_low < low {
			memory.zero(new_low as usize, (low - new_low) as usize)?;
			memory.reset_lowest_used(low);
		}
		memory.with_direct_access_mut(|buf| buf.resize(used_mem.0, 0));
		result
	}

	/// Prepare module instance
	pub fn prepare_module<E: Externalities<Blake2Hasher>>(
		&self,
		ext: &mut E,
		heap_pages: usize,
		module: &Module,
		) -> error::Result<ModuleRef>
	{
		let resolver = FunctionExecutor::<E>::resolver();

		// start module instantiation. Don't run 'start' function yet.
		let intermediate_instance = ModuleInstance::new(
			module,
			&ImportsBuilder::new().with_resolver("env", &resolver)
		)?;

		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(intermediate_instance.not_started_instance())?;
		memory.grow(Pages(heap_pages)).map_err(|_| Error::from(ErrorKind::Runtime))?;
		let table: Option<TableRef> = intermediate_instance
			.not_started_instance()
			.export_by_name("__indirect_function_table")
			.and_then(|e| e.as_table().cloned());
		let mut fec = FunctionExecutor::new(memory.clone(), table, ext)?;

		// finish instantiation by running 'start' function (if any).
		Ok(intermediate_instance.run_start(&mut fec)?)
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use codec::Encode;
	use state_machine::TestExternalities;

	#[test]
	fn returning_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_empty_return", &[]).unwrap();
		assert_eq!(output, vec![0u8; 0]);
	}

	#[test]
	fn panicking_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_panic", &[]);
		assert!(output.is_err());

		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_conditional_panic", &[]);
		assert_eq!(output.unwrap(), vec![0u8; 0]);

		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_conditional_panic", &[2]);
		assert!(output.is_err());
	}

	#[test]
	fn storage_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"foo".to_vec(), b"bar".to_vec());
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_data_in", b"Hello world").unwrap();

		assert_eq!(output, b"all ok!".to_vec());

		let expected = TestExternalities::new(map![
			b"input".to_vec() => b"Hello world".to_vec(),
			b"foo".to_vec() => b"bar".to_vec(),
			b"baz".to_vec() => b"bar".to_vec()
		]);
		assert_eq!(ext, expected);
	}

	#[test]
	fn clear_prefix_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"aaa".to_vec(), b"1".to_vec());
		ext.set_storage(b"aab".to_vec(), b"2".to_vec());
		ext.set_storage(b"aba".to_vec(), b"3".to_vec());
		ext.set_storage(b"abb".to_vec(), b"4".to_vec());
		ext.set_storage(b"bbb".to_vec(), b"5".to_vec());
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");

		// This will clear all entries which prefix is "ab".
		let output = WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_clear_prefix", b"ab").unwrap();

		assert_eq!(output, b"all ok!".to_vec());

		let expected: TestExternalities<_> = map![
			b"aaa".to_vec() => b"1".to_vec(),
			b"aab".to_vec() => b"2".to_vec(),
			b"bbb".to_vec() => b"5".to_vec()
		];
		assert_eq!(expected, ext);
	}

	#[test]
	fn blake2_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_blake2_256", &[]).unwrap(),
			blake2_256(&b""[..]).encode()
		);
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_blake2_256", b"Hello world!").unwrap(),
			blake2_256(&b"Hello world!"[..]).encode()
		);
	}

	#[test]
	fn twox_256_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_twox_256", &[]).unwrap(),
			hex!("99e9d85137db46ef4bbea33613baafd56f963c64b1f3685a4eb4abd67ff6203a")
		);
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_twox_256", b"Hello world!").unwrap(),
			hex!("b27dfd7f223f177f2a13647b533599af0c07f68bda23d96d059da2b451a35a74")
		);
	}

	#[test]
	fn twox_128_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_twox_128", &[]).unwrap(),
			hex!("99e9d85137db46ef4bbea33613baafd5")
		);
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_twox_128", b"Hello world!").unwrap(),
			hex!("b27dfd7f223f177f2a13647b533599af")
		);
	}

	#[test]
	fn ed25519_verify_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		let key = ed25519::Pair::from_seed(&blake2_256(b"test"));
		let sig = key.sign(b"all ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(sig.as_ref());

		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![1]
		);

		let other_sig = key.sign(b"all is not ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(other_sig.as_ref());

		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_ed25519_verify", &calldata).unwrap(),
			vec![0]
		);
	}

	#[test]
	fn enumerated_trie_root_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_enumerated_trie_root", &[]).unwrap(),
			ordered_trie_root::<Blake2Hasher, _, _>(vec![b"zero".to_vec(), b"one".to_vec(), b"two".to_vec()].iter()).as_fixed_bytes().encode()
		);
	}


}
