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
use std::mem::ManuallyDrop;
use std::sync::{Mutex, MutexGuard};
use std::time::Instant;
use tiny_keccak;
use secp256k1;

use wasmi::{
	Module, ModuleInstance, MemoryInstance, MemoryRef, TableRef, ImportsBuilder, ModuleRef,
};
use wasmi::RuntimeValue::{I32, I64};
use wasmi::memory_units::{Bytes, Pages};
use state_machine::Externalities;
use crate::error::{Error, ErrorKind, Result};
use crate::wasm_utils::UserError;
use primitives::{blake2_256, twox_128, twox_256, ed25519, sr25519};
use primitives::hexdisplay::HexDisplay;
use primitives::sandbox as sandbox_primitives;
use primitives::{H256, Blake2Hasher};
use trie::ordered_trie_root;
use crate::sandbox;
use crate::allocator;
use log::trace;
use std::slice;
use std::rc::Rc;
use std::ptr;

#[cfg(feature="wasm-extern-trace")]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ( trace!( $( $x )* ) )
}
#[cfg(not(feature="wasm-extern-trace"))]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ()
}

lazy_static! {
	static ref FE_PTR: Mutex<
		Option<
			u64
		>
	> = Default::default();
}

unsafe impl Send for FunctionExecutor{}
unsafe impl Sync for FunctionExecutor{}

#[link(name = "node_runtime", kind = "dylib")]
extern "C" {
	static data_offset: *mut u8;

	fn node_runtime_init();

	fn Core_execute_block(offset: u32, size: u32) -> u64;
	fn Core_version(offset: u32, size: u32) -> u64;
	fn Core_authorities(offset: u32, size: u32) -> u64;
	fn Core_initialise_block(offset: u32, size: u32) -> u64;
	fn AuraApi_slot_duration(offset: u32, size: u32) -> u64;
	fn GrandpaApi_grandpa_authorities(offset: u32, size: u32) -> u64;
	fn BlockBuilder_check_inherents(offset: u32, size: u32) -> u64;
	fn GrandpaApi_grandpa_pending_change(offset: u32, size: u32) -> u64;
	fn BlockBuilder_apply_extrinsic(offset: u32, size: u32) -> u64;
	fn BlockBuilder_finalise_block(offset: u32, size: u32) -> u64;
	fn BlockBuilder_inherent_extrinsics(offset: u32, size: u32) -> u64;
	fn BlockBuilder_random_seed(offset: u32, size: u32) -> u64;
	fn TaggedTransactionQueue_validate_transaction(offset: u32, size: u32) -> u64;
	fn Metadata_metadata(offset: u32, size: u32) -> u64;
}

struct FunctionExecutor {
	sandbox_store: sandbox::Store,
	heap: allocator::FreeingBumpHeapAllocator,
	memory: MemoryRef,
	table: Option<TableRef>,
	ext: &'static mut Externalities<Blake2Hasher>,
	hash_lookup: HashMap<Vec<u8>, Vec<u8>>,
	from: u32,
}

use std::mem;
impl FunctionExecutor {
	fn new<'e, E: Externalities<Blake2Hasher>>(mem: MemoryRef, t: Option<TableRef>, e: &'e mut E, from: u32) -> Result<Self> {
		unsafe {
			node_runtime_init();
		}
		let current_size: Bytes = mem.current_size().into();
		let current_size = current_size.0 as u32;
		let used_size = mem.used_size().0 as u32;
		let heap_size = current_size - used_size;

		let offset = unsafe { data_offset };
		let data_offset_u = unsafe { data_offset } as u32;
		let data_offset_usize = unsafe { data_offset } as usize;

		Ok(FunctionExecutor {
			sandbox_store: sandbox::Store::new(),
			heap: allocator::FreeingBumpHeapAllocator::new(mem.used_size().0 as u32, heap_size),
			memory: mem,
			table: t,
			ext: unsafe { mem::transmute(e as &mut Externalities<Blake2Hasher>) },
			hash_lookup: HashMap::new(),
			from: from,
		})
	}
}

impl sandbox::SandboxCapabilities for FunctionExecutor {
	fn store(&self) -> &sandbox::Store {
		panic!("store");
		&self.sandbox_store
	}
	fn store_mut(&mut self) -> &mut sandbox::Store {
		panic!("store_mut");
		&mut self.sandbox_store
	}
	fn allocate(&mut self, len: u32) -> ::std::result::Result<u32, UserError> {
		panic!("allocate");
		self.heap.allocate(len)
	}
	fn deallocate(&mut self, ptr: u32) -> ::std::result::Result<(), UserError> {
		panic!("deallocate");
		self.heap.deallocate(ptr)
	}
	fn write_memory(&mut self, ptr: u32, data: &[u8]) -> ::std::result::Result<(), UserError> {
		panic!("write_memory");
		self.memory.set(ptr, data).map_err(|_| UserError("Invalid attempt to write_memory"))
	}
	fn read_memory(&self, ptr: u32, len: u32) -> ::std::result::Result<Vec<u8>, UserError> {
		panic!("read_memory");
		self.memory.get(ptr, len as usize).map_err(|_| UserError("Invalid attempt to write_memory"))
	}
}

trait WritePrimitive<T: Sized> {
	fn write_primitive(&self, offset: u32, t: T) -> ::std::result::Result<(), UserError>;
}

impl WritePrimitive<u32> for MemoryInstance {
	fn write_primitive(&self, offset: u32, t: u32) -> ::std::result::Result<(), UserError> {
		use byteorder::{LittleEndian, ByteOrder};
		let mut r = [0u8; 4];
		LittleEndian::write_u32(&mut r, t);
		self.set(offset, &r).map_err(|_| UserError("Invalid attempt to write_primitive"))
	}
}

trait ReadPrimitive<T: Sized> {
	fn read_primitive(&self, offset: u32) -> ::std::result::Result<T, UserError>;
}

impl ReadPrimitive<u32> for MemoryInstance {
	fn read_primitive(&self, offset: u32) -> ::std::result::Result<u32, UserError> {
		use byteorder::{LittleEndian, ByteOrder};
		Ok(LittleEndian::read_u32(&self.get(offset, 4).map_err(|_| UserError("Invalid attempt to read_primitive"))?))
	}
}

impl_function_executor!(this: FunctionExecutor,
	ext_print_utf8(utf8_data: *const u8, utf8_len: u32) => {
		panic!("ext_print_utf8");
		if let Ok(utf8) = this.memory.get(utf8_data, utf8_len as usize) {
			if let Ok(message) = String::from_utf8(utf8) {
				println!("{}", message);
			}
		}
		Ok(())
	},
	ext_print_hex(data: *const u8, len: u32) => {
		panic!("ext_print_hex");
		if let Ok(hex) = memory_get(data, len as usize) {
			println!("{}", HexDisplay::from(&hex));
		}
		Ok(())
	},
	ext_print_num(number: u64) => {
		panic!("ext_print_num");
		println!("{}", number);
		Ok(())
	},
	ext_malloc(size: usize) -> *mut u8 => {
		panic!("ext_malloc");
		debug_trace!(target: "sr-io", "malloc {} bytes at {}", size, r);
		Ok(0)
	},
	ext_free(addr: *mut u8) => {
		panic!("ext_free");
		debug_trace!(target: "sr-io", "free {}", addr);
		Ok(())
	},
	ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32) => {
		panic!("ext_set_storage");
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_set_storage"))?;
		let value = this.memory.get(value_data, value_len as usize).map_err(|_| UserError("Invalid attempt to determine value in ext_set_storage"))?;
		if let Some(_preimage) = this.hash_lookup.get(&key) {
			debug_trace!(target: "wasm-trace", "*** Setting storage: %{} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&_preimage), HexDisplay::from(&value), HexDisplay::from(&key));
		} else {
			debug_trace!(target: "wasm-trace", "*** Setting storage:  {} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&key), HexDisplay::from(&value), HexDisplay::from(&key));
		}
		this.ext.set_storage(key, value);
		Ok(())
	},
	ext_set_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32) => {
		panic!("ext_set_child_storage");
		let storage_key = this.memory.get(storage_key_data, storage_key_len as usize).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_set_child_storage"))?;
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_set_child_storage"))?;
		let value = this.memory.get(value_data, value_len as usize).map_err(|_| UserError("Invalid attempt to determine value in ext_set_child_storage"))?;
		if let Some(_preimage) = this.hash_lookup.get(&key) {
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
		this.ext.set_child_storage(storage_key, key, value);
		Ok(())
	},
	ext_clear_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32) => {
		panic!("ext_clear_child_storage");
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_clear_child_storage"))?;
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_clear_child_storage"))?;
		debug_trace!(target: "wasm-trace", "*** Clearing child storage: {} -> {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = this.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			}, HexDisplay::from(&key));
		this.ext.clear_child_storage(&storage_key, &key);
		Ok(())
	},
	ext_clear_storage(key_data: *const u8, key_len: u32) => {
		panic!("ext_clear_storage");
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_clear_storage"))?;
		debug_trace!(target: "wasm-trace", "*** Clearing storage: {}   [k={}]",
			if let Some(_preimage) = this.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			}, HexDisplay::from(&key));
		this.ext.clear_storage(&key);
		Ok(())
	},
	ext_exists_storage(key_data: *const u8, key_len: u32) -> u32 => {
		panic!("ext_exists_storage");
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_exists_storage"))?;
		Ok(if this.ext.exists_storage(&key) { 1 } else { 0 })
	},
	ext_exists_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32) -> u32 => {
		panic!("ext_exists_child_storage");
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_exists_child_storage"))?;
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to determine key in ext_exists_child_storage"))?;
		Ok(if this.ext.exists_child_storage(&storage_key, &key) { 1 } else { 0 })
	},
	ext_clear_prefix(prefix_data: *const u8, prefix_len: u32) => {
		panic!("ext_clear_prefix");
		let prefix = this.memory.get(prefix_data, prefix_len as usize).map_err(|_| UserError("Invalid attempt to determine prefix in ext_clear_prefix"))?;
		this.ext.clear_prefix(&prefix);
		Ok(())
	},
	ext_kill_child_storage(storage_key_data: *const u8, storage_key_len: u32) => {
		panic!("ext_kill_child_storage");
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_kill_child_storage"))?;
		this.ext.kill_child_storage(&storage_key);
		Ok(())
	},
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8 => {
		panic!("ext_get_allocated_storage");
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine key in ext_get_allocated_storage"))?;
		let maybe_value = this.ext.storage(&key);

		debug_trace!(target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
			if let Some(_preimage) = this.hash_lookup.get(&key) {
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
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_get_allocated_storage"))?;
			this.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_get_allocated_storage"))?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_get_allocated_storage"))?;
			Ok(0)
		}
	},
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	ext_get_allocated_child_storage(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8 => {
		panic!("ext_get_allocated_child_storage");
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_get_allocated_child_storage"))?;
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine key in ext_get_allocated_child_storage"))?;
		let maybe_value = this.ext.child_storage(&storage_key, &key);

		debug_trace!(target: "wasm-trace", "*** Getting child storage: {} -> {} == {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = this.hash_lookup.get(&key) {
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
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_get_allocated_child_storage"))?;
			this.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_get_allocated_child_storage"))?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_get_allocated_child_storage"))?;
			Ok(0)
		}
	},
	// return u32::max_value() if no value exists for the key.
	ext_get_storage_into(key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32 => {
		panic!("ext_get_storage_into");
		let key = this.memory.get(key_data, key_len as usize).map_err(|_| UserError("Invalid attempt to get key in ext_get_storage_into"))?;
		let maybe_value = this.ext.storage(&key);
		debug_trace!(target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
			if let Some(_preimage) = this.hash_lookup.get(&key) {
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
			this.memory.set(value_data, &value[..written]).map_err(|_| UserError("Invalid attempt to set value in ext_get_storage_into"))?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	// return u32::max_value() if no value exists for the key.
	ext_get_child_storage_into(storage_key_data: *const u8, storage_key_len: u32, key_data: *const u8, key_len: u32, value_data: *mut u8, value_len: u32, value_offset: u32) -> u32 => {
		panic!("ext_get_child_storage_into");
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_get_child_storage_into"))?;
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| UserError("Invalid attempt to get key in ext_get_child_storage_into"))?;
		let maybe_value = this.ext.child_storage(&storage_key, &key);
		debug_trace!(target: "wasm-trace", "*** Getting storage: {} -> {} == {}   [k={}]",
			::primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = this.hash_lookup.get(&key) {
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
			this.memory.set(value_data, &value[..written]).map_err(|_| UserError("Invalid attempt to set value in ext_get_child_storage_into"))?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	ext_storage_root(result: *mut u8) => {
		panic!("ext_storage_root");
		let r = this.ext.storage_root();
		this.memory.set(result, r.as_ref()).map_err(|_| UserError("Invalid attempt to set memory in ext_storage_root"))?;
		Ok(())
	},
	ext_child_storage_root(storage_key_data: *const u8, storage_key_len: u32, written_out: *mut u32) -> *mut u8 => {
		panic!("ext_child_storage_root");
		let storage_key = this.memory.get(storage_key_data, storage_key_len as usize).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_child_storage_root"))?;
		let r = this.ext.child_storage_root(&storage_key);
		if let Some(value) = r {
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value).map_err(|_| UserError("Invalid attempt to set memory in ext_child_storage_root"))?;
			this.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| UserError("Invalid attempt to write written_out in ext_child_storage_root"))?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| UserError("Invalid attempt to write failed written_out in ext_child_storage_root"))?;
			Ok(0)
		}
	},
	ext_storage_changes_root(parent_hash_data: *const u8, parent_hash_len: u32, parent_number: u64, result: *mut u8) -> u32 => {
		panic!("ext_storage_changes_root");
		/*
		let storage_key = this.memory.get(storage_key_data, storage_key_len as usize).map_err(|_| UserError("Invalid attempt to determine storage_key in ext_child_storage_root"))?;
		let mut parent_hash = H256::default();
		if parent_hash_len != parent_hash.as_ref().len() as u32 {
			return Err(UserError("Invalid parent_hash_len in ext_storage_changes_root").into());
		}
		let raw_parent_hash = this.memory.get(parent_hash_data, parent_hash_len as usize)
			.map_err(|_| UserError("Invalid attempt to get parent_hash in ext_storage_changes_root"))?;
		parent_hash.as_mut().copy_from_slice(&raw_parent_hash[..]);
		let r = this.ext.storage_changes_root(parent_hash, parent_number);
		if let Some(ref r) = r {
			this.memory.set(result, &r[..]).map_err(|_| UserError("Invalid attempt to set memory in ext_storage_changes_root"))?;
		}
		Ok(if r.is_some() { 1u32 } else { 0u32 })
		*/
	},
	ext_blake2_256_enumerated_trie_root(values_data: *const u8, lens_data: *const u32, lens_len: u32, result: *mut u8) => {
		panic!("ext_blake2_256_enumerated_trie_root");
		let values = (0..lens_len)
			.map(|i| this.memory.read_primitive(lens_data + i * 4))
			.collect::<::std::result::Result<Vec<u32>, UserError>>()?
			.into_iter()
			.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
			.map(|(offset, len)|
				this.memory.get(values_data + offset, len as usize)
					.map_err(|_| UserError("Invalid attempt to get memory in ext_blake2_256_enumerated_trie_root"))
			)
			.collect::<::std::result::Result<Vec<_>, UserError>>()?;
		let r = ordered_trie_root::<Blake2Hasher, _, _>(values.into_iter());
		this.memory.set(result, &r[..]).map_err(|_| UserError("Invalid attempt to set memory in ext_blake2_256_enumerated_trie_root"))?;
		Ok(())
	},
	ext_chain_id() -> u64 => {
		panic!("ext_chain_id");
		Ok(this.ext.chain_id())
	},
	ext_twox_128(data: *const u8, len: u32, out: *mut u8) => {
		panic!("ext_twox_128");
		let result: [u8; 16] = if len == 0 {
			let hashed = twox_128(&[0u8; 0]);
			debug_trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
			this.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = this.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get key in ext_twox_128"))?;
			let hashed_key = twox_128(&key);
			debug_trace!(target: "xxhash", "XXhash: {} -> {}",
				if let Ok(_skey) = ::std::str::from_utf8(&key) {
					_skey
				} else {
					&format!("{}", HexDisplay::from(&key))
				},
				HexDisplay::from(&hashed_key)
			);
			this.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		this.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_twox_128"))?;
		Ok(())
	},
	ext_twox_256(data: *const u8, len: u32, out: *mut u8) => {
		panic!("ext_twox_256");
		let result: [u8; 32] = if len == 0 {
			twox_256(&[0u8; 0])
		} else {
			twox_256(&this.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get data in ext_twox_256"))?)
		};
		this.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_twox_256"))?;
		Ok(())
	},
	ext_blake2_256(data: *const u8, len: u32, out: *mut u8) => {
		panic!("ext_blake2_256");
		let result: [u8; 32] = if len == 0 {
			blake2_256(&[0u8; 0])
		} else {
			blake2_256(&this.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get data in ext_blake2_256"))?)
		};
		this.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_blake2_256"))?;
		Ok(())
	},
	ext_keccak_256(data: *const u8, len: u32, out: *mut u8) => {
		panic!("ext_keccak_256");
		let result: [u8; 32] = if len == 0 {
			tiny_keccak::keccak256(&[0u8; 0])
		} else {
			tiny_keccak::keccak256(&this.memory.get(data, len as usize).map_err(|_| UserError("Invalid attempt to get data in ext_keccak_256"))?)
		};
		this.memory.set(out, &result).map_err(|_| UserError("Invalid attempt to set result in ext_keccak_256"))?;
		Ok(())
	},
	ext_ed25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32 => {
		panic!("ext_ed25519_verify");
		let mut sig = [0u8; 64];
		this.memory.get_into(sig_data, &mut sig[..]).map_err(|_| UserError("Invalid attempt to get signature in ext_ed25519_verify"))?;
		let mut pubkey = [0u8; 32];
		this.memory.get_into(pubkey_data, &mut pubkey[..]).map_err(|_| UserError("Invalid attempt to get pubkey in ext_ed25519_verify"))?;
		let msg = this.memory.get(msg_data, msg_len as usize).map_err(|_| UserError("Invalid attempt to get message in ext_ed25519_verify"))?;

		Ok(if ed25519::verify(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	},
	ext_sr25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32 => {
		panic!("ext_sr25519_verify");
		let mut sig = [0u8; 64];
		this.memory.get_into(sig_data, &mut sig[..]).map_err(|_| UserError("Invalid attempt to get signature in ext_sr25519_verify"))?;
		let mut pubkey = [0u8; 32];
		this.memory.get_into(pubkey_data, &mut pubkey[..]).map_err(|_| UserError("Invalid attempt to get pubkey in ext_sr25519_verify"))?;
		let msg = this.memory.get(msg_data, msg_len as usize).map_err(|_| UserError("Invalid attempt to get message in ext_sr25519_verify"))?;

		Ok(if sr25519::verify(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	},
	ext_secp256k1_ecdsa_recover(msg_data: *const u8, sig_data: *const u8, pubkey_data: *mut u8) -> u32 => {
		panic!("ext_secp256k1_ecdsa_recover");
		let mut sig = [0u8; 65];
		this.memory.get_into(sig_data, &mut sig[..]).map_err(|_| UserError("Invalid attempt to get signature in ext_secp256k1_ecdsa_recover"))?;
		let rs = match secp256k1::Signature::parse_slice(&sig[0..64]) {
			Ok(rs) => rs,
			_ => return Ok(1),
		};
		let v = match secp256k1::RecoveryId::parse(if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8) {
			Ok(v) => v,
			_ => return Ok(2),
		};


		let mut msg = [0u8; 32];
		this.memory.get_into(msg_data, &mut msg[..]).map_err(|_| UserError("Invalid attempt to get message in ext_secp256k1_ecdsa_recover"))?;

		let pubkey = match secp256k1::recover(&secp256k1::Message::parse(&msg), &rs, &v) {
			Ok(pk) => pk,
			_ => return Ok(3),
		};

		this.memory.set(pubkey_data, &pubkey.serialize()[1..65]).map_err(|_| UserError("Invalid attempt to set pubkey in ext_secp256k1_ecdsa_recover"))?;

		Ok(0)
	},
	ext_sandbox_instantiate(
		dispatch_thunk_idx: usize,
		wasm_ptr: *const u8,
		wasm_len: usize,
		imports_ptr: *const u8,
		imports_len: usize,
		state: usize
	) -> u32 => {
		panic!("ext_sandbox_instantiate");
        Ok(0)
        /*
		let wasm = this.memory.get(wasm_ptr, wasm_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_instantiate: wasm"))?;
		let raw_env_def = this.memory.get(imports_ptr, imports_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_instantiate: imports"))?;

		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = this.table.as_ref()
				.ok_or_else(|| UserError("Runtime doesn't have a table; sandbox is unavailable"))?;
			table.get(dispatch_thunk_idx)
				.map_err(|_| UserError("dispatch_thunk_idx is out of the table bounds"))?
				.ok_or_else(|| UserError("dispatch_thunk_idx points on an empty table entry"))?
				.clone()
		};

		let instance_idx_or_err_code =
			match sandbox::instantiate(this, dispatch_thunk, &wasm, &raw_env_def, state) {
				Ok(instance_idx) => instance_idx,
				Err(sandbox::InstantiationError::StartTrapped) => sandbox_primitives::ERR_EXECUTION,
				Err(_) => sandbox_primitives::ERR_MODULE,
			};

		Ok(instance_idx_or_err_code as u32)
        */
	},
	ext_sandbox_instance_teardown(instance_idx: u32) => {
		panic!("ext_sandbox_instance_teardown");
		this.sandbox_store.instance_teardown(instance_idx)?;
		Ok(())
	},
	ext_sandbox_invoke(instance_idx: u32, export_ptr: *const u8, export_len: usize, args_ptr: *const u8, args_len: usize, return_val_ptr: *const u8, return_val_len: usize, state: usize) -> u32 => {
		panic!("ext_sandbox_invoke");
		use parity_codec::{Decode, Encode};

		trace!(target: "sr-sandbox", "invoke, instance_idx={}", instance_idx);
		let export = this.memory.get(export_ptr, export_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_invoke: export"))
			.and_then(|b|
				String::from_utf8(b)
					.map_err(|_| UserError("export name should be a valid utf-8 sequence"))
			)?;

		// Deserialize arguments and convert them into wasmi types.
		let serialized_args = this.memory.get(args_ptr, args_len as usize)
			.map_err(|_| UserError("OOB while ext_sandbox_invoke: args"))?;
		let args = Vec::<sandbox_primitives::TypedValue>::decode(&mut &serialized_args[..])
			.ok_or_else(|| UserError("Can't decode serialized arguments for the invocation"))?
			.into_iter()
			.map(Into::into)
			.collect::<Vec<_>>();

		let instance = this.sandbox_store.instance(instance_idx)?;
		let result = instance.invoke(&export, &args, this, state);

		match result {
			Ok(None) => Ok(sandbox_primitives::ERR_OK),
			Ok(Some(val)) => {
				// Serialize return value and write it back into the memory.
				sandbox_primitives::ReturnValue::Value(val.into()).using_encoded(|val| {
					if val.len() > return_val_len as usize {
						Err(UserError("Return value buffer is too small"))?;
					}
					this.memory
						.set(return_val_ptr, val)
						.map_err(|_| UserError("Return value buffer is OOB"))?;
					Ok(sandbox_primitives::ERR_OK)
				})
			}
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	},
	ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32 => {
		panic!("ext_sandbox_memory_new");
		let mem_idx = this.sandbox_store.new_memory(initial, maximum)?;
		Ok(mem_idx)
	},
	ext_sandbox_memory_get(memory_idx: u32, offset: u32, buf_ptr: *mut u8, buf_len: u32) -> u32 => {
		panic!("ext_sandbox_memory_get");
		let sandboxed_memory = this.sandbox_store.memory(memory_idx)?;

		match MemoryInstance::transfer(
			&sandboxed_memory,
			offset as usize,
			&this.memory,
			buf_ptr as usize,
			buf_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	},
	ext_sandbox_memory_set(memory_idx: u32, offset: u32, val_ptr: *const u8, val_len: u32) -> u32 => {
		panic!("ext_sandbox_memory_set");
		let sandboxed_memory = this.sandbox_store.memory(memory_idx)?;

		match MemoryInstance::transfer(
			&this.memory,
			val_ptr as usize,
			&sandboxed_memory,
			offset as usize,
			val_len as usize,
		) {
			Ok(()) => Ok(sandbox_primitives::ERR_OK),
			Err(_) => Ok(sandbox_primitives::ERR_OUT_OF_BOUNDS),
		}
	},
	ext_sandbox_memory_teardown(memory_idx: u32) => {
		panic!("ext_sandbox_memory_teardown");
		this.sandbox_store.memory_teardown(memory_idx)?;
		Ok(())
	},
	=> <>
);

pub fn hash_lookup_insert(k: Vec<u8>, v: Vec<u8>) -> Option<Vec<u8>> {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	unsafe {
		return (*ptr).hash_lookup.insert(k, v);
	}
}

pub fn memory_get(offset: u32, size: usize) -> Result<Vec<u8>> {
	let offset = offset as u64;
	let slice : &[u8] = unsafe {
		let data_offset_u64 = unsafe { data_offset as u64 };
		let here: u64 = data_offset_u64 + offset;
		let here_ptr: u64 = data_offset_u64 + offset;
		let ptr = here_ptr as *mut _;
		slice::from_raw_parts_mut(ptr, size)
	};
	let result = Ok(slice.to_vec());
	result
}

/// Copy data from given offset in the memory into `target` slice.
pub fn memory_get_into(offset: u32, target: &mut [u8]) -> Result<()> {
	let size = target.len();
	let slice : &[u8] = unsafe {
		slice::from_raw_parts_mut(data_offset.offset(offset as isize), size)
	};

	target.copy_from_slice(slice);

	Ok(())
}

pub fn memory_set(offset: u32, value: &[u8]) -> Result<()> {
	if value.len() == 0 {
		return Ok(());
	}
	let offset = offset as u64;
	let data_offset_u64 = unsafe { data_offset as u64 };

	let here: u64 = data_offset_u64 + offset;
	let here_ptr: u64 = data_offset_u64 + offset;
	let ptr = here_ptr as *mut _;

	unsafe {
		let size = value.len();
		let slice = unsafe { slice::from_raw_parts_mut(ptr, size) };
		std::ptr::copy(value.as_ptr(), ptr, size);
	}
	Ok(())
}

pub fn memory_write_primitive(offset: u32, t: u32) -> ::std::result::Result<(), UserError> {
	use byteorder::{LittleEndian, ByteOrder};
	let mut r = [0u8; 4];
	LittleEndian::write_u32(&mut r, t);
	memory_set(offset, &r).map_err(|_| UserError("Invalid attempt to write_primitive"))
}

pub fn memory_read_primitive(offset: u32) -> ::std::result::Result<u32, UserError> {
	use byteorder::{LittleEndian, ByteOrder};
	Ok(LittleEndian::read_u32(&memory_get(offset, 4).unwrap()))
}


// Mangling is left in place, because of wasm2c limitations.
// The functions below are the functions from the `impl_function_executor`
// macro above -- with the exception that they access the global singleton.
#[no_mangle] extern "C" fn Z_envZ_ext_storage_changes_rootZ_iiiji(parent_hash_data: u32, parent_hash_len: u32, parent_number: u64, result: u32) -> u32 {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let mut parent_hash = H256::default();
	if parent_hash_len != parent_hash.as_ref().len() as u32 {
		return 0;
	}
	let raw_parent_hash = memory_get(parent_hash_data, parent_hash_len as usize).unwrap();
	parent_hash.as_mut().copy_from_slice(&raw_parent_hash[..]);
	let r = unsafe { (*ptr).ext.storage_changes_root(parent_hash, parent_number) };
	if let Some(ref r) = r {
		memory_set(result, &r[..]).unwrap();
	}
	if r.is_some() { 1u32 } else { 0u32 }
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_print_utf8Z_vii(utf8_data: u32, utf8_len: u32) {
	if let Ok(utf8) = memory_get(utf8_data, utf8_len as usize) {
		if let Ok(message) = String::from_utf8(utf8) {
			println!("{}", message);
		}
	}
}

#[no_mangle] extern fn Z_envZ_ext_print_hexZ_vii(data: u32, len: u32) {
	if let Ok(hex) = memory_get(data, len as usize) {
		println!("{}", HexDisplay::from(&hex));
	}
}

#[no_mangle] extern fn Z_envZ_ext_print_numZ_vj(number: u64) {
	println!("{}", number);
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_mallocZ_ii(size: u32) -> u32 {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	unsafe {
		let r = (*ptr).heap.allocate(size).unwrap();
		debug_trace!(target: "sr-io", "malloc {} bytes at {}", size, r);
		r
	}
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_freeZ_vi(addr: u32) {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	unsafe {
		return (*ptr).heap.deallocate(addr).unwrap();
	}
	debug_trace!(target: "sr-io", "free {}", addr);
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_set_storageZ_viiii(key_data: u32, key_len: u32, value_data: u32, value_len: u32) {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let key = memory_get(key_data, key_len as usize).unwrap();
	let value = memory_get(value_data, value_len as usize).unwrap();

	unsafe {
		if let Some(_preimage) = (*ptr).hash_lookup.get(&key) {
			debug_trace!(target: "wasm-trace", "*** Setting storage: %{} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&_preimage), HexDisplay::from(&value), HexDisplay::from(&key));
		} else {
			debug_trace!(target: "wasm-trace", "*** Setting storage:  {} -> {}   [k={}]", ::primitives::hexdisplay::ascii_format(&key), HexDisplay::from(&value), HexDisplay::from(&key));
		}
		(*ptr).ext.set_storage(key, value);
	}
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_clear_storageZ_vii(key_data: u32, key_len: u32) {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let key = memory_get(key_data, key_len as usize).unwrap();
	unsafe {
		debug_trace!(target: "wasm-trace", "*** Clearing storage: {}   [k={}]",
			if let Some(_preimage) = (*ptr).hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			}, HexDisplay::from(&key));

		(*ptr).ext.clear_storage(&key);
	}
	()
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_exists_storageZ_iii(key_data: u32, key_len: u32) -> u32 {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let key = memory_get(key_data, key_len as usize).unwrap();
	unsafe {
		if (*ptr).ext.exists_storage(&key) { 1 } else { 0 }
	}
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_clear_prefixZ_vii(prefix_data: u32, prefix_len: u32) {
	let prefix = memory_get(prefix_data, prefix_len as usize).unwrap();

	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	unsafe {
		(*ptr).ext.clear_prefix(&prefix);
	}
}

// return u32::max_value() if no value exists for the key.
#[no_mangle] pub extern "C" fn Z_envZ_ext_get_storage_intoZ_iiiiii(key_data: u32, key_len: u32, value_data: u32, value_len: u32, value_offset: u32) -> u32 {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let key = memory_get(key_data, key_len as usize).unwrap();
	let maybe_value = unsafe { (*ptr).ext.storage(&key) };

	debug_trace!(target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
		if let Some(_preimage) = hash_lookup.get(&key) {
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
		memory_set(value_data, &value[..written]).unwrap();
		written as u32
	} else {
		u32::max_value()
	}
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_storage_rootZ_vi(result: u32) {
	let guard = FE_PTR.lock().unwrap();
	let opt: u64 = guard.unwrap();
	let ptr = opt as *mut ManuallyDrop<Box<FunctionExecutor>>;

	let r = unsafe { (*ptr).ext.storage_root() };
	memory_set(result, r.as_ref()).unwrap();
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_blake2_256_enumerated_trie_rootZ_viiii(values_data: u32, lens_data: u32, lens_len: u32, result: u32) {
	let values = (0..lens_len)
		.map(|i| memory_read_primitive(lens_data + i * 4))
		.collect::<::std::result::Result<Vec<u32>, UserError>>().unwrap()
		.into_iter()
		.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
		.map(|(offset, len)|
			memory_get(values_data + offset, len as usize)
				.map_err(|_| UserError("Invalid attempt to get memory in ext_blake2_256_enumerated_trie_root"))
		)
		.collect::<::std::result::Result<Vec<_>, UserError>>().unwrap();
	let r = ordered_trie_root::<Blake2Hasher, _, _>(values.into_iter());

	memory_set(result, &r[..]).unwrap();
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_twox_128Z_viii(data: u32, len: u32, out: u32) {
	let result = if len == 0 {
		let hashed = twox_128(&[0u8; 0]);
		debug_trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
		hash_lookup_insert(hashed.to_vec(), vec![]);
		hashed
	} else {
		let key = memory_get(data, len as usize).unwrap();
		let hashed_key = twox_128(&key);
		let f = format!("{}", HexDisplay::from(&key));
		debug_trace!(target: "xxhash", "XXhash: {} -> {}",
			if let Ok(_skey) = ::std::str::from_utf8(&key) {
				_skey
			} else {
				&f
			},
			HexDisplay::from(&hashed_key)
		);

		hash_lookup_insert(hashed_key.to_vec(), key);
		hashed_key
	};

	memory_set(out, &result).unwrap();
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_twox_256Z_viii(data: u32, len: u32, out: u32)  {
	let result = if len == 0 {
		twox_256(&[0u8; 0])
	} else {
		twox_256(&memory_get(data, len as usize).unwrap())
	};
	memory_set(out, &result).unwrap();
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_blake2_256Z_viii(data: u32, len: u32, out: u32) {
	let result = if len == 0 {
		blake2_256(&[0u8; 0])
	} else {
		blake2_256(&memory_get(data, len as usize).unwrap())
	};
	memory_set(out, &result).unwrap();
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_ed25519_verifyZ_iiiii(msg_data: u32, msg_len: u32, sig_data: u32, pubkey_data: u32) -> u32 {
	panic!("Z_envZ_ext_ed25519_verifyZ_iiiii not implemented");
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_instantiateZ_iiiiiii(
	dispatch_thunk_idx: u32,
	wasm_ptr: u32,
	wasm_len: u32,
	imports_ptr: u32,
	imports_len: u32,
	state: u32
) -> u32 {
	panic!("Z_envZ_ext_sandbox_instantiateZ_iiiiiii missing");
	0u32
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_instance_teardownZ_vi(instance_idx: u32) {
	panic!("Z_envZ_ext_sandbox_instance_teardownZ_vi not implemented");
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_invokeZ_iiiiiiiii(instance_idx: u32, export_ptr: u32, export_len: u32, args_ptr: u32, args_len: u32, return_val_ptr: u32, return_val_len: u32, state: u32) -> u32 {
	panic!("Z_envZ_ext_sandbox_invokeZ_iiiiiiiii not implemented");
	0u32
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_memory_newZ_iii(initial: u32, maximum: u32) -> u32 {
	panic!("Z_envZ_ext_sandbox_memory_newZ_iii missing");
	0u32
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_memory_getZ_iiiii(memory_idx: u32, offset: u32, buf_ptr: *mut u8, buf_len: u32) -> u32 {
	panic!("Z_envZ_ext_sandbox_memory_getZ_iiiii missing");
	0u32
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_memory_setZ_iiiii(memory_idx: u32, offset: u32, val_ptr: *const u8, val_len: u32) -> u32 {
	panic!("Z_envZ_ext_sandbox_memory_setZ_iiiii missing");
	0u32
}

#[no_mangle] pub extern "C" fn Z_envZ_ext_sandbox_memory_teardownZ_vi(memory_idx: u32) {
	panic!("Z_envZ_ext_sandbox_memory_teardownZ_vi missing");
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
		) -> Result<Vec<u8>> {
		let module = ::wasmi::Module::from_buffer(code)?;
		let module = self.prepare_module(ext, heap_pages, &module)?;
		self.call_in_wasm_module(ext, &module, method, data)
	}

	fn get_mem_instance(module: &ModuleRef) -> Result<MemoryRef> {
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
	) -> Result<Vec<u8>> {
		let start = Instant::now();

		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(module_instance)?;
		let table: Option<TableRef> = module_instance
			.export_by_name("__indirect_function_table")
			.and_then(|e| e.as_table().cloned());

		let low = memory.lowest_used();
		let used_mem = memory.used_size();

		let mut inner = FunctionExecutor::new(memory.clone(), table, ext, 1)?;
		let mut fec = ManuallyDrop::new(Box::new(inner));
		let ptr = &fec;
		let bx = &fec;
		let ptr: *const ManuallyDrop<Box<FunctionExecutor>> = &*bx;
		let ptr = ptr as usize as u64;
		*FE_PTR.lock().unwrap() = Some(ptr);

		let size: u32 = data.len() as u32;
		let offset: u32 = Z_envZ_ext_mallocZ_ii(size);

		memory_set(offset, &data)?;

		let result: u64 = match method {
			"Core_execute_block" => unsafe { Core_execute_block(offset as u32, size as u32) },
			"Core_version" => unsafe { Core_version(offset as u32, size as u32) },
			"Core_authorities" => unsafe { Core_authorities(offset as u32, size as u32) },
			"Core_initialise_block" => unsafe { Core_initialise_block(offset as u32, size as u32) },
			"AuraApi_slot_duration" => unsafe { AuraApi_slot_duration(offset as u32, size as u32) },
			"GrandpaApi_grandpa_authorities" => unsafe { GrandpaApi_grandpa_authorities(offset as u32, size as u32) },
			"BlockBuilder_check_inherents" => unsafe { BlockBuilder_check_inherents(offset as u32, size as u32) },
			"GrandpaApi_grandpa_pending_change" => unsafe { GrandpaApi_grandpa_pending_change(offset as u32, size as u32) },
			"BlockBuilder_apply_extrinsic" => unsafe { BlockBuilder_apply_extrinsic(offset as u32, size as u32) },
			"BlockBuilder_finalise_block" => unsafe { BlockBuilder_finalise_block(offset as u32, size as u32) },
			"BlockBuilder_inherent_extrinsics" => unsafe { BlockBuilder_inherent_extrinsics(offset as u32, size as u32) },
			"BlockBuilder_random_seed" => unsafe { BlockBuilder_random_seed(offset as u32, size as u32) },
			"TaggedTransactionQueue_validate_transaction" => unsafe { TaggedTransactionQueue_validate_transaction(offset as u32, size as u32) },
			"Metadata_metadata" => unsafe { Metadata_metadata(offset as u32, size as u32) },

			&_ => { panic!("method {:?} missing", method) },
		};

		let r = result;
		let offset = r as u32;
		let length = (r >> 32) as u32;
		let length = length as usize;

		let result = memory_get(offset, length);

		// cleanup module instance for next use
		/*
		let new_low = memory.lowest_used();
		if new_low < low {
			memory.zero(new_low as usize, (low - new_low) as usize)?;
			memory.reset_lowest_used(low);
		}
		memory.with_direct_access_mut(|buf| buf.resize(used_mem.0, 0));
		*/

		let duration = start.elapsed();
		eprintln!("duration for {:?}: {:?}µs", method, duration.as_micros());
		result
	}

	/// Prepare module instance
	pub fn prepare_module<E: Externalities<Blake2Hasher>>(
		&self,
		ext: &mut E,
		heap_pages: usize,
		module: &Module,
		) -> Result<ModuleRef>
	{
		// start module instantiation. Don't run 'start' function yet.
		let intermediate_instance = ModuleInstance::new(
			module,
			&ImportsBuilder::new()
			.with_resolver("env", FunctionExecutor::resolver())
			)?;

		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(intermediate_instance.not_started_instance())?;
		memory.grow(Pages(heap_pages)).map_err(|_| Error::from(ErrorKind::Runtime))?;
		let table: Option<TableRef> = intermediate_instance
			.not_started_instance()
			.export_by_name("__indirect_function_table")
			.and_then(|e| e.as_table().cloned());

		let mut inner = FunctionExecutor::new(memory.clone(), table, ext, 1)?;
		let mut fec = ManuallyDrop::new(Box::new(inner));

		let ptr = &fec;
		let bx = &fec;
		let ptr: *const ManuallyDrop<Box<FunctionExecutor>> = &*bx;
		let ptr = ptr as usize as u64;
		*FE_PTR.lock().unwrap() = Some(ptr);

		// finish instantiation by running 'start' function (if any).
		Ok(intermediate_instance.run_start(&mut **fec)?)
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use parity_codec::Encode;
	use state_machine::TestExternalities;
	use hex_literal::{hex, hex_impl};
	use primitives::map;

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
	fn sr25519_verify_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		let key = sr25519::Pair::from_seed(&blake2_256(b"test"));
		let sig = key.sign(b"all ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(sig.as_ref());

		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_sr25519_verify", &calldata).unwrap(),
			vec![1]
		);

		let other_sig = key.sign(b"all is not ok!");
		let mut calldata = vec![];
		calldata.extend_from_slice(key.public().as_ref());
		calldata.extend_from_slice(other_sig.as_ref());

		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_sr25519_verify", &calldata).unwrap(),
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
