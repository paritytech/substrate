// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, convert::TryFrom, str};
use tiny_keccak;
use secp256k1;

use wasmi::{
	Module, ModuleInstance, MemoryInstance, MemoryRef, TableRef, ImportsBuilder, ModuleRef,
	memory_units::Pages, RuntimeValue::{I32, I64, self},
};
use state_machine::{Externalities, ChildStorageKey};
use crate::error::{Error, Result};
use primitives::{blake2_128, blake2_256, twox_64, twox_128, twox_256, ed25519, sr25519, Pair};
use primitives::offchain;
use primitives::hexdisplay::HexDisplay;
use primitives::sandbox as sandbox_primitives;
use primitives::{H256, Blake2Hasher};
use trie::ordered_trie_root;
use crate::sandbox;
use crate::allocator;
use log::trace;

#[cfg(feature="wasm-extern-trace")]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ( trace!( $( $x )* ) )
}
#[cfg(not(feature="wasm-extern-trace"))]
macro_rules! debug_trace {
	( $( $x:tt )* ) => ()
}

struct FunctionExecutor<'e, E: Externalities<Blake2Hasher> + 'e> {
	sandbox_store: sandbox::Store,
	heap: allocator::FreeingBumpHeapAllocator,
	memory: MemoryRef,
	table: Option<TableRef>,
	ext: &'e mut E,
	hash_lookup: HashMap<Vec<u8>, Vec<u8>>,
}

impl<'e, E: Externalities<Blake2Hasher>> FunctionExecutor<'e, E> {
	fn new(m: MemoryRef, t: Option<TableRef>, e: &'e mut E) -> Result<Self> {
		Ok(FunctionExecutor {
			sandbox_store: sandbox::Store::new(),
			heap: allocator::FreeingBumpHeapAllocator::new(m.clone()),
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
	fn allocate(&mut self, len: u32) -> Result<u32> {
		self.heap.allocate(len)
	}
	fn deallocate(&mut self, ptr: u32) -> Result<()> {
		self.heap.deallocate(ptr)
	}
	fn write_memory(&mut self, ptr: u32, data: &[u8]) -> Result<()> {
		self.memory.set(ptr, data).map_err(Into::into)
	}
	fn read_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>> {
		self.memory.get(ptr, len as usize).map_err(Into::into)
	}
}

trait WritePrimitive<T: Sized> {
	fn write_primitive(&self, offset: u32, t: T) -> Result<()>;
}

impl WritePrimitive<u32> for MemoryInstance {
	fn write_primitive(&self, offset: u32, t: u32) -> Result<()> {
		use byteorder::{LittleEndian, ByteOrder};
		let mut r = [0u8; 4];
		LittleEndian::write_u32(&mut r, t);
		self.set(offset, &r).map_err(Into::into)
	}
}

trait ReadPrimitive<T: Sized> {
	fn read_primitive(&self, offset: u32) -> Result<T>;
}

impl ReadPrimitive<u32> for MemoryInstance {
	fn read_primitive(&self, offset: u32) -> Result<u32> {
		use byteorder::{LittleEndian, ByteOrder};
		let result = self.get(offset, 4)?;
		Ok(LittleEndian::read_u32(&result))
	}
}

fn deadline_to_timestamp(deadline: u64) -> Option<offchain::Timestamp> {
	if deadline == 0 {
		None
	} else {
		Some(offchain::Timestamp::from_unix_millis(deadline))
	}
}

fn u32_to_key(key: u32) -> std::result::Result<Option<offchain::CryptoKeyId>, ()> {
	if key > u16::max_value() as u32 {
		Err(())
	} else if key == 0 {
		Ok(None)
	} else {
		Ok(Some(offchain::CryptoKeyId(key as u16)))
	}
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
	ext_malloc(size: usize) -> *mut u8 => {
		let r = this.heap.allocate(size)?;
		debug_trace!(target: "sr-io", "malloc {} bytes at {}", size, r);
		Ok(r)
	},
	ext_free(addr: *mut u8) => {
		this.heap.deallocate(addr)?;
		debug_trace!(target: "sr-io", "free {}", addr);
		Ok(())
	},
	ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32) => {
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_set_storage")?;
		let value = this.memory.get(value_data, value_len as usize)
			.map_err(|_| "Invalid attempt to determine value in ext_set_storage")?;
		if let Some(_preimage) = this.hash_lookup.get(&key) {
			debug_trace!(
				target: "wasm-trace",
				"*** Setting storage: %{} -> {}   [k={}]",
				primitives::hexdisplay::ascii_format(&_preimage),
				HexDisplay::from(&value),
				HexDisplay::from(&key),
			);
		} else {
			debug_trace!(
				target: "wasm-trace",
				"*** Setting storage:  {} -> {}   [k={}]",
				primitives::hexdisplay::ascii_format(&key),
				HexDisplay::from(&value),
				HexDisplay::from(&key),
			);
		}
		this.ext.set_storage(key, value);
		Ok(())
	},
	ext_set_child_storage(
		storage_key_data: *const u8,
		storage_key_len: u32,
		key_data: *const u8,
		key_len: u32,
		value_data: *const u8,
		value_len: u32
	) => {
		let storage_key = this.memory.get(storage_key_data, storage_key_len as usize)
			.map_err(|_| "Invalid attempt to determine storage_key in ext_set_child_storage")?;
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_set_child_storage")?;
		let value = this.memory.get(value_data, value_len as usize)
			.map_err(|_| "Invalid attempt to determine value in ext_set_child_storage")?;
		if let Some(_preimage) = this.hash_lookup.get(&key) {
			debug_trace!(
				target: "wasm-trace", "*** Setting child storage: {} -> %{} -> {}   [k={}]",
				primitives::hexdisplay::ascii_format(&storage_key),
				primitives::hexdisplay::ascii_format(&_preimage),
				HexDisplay::from(&value),
				HexDisplay::from(&key)
			);
		} else {
			debug_trace!(
				target: "wasm-trace", "*** Setting child storage: {} ->  {} -> {}   [k={}]",
				primitives::hexdisplay::ascii_format(&storage_key),
				primitives::hexdisplay::ascii_format(&key),
				HexDisplay::from(&value),
				HexDisplay::from(&key)
			);
		}
		let storage_key = ChildStorageKey::from_vec(storage_key)
			.ok_or_else(|| "ext_set_child_storage: child storage key is invalid")?;
		this.ext.set_child_storage(storage_key, key, value);
		Ok(())
	},
	ext_clear_child_storage(
		storage_key_data: *const u8,
		storage_key_len: u32,
		key_data: *const u8,
		key_len: u32
	) => {
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| "Invalid attempt to determine storage_key in ext_clear_child_storage")?;
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_clear_child_storage")?;
		debug_trace!(
			target: "wasm-trace", "*** Clearing child storage: {} -> {}   [k={}]",
			primitives::hexdisplay::ascii_format(&storage_key),
			if let Some(_preimage) = this.hash_lookup.get(&key) {
				format!("%{}", primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", primitives::hexdisplay::ascii_format(&key))
			},
			HexDisplay::from(&key)
		);
		let storage_key = ChildStorageKey::from_vec(storage_key)
			.ok_or_else(|| "ext_clear_child_storage: child storage key is not valid")?;

		this.ext.clear_child_storage(storage_key, &key);
		Ok(())
	},
	ext_clear_storage(key_data: *const u8, key_len: u32) => {
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_clear_storage")?;
		debug_trace!(
			target: "wasm-trace", "*** Clearing storage: {}   [k={}]",
			if let Some(_preimage) = this.hash_lookup.get(&key) {
				format!("%{}", ::primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", ::primitives::hexdisplay::ascii_format(&key))
			},
			HexDisplay::from(&key)
		);
		this.ext.clear_storage(&key);
		Ok(())
	},
	ext_exists_storage(key_data: *const u8, key_len: u32) -> u32 => {
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_exists_storage")?;
		Ok(if this.ext.exists_storage(&key) { 1 } else { 0 })
	},
	ext_exists_child_storage(
		storage_key_data: *const u8,
		storage_key_len: u32,
		key_data: *const u8,
		key_len: u32
	) -> u32 => {
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| "Invalid attempt to determine storage_key in ext_exists_child_storage")?;
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to determine key in ext_exists_child_storage")?;
		let storage_key = ChildStorageKey::from_vec(storage_key)
			.ok_or_else(|| "ext_exists_child_storage: child storage key is not valid")?;
		Ok(if this.ext.exists_child_storage(storage_key, &key) { 1 } else { 0 })
	},
	ext_clear_prefix(prefix_data: *const u8, prefix_len: u32) => {
		let prefix = this.memory.get(prefix_data, prefix_len as usize)
			.map_err(|_| "Invalid attempt to determine prefix in ext_clear_prefix")?;
		this.ext.clear_prefix(&prefix);
		Ok(())
	},
	ext_kill_child_storage(storage_key_data: *const u8, storage_key_len: u32) => {
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| "Invalid attempt to determine storage_key in ext_kill_child_storage")?;
		let storage_key = ChildStorageKey::from_vec(storage_key)
			.ok_or_else(|| "ext_exists_child_storage: child storage key is not valid")?;
		this.ext.kill_child_storage(storage_key);
		Ok(())
	},
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8 => {
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| "Invalid attempt to determine key in ext_get_allocated_storage")?;
		let maybe_value = this.ext.storage(&key);

		debug_trace!(
			target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
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
			HexDisplay::from(&key),
		);

		if let Some(value) = maybe_value {
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value)
				.map_err(|_| "Invalid attempt to set memory in ext_get_allocated_storage")?;
			this.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| "Invalid attempt to write written_out in ext_get_allocated_storage")?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| "Invalid attempt to write failed written_out in ext_get_allocated_storage")?;
			Ok(0)
		}
	},
	// return 0 and place u32::max_value() into written_out if no value exists for the key.
	ext_get_allocated_child_storage(
		storage_key_data: *const u8,
		storage_key_len: u32,
		key_data: *const u8,
		key_len: u32,
		written_out: *mut u32
	) -> *mut u8 => {
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| "Invalid attempt to determine storage_key in ext_get_allocated_child_storage")?;
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| "Invalid attempt to determine key in ext_get_allocated_child_storage")?;

		let maybe_value = {
			let storage_key = ChildStorageKey::from_slice(&storage_key)
				.ok_or_else(|| "ext_get_allocated_child_storage: child storage key is not valid")?;
			this.ext.child_storage(storage_key, &key)
		};

		debug_trace!(
			target: "wasm-trace", "*** Getting child storage: {} -> {} == {}   [k={}]",
			primitives::hexdisplay::ascii_format(&storage_key),
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
			HexDisplay::from(&key),
		);

		if let Some(value) = maybe_value {
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value)
				.map_err(|_| "Invalid attempt to set memory in ext_get_allocated_child_storage")?;
			this.memory.write_primitive(written_out, value.len() as u32)
				.map_err(|_| "Invalid attempt to write written_out in ext_get_allocated_child_storage")?;
			Ok(offset)
		} else {
			this.memory.write_primitive(written_out, u32::max_value())
				.map_err(|_| "Invalid attempt to write failed written_out in ext_get_allocated_child_storage")?;
			Ok(0)
		}
	},
	// return u32::max_value() if no value exists for the key.
	ext_get_storage_into(
		key_data: *const u8,
		key_len: u32,
		value_data: *mut u8,
		value_len: u32,
		value_offset: u32
	) -> u32 => {
		let key = this.memory.get(key_data, key_len as usize)
			.map_err(|_| "Invalid attempt to get key in ext_get_storage_into")?;
		let maybe_value = this.ext.storage(&key);
		debug_trace!(
			target: "wasm-trace", "*** Getting storage: {} == {}   [k={}]",
			if let Some(_preimage) = this.hash_lookup.get(&key) {
				format!("%{}", primitives::hexdisplay::ascii_format(&_preimage))
			} else {
				format!(" {}", primitives::hexdisplay::ascii_format(&key))
			},
			if let Some(ref b) = maybe_value {
				&format!("{}", HexDisplay::from(b))
			} else {
				"<empty>"
			},
			HexDisplay::from(&key),
		);

		if let Some(value) = maybe_value {
			let value = &value[value_offset as usize..];
			let written = std::cmp::min(value_len as usize, value.len());
			this.memory.set(value_data, &value[..written])
				.map_err(|_| "Invalid attempt to set value in ext_get_storage_into")?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	// return u32::max_value() if no value exists for the key.
	ext_get_child_storage_into(
		storage_key_data: *const u8,
		storage_key_len: u32,
		key_data: *const u8,
		key_len: u32,
		value_data: *mut u8,
		value_len: u32,
		value_offset: u32
	) -> u32 => {
		let storage_key = this.memory.get(
			storage_key_data,
			storage_key_len as usize
		).map_err(|_| "Invalid attempt to determine storage_key in ext_get_child_storage_into")?;
		let key = this.memory.get(
			key_data,
			key_len as usize
		).map_err(|_| "Invalid attempt to get key in ext_get_child_storage_into")?;

		let maybe_value = {
			let storage_key = ChildStorageKey::from_slice(&*storage_key)
				.ok_or_else(|| "ext_get_child_storage_into: child storage key is not valid")?;
			this.ext.child_storage(storage_key, &key)
		};
		debug_trace!(
			target: "wasm-trace", "*** Getting storage: {} -> {} == {}   [k={}]",
			primitives::hexdisplay::ascii_format(&storage_key),
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
			HexDisplay::from(&key),
		);

		if let Some(value) = maybe_value {
			let value = &value[value_offset as usize..];
			let written = ::std::cmp::min(value_len as usize, value.len());
			this.memory.set(value_data, &value[..written])
				.map_err(|_| "Invalid attempt to set value in ext_get_child_storage_into")?;
			Ok(written as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	ext_storage_root(result: *mut u8) => {
		let r = this.ext.storage_root();
		this.memory.set(result, r.as_ref())
			.map_err(|_| "Invalid attempt to set memory in ext_storage_root")?;
		Ok(())
	},
	ext_child_storage_root(
		storage_key_data: *const u8,
		storage_key_len: u32,
		written_out: *mut u32
	) -> *mut u8 => {
		let storage_key = this.memory.get(storage_key_data, storage_key_len as usize)
			.map_err(|_| "Invalid attempt to determine storage_key in ext_child_storage_root")?;
		let storage_key = ChildStorageKey::from_slice(&*storage_key)
			.ok_or_else(|| "ext_child_storage_root: child storage key is not valid")?;
		let value = this.ext.child_storage_root(storage_key);

		let offset = this.heap.allocate(value.len() as u32)? as u32;
		this.memory.set(offset, &value)
			.map_err(|_| "Invalid attempt to set memory in ext_child_storage_root")?;
		this.memory.write_primitive(written_out, value.len() as u32)
			.map_err(|_| "Invalid attempt to write written_out in ext_child_storage_root")?;
		Ok(offset)
	},
	ext_storage_changes_root(parent_hash_data: *const u8, parent_hash_len: u32, result: *mut u8) -> u32 => {
		let mut parent_hash = H256::default();
		if parent_hash_len != parent_hash.as_ref().len() as u32 {
			return Err("Invalid parent_hash_len in ext_storage_changes_root".into());
		}
		let raw_parent_hash = this.memory.get(parent_hash_data, parent_hash_len as usize)
			.map_err(|_| "Invalid attempt to get parent_hash in ext_storage_changes_root")?;
		parent_hash.as_mut().copy_from_slice(&raw_parent_hash[..]);
		let r = this.ext.storage_changes_root(parent_hash)
			.map_err(|_| "Invaid parent_hash passed to ext_storage_changes_root")?;
		if let Some(r) = r {
			this.memory.set(result, &r[..])
				.map_err(|_| "Invalid attempt to set memory in ext_storage_changes_root")?;
			Ok(1)
		} else {
			Ok(0)
		}
	},
	ext_blake2_256_enumerated_trie_root(
		values_data: *const u8,
		lens_data: *const u32,
		lens_len: u32,
		result: *mut u8
	) => {
		let values = (0..lens_len)
			.map(|i| this.memory.read_primitive(lens_data + i * 4))
			.collect::<Result<Vec<u32>>>()?
			.into_iter()
			.scan(0u32, |acc, v| { let o = *acc; *acc += v; Some((o, v)) })
			.map(|(offset, len)|
				this.memory.get(values_data + offset, len as usize)
					.map_err(|_|
						Error::from(
							"Invalid attempt to get memory in ext_blake2_256_enumerated_trie_root"
						)
					)
			)
			.collect::<Result<Vec<_>>>()?;
		let r = ordered_trie_root::<Blake2Hasher, _, _>(values.into_iter());
		this.memory.set(result, &r[..])
			.map_err(|_| "Invalid attempt to set memory in ext_blake2_256_enumerated_trie_root")?;
		Ok(())
	},
	ext_chain_id() -> u64 => {
		Ok(this.ext.chain_id())
	},
	ext_twox_64(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 8] = if len == 0 {
			let hashed = twox_64(&[0u8; 0]);
			debug_trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
			this.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get key in ext_twox_64")?;
			let hashed_key = twox_64(&key);

			debug_trace!(
				target: "xxhash", "XXhash: {} -> {}",
				if let Ok(_skey) = str::from_utf8(&key) {
					_skey
				} else {
					&format!("{}", HexDisplay::from(&key))
				},
				HexDisplay::from(&hashed_key),
			);

			this.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		this.memory.set(out, &result).map_err(|_| "Invalid attempt to set result in ext_twox_64")?;
		Ok(())
	},
	ext_twox_128(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 16] = if len == 0 {
			let hashed = twox_128(&[0u8; 0]);
			debug_trace!(target: "xxhash", "XXhash: '' -> {}", HexDisplay::from(&hashed));
			this.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get key in ext_twox_128")?;
			let hashed_key = twox_128(&key);
			debug_trace!(
				target: "xxhash", "XXhash: {} -> {}",
				&if let Ok(_skey) = str::from_utf8(&key) {
					*_skey
				} else {
					format!("{}", HexDisplay::from(&key))
				},
				HexDisplay::from(&hashed_key),
			);
			this.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		this.memory.set(out, &result)
			.map_err(|_| "Invalid attempt to set result in ext_twox_128")?;
		Ok(())
	},
	ext_twox_256(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 32] = if len == 0 {
			twox_256(&[0u8; 0])
		} else {
			let mem = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get data in ext_twox_256")?;
			twox_256(&mem)
		};
		this.memory.set(out, &result).map_err(|_| "Invalid attempt to set result in ext_twox_256")?;
		Ok(())
	},
	ext_blake2_128(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 16] = if len == 0 {
			let hashed = blake2_128(&[0u8; 0]);
			this.hash_lookup.insert(hashed.to_vec(), vec![]);
			hashed
		} else {
			let key = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get key in ext_blake2_128")?;
			let hashed_key = blake2_128(&key);
			this.hash_lookup.insert(hashed_key.to_vec(), key);
			hashed_key
		};

		this.memory.set(out, &result)
			.map_err(|_| "Invalid attempt to set result in ext_blake2_128")?;
		Ok(())
	},
	ext_blake2_256(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 32] = if len == 0 {
			blake2_256(&[0u8; 0])
		} else {
			let mem = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get data in ext_blake2_256")?;
			blake2_256(&mem)
		};
		this.memory.set(out, &result).map_err(|_| "Invalid attempt to set result in ext_blake2_256")?;
		Ok(())
	},
	ext_keccak_256(data: *const u8, len: u32, out: *mut u8) => {
		let result: [u8; 32] = if len == 0 {
			tiny_keccak::keccak256(&[0u8; 0])
		} else {
			let mem = this.memory.get(data, len as usize)
				.map_err(|_| "Invalid attempt to get data in ext_keccak_256")?;
			tiny_keccak::keccak256(&mem)
		};
		this.memory.set(out, &result).map_err(|_| "Invalid attempt to set result in ext_keccak_256")?;
		Ok(())
	},
	ext_ed25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32 => {
		let mut sig = [0u8; 64];
		this.memory.get_into(sig_data, &mut sig[..])
			.map_err(|_| "Invalid attempt to get signature in ext_ed25519_verify")?;
		let mut pubkey = [0u8; 32];
		this.memory.get_into(pubkey_data, &mut pubkey[..])
			.map_err(|_| "Invalid attempt to get pubkey in ext_ed25519_verify")?;
		let msg = this.memory.get(msg_data, msg_len as usize)
			.map_err(|_| "Invalid attempt to get message in ext_ed25519_verify")?;

		Ok(if ed25519::Pair::verify_weak(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	},
	ext_sr25519_verify(msg_data: *const u8, msg_len: u32, sig_data: *const u8, pubkey_data: *const u8) -> u32 => {
		let mut sig = [0u8; 64];
		this.memory.get_into(sig_data, &mut sig[..])
			.map_err(|_| "Invalid attempt to get signature in ext_sr25519_verify")?;
		let mut pubkey = [0u8; 32];
		this.memory.get_into(pubkey_data, &mut pubkey[..])
			.map_err(|_| "Invalid attempt to get pubkey in ext_sr25519_verify")?;
		let msg = this.memory.get(msg_data, msg_len as usize)
			.map_err(|_| "Invalid attempt to get message in ext_sr25519_verify")?;

		Ok(if sr25519::Pair::verify_weak(&sig, &msg, &pubkey) {
			0
		} else {
			5
		})
	},
	ext_secp256k1_ecdsa_recover(msg_data: *const u8, sig_data: *const u8, pubkey_data: *mut u8) -> u32 => {
		let mut sig = [0u8; 65];
		this.memory.get_into(sig_data, &mut sig[..])
			.map_err(|_| "Invalid attempt to get signature in ext_secp256k1_ecdsa_recover")?;
		let rs = match secp256k1::Signature::parse_slice(&sig[0..64]) {
			Ok(rs) => rs,
			_ => return Ok(1),
		};
		let v = match secp256k1::RecoveryId::parse(if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8) {
			Ok(v) => v,
			_ => return Ok(2),
		};


		let mut msg = [0u8; 32];
		this.memory.get_into(msg_data, &mut msg[..])
			.map_err(|_| "Invalid attempt to get message in ext_secp256k1_ecdsa_recover")?;

		let pubkey = match secp256k1::recover(&secp256k1::Message::parse(&msg), &rs, &v) {
			Ok(pk) => pk,
			_ => return Ok(3),
		};

		this.memory.set(pubkey_data, &pubkey.serialize()[1..65])
			.map_err(|_| "Invalid attempt to set pubkey in ext_secp256k1_ecdsa_recover")?;

		Ok(0)
	},
	ext_submit_transaction(msg_data: *const u8, len: u32) -> u32 => {
		let extrinsic = this.memory.get(msg_data, len as usize)
			.map_err(|_| "OOB while ext_submit_transaction: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.submit_transaction(extrinsic))
			.ok_or_else(|| "Calling unavailable API ext_submit_transaction: wasm")?;

		Ok(if res.is_ok() { 0 } else { 1 })
	},
	ext_new_crypto_key(crypto: u32) -> u32 => {
		let kind = offchain::CryptoKind::try_from(crypto)
			.map_err(|_| "crypto kind OOB while ext_new_crypto_key: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.new_crypto_key(kind))
			.ok_or_else(|| "Calling unavailable API ext_new_crypto_key: wasm")?;

		match res {
			Ok(key_id) => Ok(key_id.0 as u32),
			Err(()) => Ok(u32::max_value()),
		}
	},
	ext_encrypt(key: u32, data: *const u8, data_len: u32, msg_len: *mut u32) -> *mut u8 => {
		let key = u32_to_key(key)
			.map_err(|_| "Key OOB while ext_encrypt: wasm")?;
		let message = this.memory.get(data, data_len as usize)
			.map_err(|_| "OOB while ext_encrypt: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.encrypt(key, &*message))
			.ok_or_else(|| "Calling unavailable API ext_encrypt: wasm")?;

		let (offset,len) = match res {
			Ok(encrypted) => {
				let len = encrypted.len() as u32;
				let offset = this.heap.allocate(len)? as u32;
				this.memory.set(offset, &encrypted)
					.map_err(|_| "Invalid attempt to set memory in ext_encrypt")?;
				(offset, len)
			},
			Err(()) => (0, u32::max_value()),
		};

		this.memory.write_primitive(msg_len, len)
			.map_err(|_| "Invalid attempt to write msg_len in ext_encrypt")?;

		Ok(offset)
	},
	ext_decrypt(key: u32, data: *const u8, data_len: u32, msg_len: *mut u32) -> *mut u8 => {
		let key = u32_to_key(key)
			.map_err(|_| "Key OOB while ext_decrypt: wasm")?;
		let message = this.memory.get(data, data_len as usize)
			.map_err(|_| "OOB while ext_decrypt: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.decrypt(key, &*message))
			.ok_or_else(|| "Calling unavailable API ext_decrypt: wasm")?;

		let (offset,len) = match res {
			Ok(decrypted) => {
				let len = decrypted.len() as u32;
				let offset = this.heap.allocate(len)? as u32;
				this.memory.set(offset, &decrypted)
					.map_err(|_| "Invalid attempt to set memory in ext_decrypt")?;
				(offset, len)
			},
			Err(()) => (0, u32::max_value()),
		};

		this.memory.write_primitive(msg_len, len)
			.map_err(|_| "Invalid attempt to write msg_len in ext_decrypt")?;

		Ok(offset)
	},
	ext_sign(key: u32, data: *const u8, data_len: u32, sig_data_len: *mut u32) -> *mut u8  => {
		let key = u32_to_key(key)
			.map_err(|_| "Key OOB while ext_sign: wasm")?;
		let message = this.memory.get(data, data_len as usize)
			.map_err(|_| "OOB while ext_sign: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.sign(key, &*message))
			.ok_or_else(|| "Calling unavailable API ext_sign: wasm")?;

		let (offset,len) = match res {
			Ok(signature) => {
				let len = signature.len() as u32;
				let offset = this.heap.allocate(len)? as u32;
				this.memory.set(offset, &signature)
					.map_err(|_| "Invalid attempt to set memory in ext_sign")?;
				(offset, len)
			},
			Err(()) => (0, u32::max_value()),
		};

		this.memory.write_primitive(sig_data_len, len)
			.map_err(|_| "Invalid attempt to write sig_data_len in ext_sign")?;

		Ok(offset)
	},
	ext_verify(
		key: u32,
		msg: *const u8,
		msg_len: u32,
		signature: *const u8,
		signature_len: u32
	) -> u32 => {
		let key = u32_to_key(key)
			.map_err(|_| "Key OOB while ext_verify: wasm")?;
		let message = this.memory.get(msg, msg_len as usize)
			.map_err(|_| "OOB while ext_verify: wasm")?;
		let signature = this.memory.get(signature, signature_len as usize)
			.map_err(|_| "OOB while ext_verify: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.verify(key, &*message, &*signature))
			.ok_or_else(|| "Calling unavailable API ext_verify: wasm")?;

		match res {
			Ok(true) => Ok(0),
			Ok(false) => Ok(1),
			Err(()) => Ok(u32::max_value()),
		}
	},
	ext_timestamp() -> u64 => {
		let timestamp = this.ext.offchain()
			.map(|api| api.timestamp())
			.ok_or_else(|| "Calling unavailable API ext_timestamp: wasm")?;
		Ok(timestamp.unix_millis())
	},
	ext_sleep_until(deadline: u64) => {
		this.ext.offchain()
			.map(|api| api.sleep_until(offchain::Timestamp::from_unix_millis(deadline)))
			.ok_or_else(|| "Calling unavailable API ext_sleep_until: wasm")?;
		Ok(())
	},
	ext_random_seed(seed_data: *mut u8) => {
		// NOTE the runtime as assumptions about seed size.
		let seed: [u8; 32] = this.ext.offchain()
			.map(|api| api.random_seed())
			.ok_or_else(|| "Calling unavailable API ext_random_seed: wasm")?;

		this.memory.set(seed_data, &seed)
			.map_err(|_| "Invalid attempt to set value in ext_random_seed")?;
		Ok(())
	},
	ext_local_storage_set(key: *const u8, key_len: u32, value: *const u8, value_len: u32) => {
		let key = this.memory.get(key, key_len as usize)
			.map_err(|_| "OOB while ext_local_storage_set: wasm")?;
		let value = this.memory.get(value, value_len as usize)
			.map_err(|_| "OOB while ext_local_storage_set: wasm")?;

		this.ext.offchain()
			.map(|api| api.local_storage_set(&key, &value))
			.ok_or_else(|| "Calling unavailable API ext_local_storage_set: wasm")?;

		Ok(())
	},
	ext_local_storage_get(key: *const u8, key_len: u32, value_len: *mut u32) -> *mut u8 => {
		let key = this.memory.get(key, key_len as usize)
			.map_err(|_| "OOB while ext_local_storage_get: wasm")?;

		let maybe_value = this.ext.offchain()
			.map(|api| api.local_storage_get(&key))
			.ok_or_else(|| "Calling unavailable API ext_local_storage_get: wasm")?;

		let (offset, len) = if let Some(value) = maybe_value {
			let offset = this.heap.allocate(value.len() as u32)? as u32;
			this.memory.set(offset, &value)
				.map_err(|_| "Invalid attempt to set memory in ext_local_storage_get")?;
			(offset, value.len() as u32)
		} else {
			(0, u32::max_value())
		};

		this.memory.write_primitive(value_len, len)
			.map_err(|_| "Invalid attempt to write value_len in ext_local_storage_get")?;

		Ok(offset)
	},
	ext_http_request_start(
		method: *const u8,
		method_len: u32,
		url: *const u8,
		url_len: u32,
		meta: *const u8,
		meta_len: u32
	) -> u32 => {
		let method = this.memory.get(method, method_len as usize)
			.map_err(|_| "OOB while ext_http_request_start: wasm")?;
		let url = this.memory.get(url, url_len as usize)
			.map_err(|_| "OOB while ext_http_request_start: wasm")?;
		let meta = this.memory.get(meta, meta_len as usize)
			.map_err(|_| "OOB while ext_http_request_start: wasm")?;

		let method_str = str::from_utf8(&method)
			.map_err(|_| "invalid str while ext_http_request_start: wasm")?;
		let url_str = str::from_utf8(&url)
			.map_err(|_| "invalid str while ext_http_request_start: wasm")?;

		let id = this.ext.offchain()
			.map(|api| api.http_request_start(method_str, url_str, &*meta))
			.ok_or_else(|| "Calling unavailable API ext_http_request_start: wasm")?;

		if let Ok(id) = id {
			Ok(id.0 as u32)
		} else {
			Ok(u32::max_value())
		}
	},
	ext_http_request_add_header(
		request_id: u32,
		name: *const u8,
		name_len: u32,
		value: *const u8,
		value_len: u32
	) -> u32 => {
		let name = this.memory.get(name, name_len as usize)
			.map_err(|_| "OOB while ext_http_request_add_header: wasm")?;
		let value = this.memory.get(value, value_len as usize)
			.map_err(|_| "OOB while ext_http_request_add_header: wasm")?;

		let name_str = str::from_utf8(&name)
			.map_err(|_| "Invalid str while ext_http_request_add_header: wasm")?;
		let value_str = str::from_utf8(&value)
			.map_err(|_| "Invalid str while ext_http_request_add_header: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.http_request_add_header(
				offchain::HttpRequestId(request_id as u16),
				&name_str,
				&value_str,
			))
			.ok_or_else(|| "Calling unavailable API ext_http_request_add_header: wasm")?;

		Ok(if res.is_ok() { 0 } else { 1 })
	},
	ext_http_request_write_body(
		request_id: u32,
		chunk: *const u8,
		chunk_len: u32,
		deadline: u64
	) -> u32 => {
		let chunk = this.memory.get(chunk, chunk_len as usize)
			.map_err(|_| "OOB while ext_http_request_write_body: wasm")?;

		let res = this.ext.offchain()
			.map(|api| api.http_request_write_body(
				offchain::HttpRequestId(request_id as u16),
				&chunk,
				deadline_to_timestamp(deadline)
			))
			.ok_or_else(|| "Calling unavailable API ext_http_request_write_body: wasm")?;

		Ok(match res {
			Ok(()) => 0,
			Err(e) => e as u8 as u32,
		})
	},
	ext_http_response_wait(
		ids: *const u32,
		ids_len: u32,
		statuses: *mut u32,
		deadline: u64
	) => {
		let ids = (0..ids_len)
			.map(|i|
				 this.memory.read_primitive(ids + i * 4)
					.map(|id: u32| offchain::HttpRequestId(id as u16))
					.map_err(|_| "OOB while ext_http_response_wait: wasm")
			)
			.collect::<::std::result::Result<Vec<_>, _>>()?;

		let res = this.ext.offchain()
			.map(|api| api.http_response_wait(&ids, deadline_to_timestamp(deadline)))
			.ok_or_else(|| "Calling unavailable API ext_http_response_wait: wasm")?
			.into_iter()
			.map(|status| status.into())
			.enumerate()
			// make sure to take up to `ids_len` to avoid exceeding the mem.
			.take(ids_len as usize);

		for (i, status) in res {
			this.memory.write_primitive(statuses + i as u32 * 4, status)
				.map_err(|_| "Invalid attempt to set memory in ext_http_response_wait")?;
		}

		Ok(())
	},
	ext_http_response_headers(
		request_id: u32,
		written_out: *mut u32
	) -> *mut u8 => {
		use parity_codec::Encode;

		let headers = this.ext.offchain()
			.map(|api| api.http_response_headers(offchain::HttpRequestId(request_id as u16)))
			.ok_or_else(|| "Calling unavailable API ext_http_response_headers: wasm")?;

		let encoded = headers.encode();
		let len = encoded.len() as u32;
		let offset = this.heap.allocate(len)? as u32;
		this.memory.set(offset, &encoded)
			.map_err(|_| "Invalid attempt to set memory in ext_http_response_headers")?;
		this.memory.write_primitive(written_out, len)
			.map_err(|_| "Invalid attempt to write written_out in ext_http_response_headers")?;

		Ok(offset)
	},
	ext_http_response_read_body(
		request_id: u32,
		buffer: *mut u8,
		buffer_len: u32,
		deadline: u64
	) -> u32 => {
		let mut internal_buffer = Vec::with_capacity(buffer_len as usize);
		internal_buffer.resize(buffer_len as usize, 0);

		let res = this.ext.offchain()
			.map(|api| api.http_response_read_body(
				offchain::HttpRequestId(request_id as u16),
				&mut internal_buffer,
				deadline_to_timestamp(deadline),
			))
			.ok_or_else(|| "Calling unavailable API ext_http_response_read_body: wasm")?;

		Ok(match res {
			Ok(read) => {
				this.memory.set(buffer, &internal_buffer[..read])
					.map_err(|_| "Invalid attempt to set memory in ext_http_response_read_body")?;

				read as u32
			},
			Err(err) => {
				u32::max_value() - err as u8 as u32 + 1
			}
		})
	},
	ext_sandbox_instantiate(
		dispatch_thunk_idx: usize,
		wasm_ptr: *const u8,
		wasm_len: usize,
		imports_ptr: *const u8,
		imports_len: usize,
		state: usize
	) -> u32 => {
		let wasm = this.memory.get(wasm_ptr, wasm_len as usize)
			.map_err(|_| "OOB while ext_sandbox_instantiate: wasm")?;
		let raw_env_def = this.memory.get(imports_ptr, imports_len as usize)
			.map_err(|_| "OOB while ext_sandbox_instantiate: imports")?;

		// Extract a dispatch thunk from instance's table by the specified index.
		let dispatch_thunk = {
			let table = this.table.as_ref()
				.ok_or_else(|| "Runtime doesn't have a table; sandbox is unavailable")?;
			table.get(dispatch_thunk_idx)
				.map_err(|_| "dispatch_thunk_idx is out of the table bounds")?
				.ok_or_else(|| "dispatch_thunk_idx points on an empty table entry")?
				.clone()
		};

		let instance_idx_or_err_code =
			match sandbox::instantiate(this, dispatch_thunk, &wasm, &raw_env_def, state) {
				Ok(instance_idx) => instance_idx,
				Err(sandbox::InstantiationError::StartTrapped) => sandbox_primitives::ERR_EXECUTION,
				Err(_) => sandbox_primitives::ERR_MODULE,
			};

		Ok(instance_idx_or_err_code as u32)
	},
	ext_sandbox_instance_teardown(instance_idx: u32) => {
		this.sandbox_store.instance_teardown(instance_idx)?;
		Ok(())
	},
	ext_sandbox_invoke(
		instance_idx: u32,
		export_ptr: *const u8,
		export_len: usize,
		args_ptr: *const u8,
		args_len: usize,
		return_val_ptr: *const u8,
		return_val_len: usize,
		state: usize
	) -> u32 => {
		use parity_codec::{Decode, Encode};

		trace!(target: "sr-sandbox", "invoke, instance_idx={}", instance_idx);
		let export = this.memory.get(export_ptr, export_len as usize)
			.map_err(|_| "OOB while ext_sandbox_invoke: export")
			.and_then(|b|
				String::from_utf8(b)
					.map_err(|_| "Export name should be a valid utf-8 sequence")
			)?;

		// Deserialize arguments and convert them into wasmi types.
		let serialized_args = this.memory.get(args_ptr, args_len as usize)
			.map_err(|_| "OOB while ext_sandbox_invoke: args")?;
		let args = Vec::<sandbox_primitives::TypedValue>::decode(&mut &serialized_args[..])
			.ok_or_else(|| "Can't decode serialized arguments for the invocation")?
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
						Err("Return value buffer is too small")?;
					}
					this.memory
						.set(return_val_ptr, val)
						.map_err(|_| "Return value buffer is OOB")?;
					Ok(sandbox_primitives::ERR_OK)
				})
			}
			Err(_) => Ok(sandbox_primitives::ERR_EXECUTION),
		}
	},
	ext_sandbox_memory_new(initial: u32, maximum: u32) -> u32 => {
		let mem_idx = this.sandbox_store.new_memory(initial, maximum)?;
		Ok(mem_idx)
	},
	ext_sandbox_memory_get(memory_idx: u32, offset: u32, buf_ptr: *mut u8, buf_len: u32) -> u32 => {
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
		this.sandbox_store.memory_teardown(memory_idx)?;
		Ok(())
	},
	=> <'e, E: Externalities<Blake2Hasher> + 'e>
);

/// Wasm rust executor for contracts.
///
/// Executes the provided code in a sandboxed wasm runtime.
#[derive(Debug, Clone)]
pub struct WasmExecutor;

impl WasmExecutor {

	/// Create a new instance.
	pub fn new() -> Self {
		WasmExecutor
	}

	/// Call a given method in the given code.
	///
	/// Signature of this method needs to be `(I32, I32) -> I64`.
	///
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

	/// Call a given method with a custom signature in the given code.
	///
	/// This should be used for tests only.
	pub fn call_with_custom_signature<
		E: Externalities<Blake2Hasher>,
		F: FnOnce(&mut dyn FnMut(&[u8]) -> Result<u32>) -> Result<Vec<RuntimeValue>>,
		FR: FnOnce(Option<RuntimeValue>, &MemoryRef) -> Result<Option<R>>,
		R,
	>(
		&self,
		ext: &mut E,
		heap_pages: usize,
		code: &[u8],
		method: &str,
		create_parameters: F,
		filter_result: FR,
	) -> Result<R> {
		let module = wasmi::Module::from_buffer(code)?;
		let module = self.prepare_module(ext, heap_pages, &module)?;
		self.call_in_wasm_module_with_custom_signature(
			ext,
			&module,
			method,
			create_parameters,
			filter_result,
		)
	}

	fn get_mem_instance(module: &ModuleRef) -> Result<MemoryRef> {
		Ok(module
			.export_by_name("memory")
			.ok_or_else(|| Error::InvalidMemoryReference)?
			.as_memory()
			.ok_or_else(|| Error::InvalidMemoryReference)?
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
		self.call_in_wasm_module_with_custom_signature(
			ext,
			module_instance,
			method,
			|alloc| {
				let offset = alloc(data)?;
				Ok(vec![I32(offset as i32), I32(data.len() as i32)])
			},
			|res, memory| {
				if let Some(I64(r)) = res {
					let offset = r as u32;
					let length = (r as u64 >> 32) as usize;
					memory.get(offset, length).map_err(|_| Error::Runtime).map(Some)
				} else {
					Ok(None)
				}
			}
		)
	}

	/// Call a given method in the given wasm-module runtime.
	fn call_in_wasm_module_with_custom_signature<
		E: Externalities<Blake2Hasher>,
		F: FnOnce(&mut dyn FnMut(&[u8]) -> Result<u32>) -> Result<Vec<RuntimeValue>>,
		FR: FnOnce(Option<RuntimeValue>, &MemoryRef) -> Result<Option<R>>,
		R,
	>(
		&self,
		ext: &mut E,
		module_instance: &ModuleRef,
		method: &str,
		create_parameters: F,
		filter_result: FR,
	) -> Result<R> {
		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(module_instance)?;
		let table: Option<TableRef> = module_instance
			.export_by_name("__indirect_function_table")
			.and_then(|e| e.as_table().cloned());

		let low = memory.lowest_used();
		let used_mem = memory.used_size();
		let mut fec = FunctionExecutor::new(memory.clone(), table, ext)?;
		let parameters = create_parameters(&mut |data: &[u8]| {
			let offset = fec.heap.allocate(data.len() as u32)?;
			memory.set(offset, &data)?;
			Ok(offset)
		})?;

		let result = module_instance.invoke_export(
			method,
			&parameters,
			&mut fec
		);
		let result = match result {
			Ok(val) => match filter_result(val, &memory)? {
				Some(val) => Ok(val),
				None => Err(Error::InvalidReturn),
			},
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
		) -> Result<ModuleRef>
	{
		// start module instantiation. Don't run 'start' function yet.
		let intermediate_instance = ModuleInstance::new(
			module,
			&ImportsBuilder::new()
			.with_resolver("env", FunctionExecutor::<E>::resolver())
		)?;

		// extract a reference to a linear memory, optional reference to a table
		// and then initialize FunctionExecutor.
		let memory = Self::get_mem_instance(intermediate_instance.not_started_instance())?;
		memory.grow(Pages(heap_pages)).map_err(|_| Error::Runtime)?;
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

	use parity_codec::Encode;

	use state_machine::TestExternalities as CoreTestExternalities;
	use hex_literal::hex;
	use primitives::map;

	type TestExternalities<H> = CoreTestExternalities<H, u64>;

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
	fn blake2_128_should_work() {
		let mut ext = TestExternalities::default();
		let test_code = include_bytes!("../wasm/target/wasm32-unknown-unknown/release/runtime_test.compact.wasm");
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_blake2_128", &[]).unwrap(),
			blake2_128(&b""[..]).encode()
		);
		assert_eq!(
			WasmExecutor::new().call(&mut ext, 8, &test_code[..], "test_blake2_128", b"Hello world!").unwrap(),
			blake2_128(&b"Hello world!"[..]).encode()
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
