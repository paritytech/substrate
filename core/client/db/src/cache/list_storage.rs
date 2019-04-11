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

//! List-cache storage definition and implementation.

use std::sync::Arc;

use kvdb::{KeyValueDB, DBTransaction};

use client::error::{Error as ClientError, Result as ClientResult};
use parity_codec::{Encode, Decode};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use crate::utils::{self, db_err, meta_keys};

use crate::cache::{CacheItemT, ComplexBlockId};
use crate::cache::list_cache::{CommitOperation, Fork};
use crate::cache::list_entry::{Entry, StorageEntry};

/// Single list-cache metadata.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone, PartialEq))]
pub struct Metadata<Block: BlockT> {
	/// Block at which best finalized entry is stored.
	pub finalized: Option<ComplexBlockId<Block>>,
	/// A set of blocks at which best unfinalized entries are stored.
	pub unfinalized: Vec<ComplexBlockId<Block>>,
}

/// Readonly list-cache storage trait.
pub trait Storage<Block: BlockT, T: CacheItemT> {
	/// Reads hash of the block at given number.
	fn read_id(&self, at: NumberFor<Block>) -> ClientResult<Option<Block::Hash>>;

	/// Reads header of the block with given hash.
	fn read_header(&self, at: &Block::Hash) -> ClientResult<Option<Block::Header>>;

	/// Reads cache metadata: best finalized entry (if some) and the list.
	fn read_meta(&self) -> ClientResult<Metadata<Block>>;

	/// Reads cache entry from the storage.
	fn read_entry(&self, at: &ComplexBlockId<Block>) -> ClientResult<Option<StorageEntry<Block, T>>>;

	/// Reads referenced (and thus existing) cache entry from the storage.
	fn require_entry(&self, at: &ComplexBlockId<Block>) -> ClientResult<StorageEntry<Block, T>> {
		self.read_entry(at)
			.and_then(|entry| entry
				.ok_or_else(|| ClientError::from(
					ClientError::Backend(format!("Referenced cache entry at {:?} is not found", at)))))
	}
}

/// List-cache storage transaction.
pub trait StorageTransaction<Block: BlockT, T: CacheItemT> {
	/// Insert storage entry at given block.
	fn insert_storage_entry(&mut self, at: &ComplexBlockId<Block>, entry: &StorageEntry<Block, T>);

	/// Delete storage entry at given block.
	fn remove_storage_entry(&mut self, at: &ComplexBlockId<Block>);

	/// Update metadata of the cache.
	fn update_meta(
		&mut self,
		best_finalized_entry: Option<&Entry<Block, T>>,
		unfinalized: &[Fork<Block, T>],
		operation: &CommitOperation<Block, T>,
	);
}

/// A set of columns used by the DbStorage.
#[derive(Debug)]
pub struct DbColumns {
	/// Column holding cache meta.
	pub meta: Option<u32>,
	/// Column holding the mapping of { block number => block hash } for blocks of the best chain.
	pub key_lookup: Option<u32>,
	/// Column holding the mapping of { block hash => block header }.
	pub header: Option<u32>,
	/// Column holding cache entries.
	pub cache: Option<u32>,
}

/// Database-backed list cache storage.
pub struct DbStorage {
	name: Vec<u8>,
	meta_key: Vec<u8>,
	db: Arc<KeyValueDB>,
	columns: DbColumns,
}

impl DbStorage {
	/// Create new database-backed list cache storage.
	pub fn new(name: Vec<u8>, db: Arc<KeyValueDB>, columns: DbColumns) -> Self {
		let meta_key = meta::key(&name);
		DbStorage { name, meta_key, db, columns }
	}

	/// Get reference to the database.
	pub fn db(&self) -> &Arc<KeyValueDB> { &self.db }

	/// Get reference to the database columns.
	pub fn columns(&self) -> &DbColumns { &self.columns }

	/// Encode block id for storing as a key in cache column.
	/// We append prefix to the actual encoding to allow several caches
	/// store entries in the same column.
	pub fn encode_block_id<Block: BlockT>(&self, block: &ComplexBlockId<Block>) -> Vec<u8> {
		let mut encoded = self.name.clone();
		encoded.extend(block.hash.as_ref());
		encoded
	}
}

impl<Block: BlockT, T: CacheItemT> Storage<Block, T> for DbStorage {
	fn read_id(&self, at: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
		utils::read_header::<Block>(&*self.db, self.columns.key_lookup, self.columns.header, BlockId::Number(at))
			.map(|maybe_header| maybe_header.map(|header| header.hash()))
	}

	fn read_header(&self, at: &Block::Hash) -> ClientResult<Option<Block::Header>> {
		utils::read_header::<Block>(&*self.db, self.columns.key_lookup, self.columns.header, BlockId::Hash(*at))
	}

	fn read_meta(&self) -> ClientResult<Metadata<Block>> {
		self.db.get(self.columns.meta, &self.meta_key)
			.map_err(db_err)
			.and_then(|meta| match meta {
				Some(meta) => meta::decode(&*meta),
				None => Ok(Metadata {
					finalized: None,
					unfinalized: Vec::new(),
				}),
			})
	}

	fn read_entry(&self, at: &ComplexBlockId<Block>) -> ClientResult<Option<StorageEntry<Block, T>>> {
		self.db.get(self.columns.cache, &self.encode_block_id(at))
			.map_err(db_err)
			.and_then(|entry| match entry {
				Some(entry) => StorageEntry::<Block, T>::decode(&mut &entry[..])
					.ok_or_else(|| ClientError::Backend("Failed to decode cache entry".into()))
					.map(Some),
				None => Ok(None),
			})
	}
}

/// Database-backed list cache storage transaction.
pub struct DbStorageTransaction<'a> {
	storage: &'a DbStorage,
	tx: &'a mut DBTransaction,
}

impl<'a> DbStorageTransaction<'a> {
	/// Create new database transaction.
	pub fn new(storage: &'a DbStorage, tx: &'a mut DBTransaction) -> Self {
		DbStorageTransaction { storage, tx }
	}
}

impl<'a, Block: BlockT, T: CacheItemT> StorageTransaction<Block, T> for DbStorageTransaction<'a> {
	fn insert_storage_entry(&mut self, at: &ComplexBlockId<Block>, entry: &StorageEntry<Block, T>) {
		self.tx.put(self.storage.columns.cache, &self.storage.encode_block_id(at), &entry.encode());
	}

	fn remove_storage_entry(&mut self, at: &ComplexBlockId<Block>) {
		self.tx.delete(self.storage.columns.cache, &self.storage.encode_block_id(at));
	}

	fn update_meta(
		&mut self,
		best_finalized_entry: Option<&Entry<Block, T>>,
		unfinalized: &[Fork<Block, T>],
		operation: &CommitOperation<Block, T>,
	) {
		self.tx.put(
			self.storage.columns.meta,
			&self.storage.meta_key,
			&meta::encode(best_finalized_entry, unfinalized, operation));
	}
}

/// Metadata related functions.
mod meta {
	use super::*;

	/// Convert cache name into cache metadata key.
	pub fn key(name: &[u8]) -> Vec<u8> {
		let mut key_name = meta_keys::CACHE_META_PREFIX.to_vec();
		key_name.extend_from_slice(name);
		key_name
	}

	/// Encode cache metadata 'applying' commit operation before encoding.
	pub fn encode<Block: BlockT, T: CacheItemT>(
		best_finalized_entry: Option<&Entry<Block, T>>,
		unfinalized: &[Fork<Block, T>],
		op: &CommitOperation<Block, T>
	) -> Vec<u8> {
		let mut finalized = best_finalized_entry.as_ref().map(|entry| &entry.valid_from);
		let mut unfinalized = unfinalized.iter().map(|fork| &fork.head().valid_from).collect::<Vec<_>>();

		match op {
			CommitOperation::AppendNewBlock(_, _) => (),
			CommitOperation::AppendNewEntry(index, ref entry) => {
				unfinalized[*index] = &entry.valid_from;
			},
			CommitOperation::AddNewFork(ref entry) => {
				unfinalized.push(&entry.valid_from);
			},
			CommitOperation::BlockFinalized(_, ref finalizing_entry, ref forks) => {
				finalized = finalizing_entry.as_ref().map(|entry| &entry.valid_from);
				for fork_index in forks.iter().rev() {
					unfinalized.remove(*fork_index);
				}
			},
		}

		(finalized, unfinalized).encode()
	}

	/// Decode meta information.
	pub fn decode<Block: BlockT>(encoded: &[u8]) -> ClientResult<Metadata<Block>> {
		let input = &mut &*encoded;
		let finalized: Option<ComplexBlockId<Block>> = Decode::decode(input)
			.ok_or_else(|| ClientError::from(ClientError::Backend("Error decoding cache meta".into())))?;
		let unfinalized: Vec<ComplexBlockId<Block>> = Decode::decode(input)
			.ok_or_else(|| ClientError::from(ClientError::Backend("Error decoding cache meta".into())))?;

		Ok(Metadata { finalized, unfinalized })
	}
}

#[cfg(test)]
pub mod tests {
	use std::collections::{HashMap, HashSet};
	use super::*;

	pub struct FaultyStorage;

	impl<Block: BlockT, T: CacheItemT> Storage<Block, T> for FaultyStorage {
		fn read_id(&self, _at: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
			Err(ClientError::Backend("TestError".into()))
		}

		fn read_header(&self, _at: &Block::Hash) -> ClientResult<Option<Block::Header>> {
			Err(ClientError::Backend("TestError".into()))
		}

		fn read_meta(&self) -> ClientResult<Metadata<Block>> {
			Err(ClientError::Backend("TestError".into()))
		}

		fn read_entry(&self, _at: &ComplexBlockId<Block>) -> ClientResult<Option<StorageEntry<Block, T>>> {
			Err(ClientError::Backend("TestError".into()))
		}
	}

	pub struct DummyStorage<Block: BlockT, T: CacheItemT> {
		meta: Metadata<Block>,
		ids: HashMap<NumberFor<Block>, Block::Hash>,
		headers: HashMap<Block::Hash, Block::Header>,
		entries: HashMap<Block::Hash, StorageEntry<Block, T>>,
	}

	impl<Block: BlockT, T: CacheItemT> DummyStorage<Block, T> {
		pub fn new() -> Self {
			DummyStorage {
				meta: Metadata {
					finalized: None,
					unfinalized: Vec::new(),
				},
				ids: HashMap::new(),
				headers: HashMap::new(),
				entries: HashMap::new(),
			}
		}

		pub fn with_meta(mut self, finalized: Option<ComplexBlockId<Block>>, unfinalized: Vec<ComplexBlockId<Block>>) -> Self {
			self.meta.finalized = finalized;
			self.meta.unfinalized = unfinalized;
			self
		}

		pub fn with_id(mut self, at: NumberFor<Block>, id: Block::Hash) -> Self {
			self.ids.insert(at, id);
			self
		}

		pub fn with_header(mut self, header: Block::Header) -> Self {
			self.headers.insert(header.hash(), header);
			self
		}

		pub fn with_entry(mut self, at: ComplexBlockId<Block>, entry: StorageEntry<Block, T>) -> Self {
			self.entries.insert(at.hash, entry);
			self
		}
	}

	impl<Block: BlockT, T: CacheItemT> Storage<Block, T> for DummyStorage<Block, T> {
		fn read_id(&self, at: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
			Ok(self.ids.get(&at).cloned())
		}

		fn read_header(&self, at: &Block::Hash) -> ClientResult<Option<Block::Header>> {
			Ok(self.headers.get(&at).cloned())
		}

		fn read_meta(&self) -> ClientResult<Metadata<Block>> {
			Ok(self.meta.clone())
		}

		fn read_entry(&self, at: &ComplexBlockId<Block>) -> ClientResult<Option<StorageEntry<Block, T>>> {
			Ok(self.entries.get(&at.hash).cloned())
		}
	}

	pub struct DummyTransaction<Block: BlockT> {
		updated_meta: Option<Metadata<Block>>,
		inserted_entries: HashSet<Block::Hash>,
		removed_entries: HashSet<Block::Hash>,
	}

	impl<Block: BlockT> DummyTransaction<Block> {
		pub fn new() -> Self {
			DummyTransaction {
				updated_meta: None,
				inserted_entries: HashSet::new(),
				removed_entries: HashSet::new(),
			}
		}

		pub fn inserted_entries(&self) -> &HashSet<Block::Hash> {
			&self.inserted_entries
		}

		pub fn removed_entries(&self) -> &HashSet<Block::Hash> {
			&self.removed_entries
		}

		pub fn updated_meta(&self) -> &Option<Metadata<Block>> {
			&self.updated_meta
		}
	}

	impl<Block: BlockT, T: CacheItemT> StorageTransaction<Block, T> for DummyTransaction<Block> {
		fn insert_storage_entry(&mut self, at: &ComplexBlockId<Block>, _entry: &StorageEntry<Block, T>) {
			self.inserted_entries.insert(at.hash);
		}

		fn remove_storage_entry(&mut self, at: &ComplexBlockId<Block>) {
			self.removed_entries.insert(at.hash);
		}

		fn update_meta(
			&mut self,
			best_finalized_entry: Option<&Entry<Block, T>>,
			unfinalized: &[Fork<Block, T>],
			operation: &CommitOperation<Block, T>,
		) {
			self.updated_meta = Some(meta::decode(&meta::encode(best_finalized_entry, unfinalized, operation)).unwrap());
		}
	}
}
