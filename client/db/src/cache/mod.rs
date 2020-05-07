// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! DB-backed cache of blockchain data.

use std::{sync::Arc, collections::{HashMap, hash_map::Entry}};
use parking_lot::RwLock;

use sc_client_api::blockchain::{well_known_cache_keys::{self, Id as CacheKeyId}, Cache as BlockchainCache};
use sp_blockchain::{Result as ClientResult, HeaderMetadataCache};
use sp_database::{Database, Transaction};
use codec::{Encode, Decode};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor, Zero};
use crate::utils::{self, COLUMN_META};
use crate::DbHash;

use self::list_cache::{ListCache, PruningStrategy};

mod list_cache;
mod list_entry;
mod list_storage;

/// Minimal post-finalization age of finalized blocks before they'll pruned.
const PRUNE_DEPTH: u32 = 1024;

/// The type of entry that is inserted to the cache.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum EntryType {
	/// Non-final entry.
	NonFinal,
	/// Final entry.
	Final,
	/// Genesis entry (inserted during cache initialization).
	Genesis,
}

/// Block identifier that holds both hash and number.
#[derive(Clone, Debug, Encode, Decode, PartialEq)]
pub struct ComplexBlockId<Block: BlockT> {
	/// Hash of the block.
	pub(crate) hash: Block::Hash,
	/// Number of the block.
	pub(crate) number: NumberFor<Block>,
}

impl<Block: BlockT> ComplexBlockId<Block> {
	/// Create new complex block id.
	pub fn new(hash: Block::Hash, number: NumberFor<Block>) -> Self {
		ComplexBlockId { hash, number }
	}
}

impl<Block: BlockT> ::std::cmp::PartialOrd for ComplexBlockId<Block> {
	fn partial_cmp(&self, other: &ComplexBlockId<Block>) -> Option<::std::cmp::Ordering> {
		self.number.partial_cmp(&other.number)
	}
}

/// All cache items must implement this trait.
pub trait CacheItemT: Clone + Decode + Encode + PartialEq {}

impl<T> CacheItemT for T where T: Clone + Decode + Encode + PartialEq {}

/// Database-backed blockchain data cache.
pub struct DbCache<Block: BlockT> {
	cache_at: HashMap<CacheKeyId, ListCache<Block, Vec<u8>, self::list_storage::DbStorage>>,
	header_metadata_cache: Arc<HeaderMetadataCache<Block>>,
	db: Arc<dyn Database<DbHash>>,
	key_lookup_column: u32,
	header_column: u32,
	cache_column: u32,
	genesis_hash: Block::Hash,
	best_finalized_block: ComplexBlockId<Block>,
}

impl<Block: BlockT> DbCache<Block> {
	/// Create new cache.
	pub fn new(
		db: Arc<dyn Database<DbHash>>,
		header_metadata_cache: Arc<HeaderMetadataCache<Block>>,
		key_lookup_column: u32,
		header_column: u32,
		cache_column: u32,
		genesis_hash: Block::Hash,
		best_finalized_block: ComplexBlockId<Block>,
	) -> Self {
		Self {
			cache_at: HashMap::new(),
			db,
			header_metadata_cache,
			key_lookup_column,
			header_column,
			cache_column,
			genesis_hash,
			best_finalized_block,
		}
	}

	/// Set genesis block hash.
	pub fn set_genesis_hash(&mut self, genesis_hash: Block::Hash) {
		self.genesis_hash = genesis_hash;
	}

	/// Begin cache transaction.
	pub fn transaction<'a>(&'a mut self, tx: &'a mut Transaction<DbHash>) -> DbCacheTransaction<'a, Block> {
		DbCacheTransaction {
			cache: self,
			tx,
			cache_at_ops: HashMap::new(),
			best_finalized_block: None,
		}
	}

	/// Begin cache transaction with given ops.
	pub fn transaction_with_ops<'a>(
		&'a mut self,
		tx: &'a mut Transaction<DbHash>,
		ops: DbCacheTransactionOps<Block>,
	) -> DbCacheTransaction<'a, Block> {
		DbCacheTransaction {
			cache: self,
			tx,
			cache_at_ops: ops.cache_at_ops,
			best_finalized_block: ops.best_finalized_block,
		}
	}

	/// Run post-commit cache operations.
	pub fn commit(&mut self, ops: DbCacheTransactionOps<Block>) -> ClientResult<()> {
		for (name, ops) in ops.cache_at_ops.into_iter() {
			self.get_cache(name)?.on_transaction_commit(ops);
		}
		if let Some(best_finalized_block) = ops.best_finalized_block {
			self.best_finalized_block = best_finalized_block;
		}
		Ok(())
	}

	/// Creates `ListCache` with the given name or returns a reference to the existing.
	pub(crate) fn get_cache(
		&mut self,
		name: CacheKeyId,
	) -> ClientResult<&mut ListCache<Block, Vec<u8>, self::list_storage::DbStorage>> {
		get_cache_helper(
			&mut self.cache_at,
			name,
			&self.db,
			self.key_lookup_column,
			self.header_column,
			self.cache_column,
			&self.best_finalized_block
		)
	}
}

// This helper is needed because otherwise the borrow checker will require to
// clone all parameters outside of the closure.
fn get_cache_helper<'a, Block: BlockT>(
	cache_at: &'a mut HashMap<CacheKeyId, ListCache<Block, Vec<u8>, self::list_storage::DbStorage>>,
	name: CacheKeyId,
	db: &Arc<dyn Database<DbHash>>,
	key_lookup: u32,
	header: u32,
	cache: u32,
	best_finalized_block: &ComplexBlockId<Block>,
) -> ClientResult<&'a mut ListCache<Block, Vec<u8>, self::list_storage::DbStorage>> {
	match cache_at.entry(name) {
		Entry::Occupied(entry) => Ok(entry.into_mut()),
		Entry::Vacant(entry) => {
			let cache = ListCache::new(
				self::list_storage::DbStorage::new(name.to_vec(), db.clone(),
					self::list_storage::DbColumns {
						meta: COLUMN_META,
						key_lookup,
						header,
						cache,
					},
				),
				cache_pruning_strategy(name),
				best_finalized_block.clone(),
			)?;
			Ok(entry.insert(cache))
		}
	}
}

/// Cache operations that are to be committed after database transaction is committed.
#[derive(Default)]
pub struct DbCacheTransactionOps<Block: BlockT> {
	cache_at_ops: HashMap<CacheKeyId, self::list_cache::CommitOperations<Block, Vec<u8>>>,
	best_finalized_block: Option<ComplexBlockId<Block>>,
}

impl<Block: BlockT> DbCacheTransactionOps<Block> {
	/// Empty transaction ops.
	pub fn empty() -> DbCacheTransactionOps<Block> {
		DbCacheTransactionOps {
			cache_at_ops: HashMap::new(),
			best_finalized_block: None,
		}
	}
}

/// Database-backed blockchain data cache transaction valid for single block import.
pub struct DbCacheTransaction<'a, Block: BlockT> {
	cache: &'a mut DbCache<Block>,
	tx: &'a mut Transaction<DbHash>,
	cache_at_ops: HashMap<CacheKeyId, self::list_cache::CommitOperations<Block, Vec<u8>>>,
	best_finalized_block: Option<ComplexBlockId<Block>>,
}

impl<'a, Block: BlockT> DbCacheTransaction<'a, Block> {
	/// Convert transaction into post-commit operations set.
	pub fn into_ops(self) -> DbCacheTransactionOps<Block> {
		DbCacheTransactionOps {
			cache_at_ops: self.cache_at_ops,
			best_finalized_block: self.best_finalized_block,
		}
	}

	/// When new block is inserted into database.
	pub fn on_block_insert(
		mut self,
		parent: ComplexBlockId<Block>,
		block: ComplexBlockId<Block>,
		data_at: HashMap<CacheKeyId, Vec<u8>>,
		entry_type: EntryType,
	) -> ClientResult<Self> {
		// prepare list of caches that are not update
		// (we might still need to do some cache maintenance in this case)
		let missed_caches = self.cache.cache_at.keys()
			.filter(|cache| !data_at.contains_key(*cache))
			.cloned()
			.collect::<Vec<_>>();

		let mut insert_op = |name: CacheKeyId, value: Option<Vec<u8>>| -> Result<(), sp_blockchain::Error> {
			let cache = self.cache.get_cache(name)?;
			let cache_ops = self.cache_at_ops.entry(name).or_default();
			cache.on_block_insert(
				&mut self::list_storage::DbStorageTransaction::new(
					cache.storage(),
					&mut self.tx,
				),
				parent.clone(),
				block.clone(),
				value,
				entry_type,
				cache_ops,
			)?;

			Ok(())
		};

		data_at.into_iter().try_for_each(|(name, data)| insert_op(name, Some(data)))?;
		missed_caches.into_iter().try_for_each(|name| insert_op(name, None))?;

		match entry_type {
			EntryType::Final | EntryType::Genesis =>
				self.best_finalized_block = Some(block),
			EntryType::NonFinal => (),
		}

		Ok(self)
	}

	/// When previously inserted block is finalized.
	pub fn on_block_finalize(
		mut self,
		parent: ComplexBlockId<Block>,
		block: ComplexBlockId<Block>,
	) -> ClientResult<Self> {
		for (name, cache) in self.cache.cache_at.iter() {
			let cache_ops = self.cache_at_ops.entry(*name).or_default();
			cache.on_block_finalize(
				&mut self::list_storage::DbStorageTransaction::new(
					cache.storage(),
					&mut self.tx
				),
				parent.clone(),
				block.clone(),
				cache_ops,
			)?;
		}

		self.best_finalized_block = Some(block);

		Ok(self)
	}

	/// When block is reverted.
	pub fn on_block_revert(
		mut self,
		reverted_block: &ComplexBlockId<Block>,
	) -> ClientResult<Self> {
		for (name, cache) in self.cache.cache_at.iter() {
			let cache_ops = self.cache_at_ops.entry(*name).or_default();
			cache.on_block_revert(
				&mut self::list_storage::DbStorageTransaction::new(
					cache.storage(),
					&mut self.tx
				),
				reverted_block,
				cache_ops,
			)?;
		}

		Ok(self)
	}
}

/// Synchronous implementation of database-backed blockchain data cache.
pub struct DbCacheSync<Block: BlockT>(pub RwLock<DbCache<Block>>);

impl<Block: BlockT> BlockchainCache<Block> for DbCacheSync<Block> {
	fn initialize(&self, key: &CacheKeyId, data: Vec<u8>) -> ClientResult<()> {
		let mut cache = self.0.write();
		let genesis_hash = cache.genesis_hash;
		let cache_contents = vec![(*key, data)].into_iter().collect();
		let db = cache.db.clone();
		let mut dbtx = Transaction::new();
		let tx = cache.transaction(&mut dbtx);
		let tx = tx.on_block_insert(
			ComplexBlockId::new(Default::default(), Zero::zero()),
			ComplexBlockId::new(genesis_hash, Zero::zero()),
			cache_contents,
			EntryType::Genesis,
		)?;
		let tx_ops = tx.into_ops();
		db.commit(dbtx);
		cache.commit(tx_ops)?;
		Ok(())
	}

	fn get_at(
		&self,
		key: &CacheKeyId,
		at: &BlockId<Block>,
	) -> ClientResult<Option<((NumberFor<Block>, Block::Hash), Option<(NumberFor<Block>, Block::Hash)>, Vec<u8>)>> {
		let mut cache = self.0.write();
		let header_metadata_cache = cache.header_metadata_cache.clone();
		let cache = cache.get_cache(*key)?;
		let storage = cache.storage();
		let db = storage.db();
		let columns = storage.columns();
		let at = match *at {
			BlockId::Hash(hash) => {
				match header_metadata_cache.header_metadata(hash) {
					Some(metadata) => ComplexBlockId::new(hash, metadata.number),
					None => {
						let header = utils::require_header::<Block>(
							&**db,
							columns.key_lookup,
							columns.header,
							BlockId::Hash(hash.clone()))?;
						ComplexBlockId::new(hash, *header.number())
					}
				}
			},
			BlockId::Number(number) => {
				let hash = utils::require_header::<Block>(
					&**db,
					columns.key_lookup,
					columns.header,
					BlockId::Number(number.clone()))?.hash();
				ComplexBlockId::new(hash, number)
			},
		};

		cache.value_at_block(&at)
			.map(|block_and_value| block_and_value.map(|(begin_block, end_block, value)|
				(
					(begin_block.number, begin_block.hash),
					end_block.map(|end_block| (end_block.number, end_block.hash)),
					value,
				)))
	}
}

/// Get pruning strategy for given cache.
fn cache_pruning_strategy<N: From<u32>>(cache: CacheKeyId) -> PruningStrategy<N> {
	// the cache is mostly used to store data from consensus engines
	// this kind of data is only required for non-finalized blocks
	// => by default we prune finalized cached entries

	match cache {
		// we need to keep changes tries configurations forever (or at least until changes tries,
		// that were built using this configuration, are pruned) to make it possible to refer
		// to old changes tries
		well_known_cache_keys::CHANGES_TRIE_CONFIG => PruningStrategy::NeverPrune,
		_ => PruningStrategy::ByDepth(PRUNE_DEPTH.into()),
	}
}
