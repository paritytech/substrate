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

//! DB-backed cache of blockchain data.

use std::sync::Arc;
use parking_lot::RwLock;

use kvdb::{KeyValueDB, DBTransaction};

use client::blockchain::Cache as BlockchainCache;
use client::error::Result as ClientResult;
use codec::{Encode, Decode};
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, NumberFor, As};
use utils::{self, COLUMN_META};

use self::list_cache::ListCache;

mod list_cache;
mod list_entry;
mod list_storage;

/// Minimal post-finalization age age of finalized blocks before they'll pruned.
const PRUNE_DEPTH: u64 = 1024;

/// Block identifier that holds both hash and number.
#[derive(Clone, Debug, Encode, Decode, PartialEq)]
pub struct ComplexBlockId<Block: BlockT> {
	hash: Block::Hash,
	number: NumberFor<Block>,
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
	authorities_at: ListCache<Block, Vec<AuthorityId>, self::list_storage::DbStorage>,
}

impl<Block: BlockT> DbCache<Block> {
	/// Create new cache.
	pub fn new(
		db: Arc<KeyValueDB>,
		hash_lookup_column: Option<u32>,
		header_column: Option<u32>,
		authorities_column: Option<u32>,
		best_finalized_block: ComplexBlockId<Block>,
	) -> Self {
		DbCache {
			authorities_at: ListCache::new(
				self::list_storage::DbStorage::new(b"auth".to_vec(), db,
					self::list_storage::DbColumns {
						meta: COLUMN_META,
						hash_lookup: hash_lookup_column,
						header: header_column,
						cache: authorities_column,
					},
				),
				As::sa(PRUNE_DEPTH),
				best_finalized_block,
			),
		}
	}

	/// Begin cache transaction.
	pub fn transaction<'a>(&'a mut self, tx: &'a mut DBTransaction) -> DbCacheTransaction<'a, Block> {
		DbCacheTransaction {
			cache: self,
			tx,
			authorities_at_op: None,
		}
	}

	/// Run post-commit cache operations.
	pub fn commit(&mut self, ops: DbCacheTransactionOps<Block>) {
		if let Some(authorities_at_op) = ops.authorities_at_op {
			self.authorities_at.on_transaction_commit(authorities_at_op);
		}
	}
}

/// Cache operations that are to be committed after database transaction is committed.
pub struct DbCacheTransactionOps<Block: BlockT> {
	authorities_at_op: Option<self::list_cache::CommitOperation<Block, Vec<AuthorityId>>>,
}

/// Database-backed blockchain data cache transaction valid for single block import.
pub struct DbCacheTransaction<'a, Block: BlockT> {
	cache: &'a mut DbCache<Block>,
	tx: &'a mut DBTransaction,
	authorities_at_op: Option<self::list_cache::CommitOperation<Block, Vec<AuthorityId>>>,
}

impl<'a, Block: BlockT> DbCacheTransaction<'a, Block> {
	/// Convert transaction into post-commit operations set.
	pub fn into_ops(self) -> DbCacheTransactionOps<Block> {
		DbCacheTransactionOps {
			authorities_at_op: self.authorities_at_op,
		}
	}

	/// When new block is inserted into database.
	pub fn on_block_insert(
		mut self,
		parent: ComplexBlockId<Block>,
		block: ComplexBlockId<Block>,
		authorities_at: Option<Vec<AuthorityId>>,
		is_final: bool,
	) -> ClientResult<Self> {
		assert!(self.authorities_at_op.is_none());

		self.authorities_at_op = self.cache.authorities_at.on_block_insert(
			&mut self::list_storage::DbStorageTransaction::new(
				self.cache.authorities_at.storage(),
				&mut self.tx
			),
			parent,
			block,
			authorities_at,
			is_final,
		)?;

		Ok(self)
	}

	/// When previously inserted block is finalized.
	pub fn on_block_finalize(
		mut self,
		parent: ComplexBlockId<Block>,
		block: ComplexBlockId<Block>
	) -> ClientResult<Self> {
		assert!(self.authorities_at_op.is_none());

		self.authorities_at_op = self.cache.authorities_at.on_block_finalize(
			&mut self::list_storage::DbStorageTransaction::new(
				self.cache.authorities_at.storage(),
				&mut self.tx
			),
			parent,
			block,
		)?;

		Ok(self)
	}
}

/// Synchronous implementation of database-backed blockchain data cache.
pub struct DbCacheSync<Block: BlockT>(pub RwLock<DbCache<Block>>);

impl<Block: BlockT> BlockchainCache<Block> for DbCacheSync<Block> {
	fn authorities_at(&self, at: BlockId<Block>) -> Option<Vec<AuthorityId>> {
		let cache = self.0.read();
		let storage = cache.authorities_at.storage();
		let db = storage.db();
		let columns = storage.columns();
		let at = match at {
			BlockId::Hash(hash) => {
				let header = utils::read_header::<Block>(
					&**db,
					columns.hash_lookup,
					columns.header,
					BlockId::Hash(hash.clone())).ok()??;
				ComplexBlockId::new(hash, *header.number())
			},
			BlockId::Number(number) => {
				let hash = utils::read_header::<Block>(
					&**db,
					columns.hash_lookup,
					columns.header,
					BlockId::Number(number.clone())).ok()??.hash();
				ComplexBlockId::new(hash, number)
			},
		};

		cache.authorities_at.value_at_block(&at).ok()?
	}
}
