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

//! DB-backed cache of blockchain data.

use std::sync::Arc;
use parking_lot::RwLock;

use kvdb::{KeyValueDB, DBTransaction};

use client::blockchain::Cache as BlockchainCache;
use client::error::Result as ClientResult;
use codec::{Codec, Encode, Decode, Input, Output};
use primitives::AuthorityId;
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Block as BlockT, As, NumberFor};
use utils::{COLUMN_META, BlockKey, db_err, meta_keys, read_id, db_key_to_number, number_to_db_key};

/// Database-backed cache of blockchain data.
pub struct DbCache<Block: BlockT> {
	db: Arc<KeyValueDB>,
	block_index_column: Option<u32>,
	authorities_at: DbCacheList<Block, Vec<AuthorityId>>,
}

impl<Block> DbCache<Block>
	where
		Block: BlockT,
		NumberFor<Block>: As<u64>,
{
	/// Create new cache.
	pub fn new(
		db: Arc<KeyValueDB>,
		block_index_column: Option<u32>,
		authorities_column: Option<u32>
	) -> ClientResult<Self> {
		Ok(DbCache {
			db: db.clone(),
			block_index_column,
			authorities_at: DbCacheList::new(db, meta_keys::BEST_AUTHORITIES, authorities_column)?,
		})
	}

	/// Get authorities_cache.
	pub fn authorities_at_cache(&self) -> &DbCacheList<Block, Vec<AuthorityId>> {
		&self.authorities_at
	}
}

impl<Block> BlockchainCache<Block> for DbCache<Block>
	where
		Block: BlockT,
		NumberFor<Block>: As<u64>,
{
	fn authorities_at(&self, at: BlockId<Block>) -> Option<Vec<AuthorityId>> {
		let authorities_at = read_id(&*self.db, self.block_index_column, at).and_then(|at| match at {
			Some(at) => self.authorities_at.value_at_key(at),
			None => Ok(None),
		});

		match authorities_at {
			Ok(authorities) => authorities,
			Err(error) => {
				warn!("Trying to read authorities from db cache has failed with: {}", error);
				None
			},
		}
	}
}

/// Database-backed blockchain cache which holds its entries as a list.
/// The meta column holds the pointer to the best known cache entry and
/// every entry points to the previous entry.
/// New entry appears when the set of authorities changes in block, so the
/// best entry here means the entry that is valid for the best block (and
/// probably for its ascendants).
pub struct DbCacheList<Block: BlockT, T: Clone> {
	db: Arc<KeyValueDB>,
	meta_key: &'static [u8],
	column: Option<u32>,
	/// Best entry at the moment. None means that cache has no entries at all.
	best_entry: RwLock<Option<Entry<NumberFor<Block>, T>>>,
}

/// Single cache entry.
#[derive(Clone)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub struct Entry<N, T: Clone> {
	/// first block, when this value became actual
	valid_from: N,
	/// None means that we do not know the value starting from `valid_from` block
	value: Option<T>,
}

/// Internal representation of the single cache entry. The entry points to the
/// previous entry in the cache, allowing us to traverse back in time in list-style.
#[cfg_attr(test, derive(Debug, PartialEq))]
struct StorageEntry<N, T> {
	/// None if valid from the beginning
	prev_valid_from: Option<N>,
	/// None means that we do not know the value starting from `valid_from` block
	value: Option<T>,
}

impl<Block, T> DbCacheList<Block, T>
	where
		Block: BlockT,
		NumberFor<Block>: As<u64>,
		T: Clone + PartialEq + Codec,
{
	/// Creates new cache list.
	fn new(db: Arc<KeyValueDB>, meta_key: &'static [u8], column: Option<u32>) -> ClientResult<Self> {
		let best_entry = RwLock::new(db.get(COLUMN_META, meta_key)
			.map_err(db_err)
			.and_then(|block| match block {
				Some(block) => {
					let valid_from = db_key_to_number(&block)?;
					read_storage_entry::<Block, T>(&*db, column, valid_from)
						.map(|entry| Some(Entry {
							valid_from,
							value: entry
								.expect("meta entry references the entry at the block; storage entry at block exists when referenced; qed")
								.value,
						}))
				},
				None => Ok(None),
			})?);

		Ok(DbCacheList {
			db,
			column,
			meta_key,
			best_entry,
		})
	}

	/// Gets the best known entry.
	pub fn best_entry(&self) -> Option<Entry<NumberFor<Block>, T>> {
		self.best_entry.read().clone()
	}

	/// Commits the new best pending value to the database. Returns Some if best entry must
	/// be updated after transaction is committed.
	pub fn commit_best_entry(
		&self,
		transaction: &mut DBTransaction,
		valid_from: NumberFor<Block>,
		pending_value: Option<T>
	) -> Option<Entry<NumberFor<Block>, T>> {
		let best_entry = self.best_entry();
		let update_best_entry = match (
			best_entry.as_ref().and_then(|a| a.value.as_ref()),
			pending_value.as_ref()
		) {
			(Some(best_value), Some(pending_value)) => best_value != pending_value,
			(None, Some(_)) | (Some(_), None) => true,
			(None, None) => false,
		};
		if !update_best_entry {
			return None;
		}

		let valid_from_key = number_to_db_key(valid_from);
		transaction.put(COLUMN_META, self.meta_key, &valid_from_key);
		transaction.put(self.column, &valid_from_key, &StorageEntry {
			prev_valid_from: best_entry.map(|b| b.valid_from),
			value: pending_value.clone(),
		}.encode());

		Some(Entry {
			valid_from,
			value: pending_value,
		})
	}

	/// Updates the best in-memory cache entry. Must be called after transaction with changes
	/// from commit_best_entry has been committed.
	pub fn update_best_entry(&self, best_entry: Option<Entry<NumberFor<Block>, T>>) {
		*self.best_entry.write() = best_entry;
	}

	/// Prune all entries from the beginning up to the block (including entry at the number). Returns
	/// the number of pruned entries. Pruning never deletes the latest entry in the cache.
	pub fn prune_entries(
		&self,
		transaction: &mut DBTransaction,
		last_to_prune: NumberFor<Block>
	) -> ClientResult<usize> {
		// find the last entry we want to keep
		let mut last_entry_to_keep = match self.best_entry() {
			Some(best_entry) => best_entry.valid_from,
			None => return Ok(0),
		};
		let mut first_entry_to_remove = last_entry_to_keep;
		while first_entry_to_remove > last_to_prune {
			last_entry_to_keep = first_entry_to_remove;

			let entry = read_storage_entry::<Block, T>(&*self.db, self.column, first_entry_to_remove)?
				.expect("entry referenced from the next entry; entry exists when referenced; qed");
			// if we have reached the first list entry
			// AND all list entries are for blocks that are later than last_to_prune
			// => nothing to prune
			first_entry_to_remove = match entry.prev_valid_from {
				Some(prev_valid_from) => prev_valid_from,
				None => return Ok(0),
			}
		}

		// remove all entries, starting from entry_to_remove
		let mut pruned = 0;
		let mut entry_to_remove = Some(first_entry_to_remove);
		while let Some(current_entry) = entry_to_remove {
			let entry = read_storage_entry::<Block, T>(&*self.db, self.column, current_entry)?
				.expect("referenced entry exists; entry_to_remove is a reference to the entry; qed");

			if current_entry != last_entry_to_keep {
				transaction.delete(self.column, &number_to_db_key(current_entry));
				pruned += 1;
			}
			entry_to_remove = entry.prev_valid_from;
		}

		let mut entry = read_storage_entry::<Block, T>(&*self.db, self.column, last_entry_to_keep)?
			.expect("last_entry_to_keep >= first_entry_to_remove; that means that we're leaving this entry in the db; qed");
		entry.prev_valid_from = None;
		transaction.put(self.column, &number_to_db_key(last_entry_to_keep), &entry.encode());

		Ok(pruned)
	}

	/// Reads the cached value, actual at given block. Returns None if the value was not cached
	/// or if it has been pruned.
	fn value_at_key(&self, key: BlockKey) -> ClientResult<Option<T>> {
		let at = db_key_to_number::<NumberFor<Block>>(&key)?;
		let best_valid_from = match self.best_entry() {
			// there are entries in cache
			Some(best_entry) => {
				// we're looking for the best value
				if at >= best_entry.valid_from {
					return Ok(best_entry.value);
				}

				// we're looking for the value of older blocks
				best_entry.valid_from
			},
			// there are no entries in the cache
			None => return Ok(None),
		};

		let mut entry = read_storage_entry::<Block, T>(&*self.db, self.column, best_valid_from)?
			.expect("self.best_entry().is_some() if there's entry for best_valid_from; qed");
		loop {
			let prev_valid_from = match entry.prev_valid_from {
				Some(prev_valid_from) => prev_valid_from,
				None => return Ok(None),
			};

			let prev_entry = read_storage_entry::<Block, T>(&*self.db, self.column, prev_valid_from)?
				.expect("entry referenced from the next entry; entry exists when referenced; qed");
			if at >= prev_valid_from {
				return Ok(prev_entry.value);
			}

			entry = prev_entry;
		}
	}
}

/// Reads the entry at the block with given number.
fn read_storage_entry<Block, T>(
	db: &KeyValueDB,
	column: Option<u32>,
	number: NumberFor<Block>
) -> ClientResult<Option<StorageEntry<NumberFor<Block>, T>>>
	where
		Block: BlockT,
		NumberFor<Block>: As<u64>,
		T: Codec,
{
	db.get(column, &number_to_db_key(number))
		.and_then(|entry| match entry {
			Some(entry) => Ok(StorageEntry::<NumberFor<Block>, T>::decode(&mut &entry[..])),
			None => Ok(None),
		})
	.map_err(db_err)
}

impl<N: Encode, T: Encode> Encode for StorageEntry<N, T> {
	fn encode_to<O: Output>(&self, dest: &mut O) {
		dest.push(&self.prev_valid_from);
		dest.push(&self.value);
	}
}

impl<N: Decode, T: Decode> Decode for StorageEntry<N, T> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(StorageEntry {
			prev_valid_from: Decode::decode(input)?,
			value: Decode::decode(input)?,
		})
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::Block as RawBlock;
	use light::{AUTHORITIES_ENTRIES_TO_KEEP, columns, LightStorage};
	use light::tests::insert_block;
	use super::*;

	type Block = RawBlock<u64>;

	#[test]
	fn authorities_storage_entry_serialized() {
		let test_cases: Vec<StorageEntry<u64, Vec<AuthorityId>>> = vec![
			StorageEntry { prev_valid_from: Some(42), value: Some(vec![[1u8; 32].into()]) },
			StorageEntry { prev_valid_from: None, value: Some(vec![[1u8; 32].into(), [2u8; 32].into()]) },
			StorageEntry { prev_valid_from: None, value: None },
		];

		for expected in test_cases {
			let serialized = expected.encode();
			let deserialized = StorageEntry::decode(&mut &serialized[..]).unwrap();
			assert_eq!(expected, deserialized);
		}
	}

	#[test]
	fn best_authorities_are_updated() {
		let db = LightStorage::new_test();
		let authorities_at: Vec<(usize, Option<Entry<u64, Vec<AuthorityId>>>)> = vec![
			(0, None),
			(0, None),
			(1, Some(Entry { valid_from: 1, value: Some(vec![[2u8; 32].into()]) })),
			(1, Some(Entry { valid_from: 1, value: Some(vec![[2u8; 32].into()]) })),
			(2, Some(Entry { valid_from: 3, value: Some(vec![[4u8; 32].into()]) })),
			(2, Some(Entry { valid_from: 3, value: Some(vec![[4u8; 32].into()]) })),
			(3, Some(Entry { valid_from: 5, value: None })),
			(3, Some(Entry { valid_from: 5, value: None })),
		];

		// before any block, there are no entries in cache
		assert!(db.cache().authorities_at_cache().best_entry().is_none());
		assert_eq!(db.db().iter(columns::AUTHORITIES).count(), 0);

		// insert blocks and check that best_authorities() returns correct result
		let mut prev_hash = Default::default();
		for number in 0..authorities_at.len() {
			let authorities_at_number = authorities_at[number].1.clone().and_then(|e| e.value);
			prev_hash = insert_block(&db, &prev_hash, number as u64, authorities_at_number);
			assert_eq!(db.cache().authorities_at_cache().best_entry(), authorities_at[number].1);
			assert_eq!(db.db().iter(columns::AUTHORITIES).count(), authorities_at[number].0);
		}

		// check that authorities_at() returns correct results for all retrospective blocks
		for number in 1..authorities_at.len() + 1 {
			assert_eq!(db.cache().authorities_at(BlockId::Number(number as u64)),
				authorities_at.get(number + 1)
					.or_else(|| authorities_at.last())
					.unwrap().1.clone().and_then(|e| e.value));
		}

		// now check that cache entries are pruned when new blocks are inserted
		let mut current_entries_count = authorities_at.last().unwrap().0;
		let pruning_starts_at = AUTHORITIES_ENTRIES_TO_KEEP as usize;
		for number in authorities_at.len()..authorities_at.len() + pruning_starts_at {
			prev_hash = insert_block(&db, &prev_hash, number as u64, None);
			if number > pruning_starts_at {
				let prev_entries_count = authorities_at[number - pruning_starts_at].0;
				let entries_count = authorities_at.get(number - pruning_starts_at + 1).map(|e| e.0)
					.unwrap_or_else(|| authorities_at.last().unwrap().0);
				current_entries_count -= entries_count - prev_entries_count;
			}

			// there's always at least 1 entry in the cache (after first insertion)
			assert_eq!(db.db().iter(columns::AUTHORITIES).count(), ::std::cmp::max(current_entries_count, 1));
		}
	}

	#[test]
	fn best_authorities_are_pruned() {
		let db = LightStorage::<Block>::new_test();
		let mut transaction = DBTransaction::new();

		// insert first entry at block#100
		db.cache().authorities_at_cache().update_best_entry(
			db.cache().authorities_at_cache().commit_best_entry(&mut transaction, 100, Some(vec![[1u8; 32].into()])));
		db.db().write(transaction).unwrap();

		// no entries are pruned, since there's only one entry in the cache
		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 50).unwrap(), 0);
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 100).unwrap(), 0);
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 150).unwrap(), 0);

		// insert second entry at block#200
		let mut transaction = DBTransaction::new();
		db.cache().authorities_at_cache().update_best_entry(
			db.cache().authorities_at_cache().commit_best_entry(&mut transaction, 200, Some(vec![[2u8; 32].into()])));
		db.db().write(transaction).unwrap();

		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 50).unwrap(), 0);
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 100).unwrap(), 1);
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 150).unwrap(), 1);
		// still only 1 entry is removed since pruning never deletes the last entry
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 200).unwrap(), 1);
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 250).unwrap(), 1);

		// physically remove entry for block#100 from db
		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 150).unwrap(), 1);
		db.db().write(transaction).unwrap();

		assert_eq!(db.cache().authorities_at_cache().best_entry().unwrap().value, Some(vec![[2u8; 32].into()]));
		assert_eq!(db.cache().authorities_at(BlockId::Number(50)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(100)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(150)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(200)), Some(vec![[2u8; 32].into()]));
		assert_eq!(db.cache().authorities_at(BlockId::Number(250)), Some(vec![[2u8; 32].into()]));

		// try to delete last entry => failure (no entries are removed)
		let mut transaction = DBTransaction::new();
		assert_eq!(db.cache().authorities_at_cache().prune_entries(&mut transaction, 300).unwrap(), 0);
		db.db().write(transaction).unwrap();

		assert_eq!(db.cache().authorities_at_cache().best_entry().unwrap().value, Some(vec![[2u8; 32].into()]));
		assert_eq!(db.cache().authorities_at(BlockId::Number(50)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(100)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(150)), None);
		assert_eq!(db.cache().authorities_at(BlockId::Number(200)), Some(vec![[2u8; 32].into()]));
		assert_eq!(db.cache().authorities_at(BlockId::Number(250)), Some(vec![[2u8; 32].into()]));
	}
}
