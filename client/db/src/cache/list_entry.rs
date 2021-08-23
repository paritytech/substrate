// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! List-cache storage entries.

use codec::{Decode, Encode};
use sp_blockchain::Result as ClientResult;
use sp_runtime::traits::{Block as BlockT, NumberFor};

use crate::cache::{list_storage::Storage, CacheItemT, ComplexBlockId};

/// Single list-based cache entry.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub struct Entry<Block: BlockT, T> {
	/// first block, when this value became actual.
	pub valid_from: ComplexBlockId<Block>,
	/// Value stored at this entry.
	pub value: T,
}

/// Internal representation of the single list-based cache entry. The entry points to the
/// previous entry in the cache, allowing us to traverse back in time in list-style.
#[derive(Debug, Encode, Decode)]
#[cfg_attr(test, derive(Clone, PartialEq))]
pub struct StorageEntry<Block: BlockT, T: CacheItemT> {
	/// None if valid from the beginning.
	pub prev_valid_from: Option<ComplexBlockId<Block>>,
	/// Value stored at this entry.
	pub value: T,
}

impl<Block: BlockT, T: CacheItemT> Entry<Block, T> {
	/// Returns Some if the entry should be updated with the new value.
	pub fn try_update(&self, value: Option<T>) -> Option<StorageEntry<Block, T>> {
		match value {
			Some(value) => match self.value == value {
				true => None,
				false =>
					Some(StorageEntry { prev_valid_from: Some(self.valid_from.clone()), value }),
			},
			None => None,
		}
	}

	/// Wrapper that calls search_before to get range where the given block fits.
	pub fn search_best_range_before<S: Storage<Block, T>>(
		&self,
		storage: &S,
		block: NumberFor<Block>,
	) -> ClientResult<Option<(ComplexBlockId<Block>, Option<ComplexBlockId<Block>>)>> {
		Ok(self
			.search_best_before(storage, block)?
			.map(|(entry, next)| (entry.valid_from, next)))
	}

	/// Searches the list, ending with THIS entry for the best entry preceding (or at)
	/// given block number.
	/// If the entry is found, result is the entry and the block id of next entry (if exists).
	/// NOTE that this function does not check that the passed block is actually linked to
	/// the blocks it found.
	pub fn search_best_before<S: Storage<Block, T>>(
		&self,
		storage: &S,
		block: NumberFor<Block>,
	) -> ClientResult<Option<(Entry<Block, T>, Option<ComplexBlockId<Block>>)>> {
		// we're looking for the best value
		let mut next = None;
		let mut current = self.valid_from.clone();
		if block >= self.valid_from.number {
			let value = self.value.clone();
			return Ok(Some((Entry { valid_from: current, value }, next)))
		}

		// else - travel back in time
		loop {
			let entry = storage.require_entry(&current)?;
			if block >= current.number {
				return Ok(Some((Entry { valid_from: current, value: entry.value }, next)))
			}

			next = Some(current);
			current = match entry.prev_valid_from {
				Some(prev_valid_from) => prev_valid_from,
				None => return Ok(None),
			};
		}
	}
}

impl<Block: BlockT, T: CacheItemT> StorageEntry<Block, T> {
	/// Converts storage entry into an entry, valid from given block.
	pub fn into_entry(self, valid_from: ComplexBlockId<Block>) -> Entry<Block, T> {
		Entry { valid_from, value: self.value }
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::cache::list_storage::tests::{DummyStorage, FaultyStorage};
	use substrate_test_runtime_client::runtime::{Block, H256};

	fn test_id(number: u64) -> ComplexBlockId<Block> {
		ComplexBlockId::new(H256::from_low_u64_be(number), number)
	}

	#[test]
	fn entry_try_update_works() {
		// when trying to update with None value
		assert_eq!(Entry::<_, u64> { valid_from: test_id(1), value: 42 }.try_update(None), None);
		// when trying to update with the same Some value
		assert_eq!(Entry { valid_from: test_id(1), value: 1 }.try_update(Some(1)), None);
		// when trying to update with different Some value
		assert_eq!(
			Entry { valid_from: test_id(1), value: 1 }.try_update(Some(2)),
			Some(StorageEntry { prev_valid_from: Some(test_id(1)), value: 2 })
		);
	}

	#[test]
	fn entry_search_best_before_fails() {
		// when storage returns error
		assert!(Entry::<_, u64> { valid_from: test_id(100), value: 42 }
			.search_best_before(&FaultyStorage, 50)
			.is_err());
	}

	#[test]
	fn entry_search_best_before_works() {
		// when block is better than our best block
		assert_eq!(
			Entry::<_, u64> { valid_from: test_id(100), value: 100 }
				.search_best_before(&DummyStorage::new(), 150)
				.unwrap(),
			Some((Entry::<_, u64> { valid_from: test_id(100), value: 100 }, None))
		);
		// when block is found between two entries
		assert_eq!(
			Entry::<_, u64> { valid_from: test_id(100), value: 100 }
				.search_best_before(
					&DummyStorage::new()
						.with_entry(
							test_id(100),
							StorageEntry { prev_valid_from: Some(test_id(50)), value: 100 }
						)
						.with_entry(
							test_id(50),
							StorageEntry { prev_valid_from: Some(test_id(30)), value: 50 }
						),
					75
				)
				.unwrap(),
			Some((Entry::<_, u64> { valid_from: test_id(50), value: 50 }, Some(test_id(100))))
		);
		// when block is not found
		assert_eq!(
			Entry::<_, u64> { valid_from: test_id(100), value: 100 }
				.search_best_before(
					&DummyStorage::new()
						.with_entry(
							test_id(100),
							StorageEntry { prev_valid_from: Some(test_id(50)), value: 100 }
						)
						.with_entry(test_id(50), StorageEntry { prev_valid_from: None, value: 50 }),
					30
				)
				.unwrap(),
			None
		);
	}
}
