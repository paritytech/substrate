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

//! List-cache storage entries.

use client::error::Result as ClientResult;
use sr_primitives::traits::{Block as BlockT, NumberFor};
use parity_codec::{Encode, Decode};

use crate::cache::{CacheItemT, ComplexBlockId};
use crate::cache::list_storage::{Storage};

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
				false => Some(StorageEntry {
					prev_valid_from: Some(self.valid_from.clone()),
					value,
				}),
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
		Ok(self.search_best_before(storage, 0, block)?
			.map(|(_, entry, next)| (entry.valid_from, next)))
	}

	/// Searches the list, ending with THIS entry for the best entry preceeding (or at)
	/// given block number.
	/// If the entry is found, result is the entry and the block id of next entry (if exists).
	/// NOTE that this function does not check that the passed block is actually linked to
	/// the blocks it found.
	pub fn search_best_before<S: Storage<Block, T>>(
		&self,
		storage: &S,
		skip: usize,
		block: NumberFor<Block>,
	) -> ClientResult<Option<(usize, Entry<Block, T>, Option<ComplexBlockId<Block>>)>> {
		const EXPECT_PROOF: &'static str = "state is Skip*; state is Skip* only when entry.is_some(); qed";
		enum State { Seek, SkipReady(usize), Skip(usize) }

		// we're looking for the best value
		let mut state = State::Seek;
		let mut next = None;
		let mut entry = None;
		let mut current = self.valid_from.clone();
		if block >= self.valid_from.number {
			let value = self.value.clone();
			state = State::SkipReady(skip);
			entry = Some(Entry { valid_from: current.clone(), value });
		}

		// else - travel back in time
		loop {
			match state {
				State::Seek => {
					let current_entry = storage.require_entry(&current)?;
					if block >= current.number {
						state = State::Skip(skip);
						entry = Some(Entry { valid_from: current.clone(), value: current_entry.value });
					} else {
						next = Some(current);
						current = match current_entry.prev_valid_from {
							Some(prev_valid_from) => prev_valid_from,
							None => return Ok(None),
						};
					}
				},
				State::SkipReady(0) => {
					return Ok(Some((skip, entry.expect(EXPECT_PROOF), next)));
				},
				State::Skip(0) => {
					let current_entry = storage.require_entry(&current)?;
					entry = Some(Entry { valid_from: current.clone(), value: current_entry.value });
					return Ok(Some((skip, entry.expect(EXPECT_PROOF), next)));
				},
				State::Skip(skip_rest) | State::SkipReady(skip_rest) => {
					let current_entry = storage.require_entry(&current)?;
					let next_current = match current_entry.prev_valid_from {
						Some(prev_valid_from) => prev_valid_from,
						None => {
							entry = Some(Entry { valid_from: current.clone(), value: current_entry.value });
							return Ok(Some((skip - skip_rest, entry.expect(EXPECT_PROOF), next)));
						},
					};

					entry = Some(Entry { valid_from: current.clone(), value: current_entry.value });
					next = Some(current.clone());
					state = State::Skip(skip_rest - 1);
					current = next_current;
				},
			}


		}
	}
}

impl<Block: BlockT, T: CacheItemT> StorageEntry<Block, T> {
	/// Converts storage entry into an entry, valid from given block.
	pub fn into_entry(self, valid_from: ComplexBlockId<Block>) -> Entry<Block, T> {
		Entry {
			valid_from,
			value: self.value,
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::cache::list_cache::tests::test_id;
	use crate::cache::list_storage::tests::{DummyStorage, FaultyStorage};
	use super::*;

	#[test]
	fn entry_try_update_works() {
		// when trying to update with None value
		assert_eq!(Entry::<_, u64> { valid_from: test_id(1), value: 42 }.try_update(None), None);
		// when trying to update with the same Some value
		assert_eq!(Entry { valid_from: test_id(1), value: 1 }.try_update(Some(1)), None);
		// when trying to update with different Some value
		assert_eq!(Entry { valid_from: test_id(1), value: 1 }.try_update(Some(2)),
			Some(StorageEntry { prev_valid_from: Some(test_id(1)), value: 2 }));
	}

	#[test]
	fn entry_search_best_before_fails() {
		// when storage returns error
		assert!(Entry::<_, u64> { valid_from: test_id(100), value: 42 }
			.search_best_before(&FaultyStorage, 0, 50).is_err());
	}

	#[test]
	fn entry_search_best_before_works() {
		// when block is better than our best block
		assert_eq!(Entry::<_, u64> { valid_from: test_id(100), value: 100 }
			.search_best_before(&DummyStorage::new(), 0, 150).unwrap(),
		Some((0, Entry::<_, u64> { valid_from: test_id(100), value: 100 }, None)));
		// when block is found between two entries
		assert_eq!(Entry::<_, u64> { valid_from: test_id(100), value: 100 }
			.search_best_before(&DummyStorage::new()
				.with_entry(test_id(100), StorageEntry { prev_valid_from: Some(test_id(50)), value: 100 })
				.with_entry(test_id(50), StorageEntry { prev_valid_from: Some(test_id(30)), value: 50 }),
			0, 75).unwrap(),
		Some((0, Entry::<_, u64> { valid_from: test_id(50), value: 50 }, Some(test_id(100)))));
		// when block is not found
		assert_eq!(Entry::<_, u64> { valid_from: test_id(100), value: 100 }
			.search_best_before(&DummyStorage::new()
				.with_entry(test_id(100), StorageEntry { prev_valid_from: Some(test_id(50)), value: 100 })
				.with_entry(test_id(50), StorageEntry { prev_valid_from: None, value: 50 }),
			0, 30).unwrap(),
		None);
	}

	#[test]
	fn entry_search_best_before_with_skip_works() {
		let storage = DummyStorage::new()
			.with_entry(test_id(100), StorageEntry { prev_valid_from: Some(test_id(50)), value: 100 })
			.with_entry(test_id(50), StorageEntry { prev_valid_from: Some(test_id(30)), value: 50 })
			.with_entry(test_id(30), StorageEntry { prev_valid_from: Some(test_id(15)), value: 30 })
			.with_entry(test_id(15), StorageEntry { prev_valid_from: Some(test_id(5)), value: 15 })
			.with_entry(test_id(5), StorageEntry { prev_valid_from: None, value: 5 });
		let entry = Entry::<_, u64> { valid_from: test_id(100), value: 100 };

		// when block is better than our best block AND we skip everything
		let best_before = entry.search_best_before(&storage, 1000, 150).unwrap();
		assert_eq!(
			best_before,
			Some((
				4,
				Entry::<_, u64> { valid_from: test_id(5), value: 5 },
				Some(test_id(15)),
			)),
		);

		// when block is better than our best block AND we skip couple of entries
		let best_before = entry.search_best_before(&storage, 2, 150).unwrap();
		assert_eq!(
			best_before,
			Some((
				2,
				Entry::<_, u64> { valid_from: test_id(30), value: 30 },
				Some(test_id(50)),
			)),
		);

		// when block is worse than our best block AND we skip everything
		let best_before = entry.search_best_before(&storage, 1000, 40).unwrap();
		assert_eq!(
			best_before,
			Some((
				2,
				Entry::<_, u64> { valid_from: test_id(5), value: 5 },
				Some(test_id(15)),
			)),
		);

		// when block is worse than our best block AND we skip couple of entries
		let best_before = entry.search_best_before(&storage, 2, 70).unwrap();
		assert_eq!(
			best_before,
			Some((
				2,
				Entry::<_, u64> { valid_from: test_id(15), value: 15 },
				Some(test_id(30)),
			)),
		);
	}
}
