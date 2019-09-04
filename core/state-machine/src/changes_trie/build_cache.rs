// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Changes tries build cache.

use std::collections::{HashMap, HashSet};

/// Changes trie build cache.
///
/// Helps to avoid read of changes tries from the database when digest trie
/// is built. It holds changed keys for every block (indexed by changes trie
/// root) that could be referenced by future digest items. For digest entries
/// it also holds keys covered by this digest. Entries for top level digests
/// are never created, because they'll never be used to build other digests.
///
/// Entries are pruned from the cache once digest block that is using this entry
/// is inserted (because digest block will includes all keys from this entry).
/// When there's a fork, entries are pruned when first changes trie is inserted.
pub struct BuildCache<H, N> {
	/// Map of block (implies changes true) number => changes trie root.
	roots_by_number: HashMap<N, H>,
	/// Map of changes trie root => set of storage keys that are in this trie.
	/// The `Option<Vec<u8>>` in inner `HashMap` stands for the child storage key.
	/// If it is `None`, then the `HashSet` contains keys changed in top-level storage.
	/// If it is `Some`, then the `HashSet` contains keys changed in child storage, identified by the key.
	changed_keys: HashMap<H, HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>>,
}

/// The action to perform when block-with-changes-trie is imported.
#[derive(Debug, PartialEq)]
pub enum CacheAction<H, N> {
	/// No action is required.
	DoNothing,
	/// Cache data that has been collected when CT has been built.
	CacheBuildData(CachedBuildData<H, N>),
	/// Clear cache from all existing entries. When new CT configuration enacts,
	/// we don't need any cached data from previous configuration.
	Clear,
}

/// The data that has been cached during changes trie building.
#[derive(Debug, PartialEq)]
pub struct CachedBuildData<H, N> {
	block: N,
	trie_root: H,
	is_top_level_digest: bool,
	digest_input_blocks: Vec<N>,
	changed_keys: HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>,
}

/// The data (without changes trie root) that has been cached during changes trie building.
#[derive(Debug, PartialEq)]
pub(crate) struct IncompleteCachedBuildData<N> {
	is_top_level_digest: bool,
	digest_input_blocks: Vec<N>,
	changed_keys: HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>,
}

impl<H, N> BuildCache<H, N>
	where
		N: Eq + ::std::hash::Hash,
		H: Eq + ::std::hash::Hash + Clone,
{
	/// Create new changes trie build cache.
	pub fn new() -> Self {
		BuildCache {
			roots_by_number: HashMap::new(),
			changed_keys: HashMap::new(),
		}
	}

	/// Get cached changed keys for changes trie with given root.
	pub fn get(&self, root: &H) -> Option<&HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>> {
		self.changed_keys.get(&root)
	}

	/// Insert data into cache.
	pub fn perform(&mut self, action: CacheAction<H, N>) {
		match action {
			CacheAction::DoNothing => (),
			CacheAction::CacheBuildData(data) => {
				if !data.is_top_level_digest {
					self.roots_by_number.insert(data.block, data.trie_root.clone());
					self.changed_keys.insert(data.trie_root, data.changed_keys);
				}

				for digest_input_block in data.digest_input_blocks {
					let digest_input_block_hash = self.roots_by_number.remove(&digest_input_block);
					if let Some(digest_input_block_hash) = digest_input_block_hash {
						self.changed_keys.remove(&digest_input_block_hash);
					}
				}
			},
			CacheAction::Clear => {
				self.roots_by_number.clear();
				self.changed_keys.clear();
			},
		}
	}
}

impl<N> IncompleteCachedBuildData<N> {
	/// Create new cached data.
	pub(crate) fn new(is_top_level_digest: bool) -> Self {
		IncompleteCachedBuildData {
			is_top_level_digest,
			digest_input_blocks: Vec::new(),
			changed_keys: HashMap::new(),
		}
	}

	/// Returns true if this is a cached data for top-level digest CT.
	#[cfg(test)]
	pub(crate) fn is_top_level_digest(&self) -> bool {
		self.is_top_level_digest
	}

	/// Complete cached data with computed changes trie root.
	pub(crate) fn complete<H>(self, block: N, trie_root: H) -> CachedBuildData<H, N> {
		CachedBuildData {
			block,
			trie_root,
			is_top_level_digest: self.is_top_level_digest,
			digest_input_blocks: self.digest_input_blocks,
			changed_keys: self.changed_keys,
		}
	}

	/// Called for digest entries only. Set numbers of blocks that are superseded
	/// by this new entry.
	///
	/// If/when this build data is committed to the cache, entries for these blocks
	/// will be removed from the cache.
	pub(crate) fn set_digest_input_blocks(mut self, digest_input_blocks: Vec<N>) -> Self {
		self.digest_input_blocks = digest_input_blocks;
		self
	}

	/// Insert changed keys of given storage into cached data.
	pub(crate) fn insert(
		mut self,
		storage_key: Option<Vec<u8>>,
		changed_keys: HashSet<Vec<u8>>,
	) -> Self {
		if !self.is_top_level_digest {
			self.changed_keys.insert(storage_key, changed_keys);
		}
		self
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn updated_keys_are_stored_when_non_top_level_digest_is_built() {
		let mut data = IncompleteCachedBuildData::<u32>::new(false);
		data = data.insert(None, vec![vec![1]].into_iter().collect());
		assert_eq!(data.changed_keys.len(), 1);

		let mut cache = BuildCache::new();
		cache.perform(CacheAction::CacheBuildData(data.complete(1, 1)));
		assert_eq!(cache.changed_keys.len(), 1);
		assert_eq!(
			cache.get(&1).unwrap().clone(),
			vec![(None, vec![vec![1]].into_iter().collect())].into_iter().collect(),
		);
	}

	#[test]
	fn updated_keys_are_not_stored_when_top_level_digest_is_built() {
		let mut data = IncompleteCachedBuildData::<u32>::new(true);
		data = data.insert(None, vec![vec![1]].into_iter().collect());
		assert_eq!(data.changed_keys.len(), 0);

		let mut cache = BuildCache::new();
		cache.perform(CacheAction::CacheBuildData(data.complete(1, 1)));
		assert_eq!(cache.changed_keys.len(), 0);
		assert_eq!(cache.get(&1), None);
	}

	#[test]
	fn obsolete_entries_are_purged_when_new_ct_is_built() {
		let mut cache = BuildCache::<u32, u32>::new();
		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.insert(None, vec![vec![1]].into_iter().collect())
			.complete(1, 1)));
		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.insert(None, vec![vec![2]].into_iter().collect())
			.complete(2, 2)));
		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.insert(None, vec![vec![3]].into_iter().collect())
			.complete(3, 3)));

		assert_eq!(cache.changed_keys.len(), 3);

		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.set_digest_input_blocks(vec![1, 2, 3])
			.complete(4, 4)));

		assert_eq!(cache.changed_keys.len(), 1);

		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.insert(None, vec![vec![8]].into_iter().collect())
			.complete(8, 8)));
		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(false)
			.insert(None, vec![vec![12]].into_iter().collect())
			.complete(12, 12)));

		assert_eq!(cache.changed_keys.len(), 3);

		cache.perform(CacheAction::CacheBuildData(IncompleteCachedBuildData::new(true)
			.set_digest_input_blocks(vec![4, 8, 12])
			.complete(16, 16)));

		assert_eq!(cache.changed_keys.len(), 0);
	}
}