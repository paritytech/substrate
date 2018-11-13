// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Changes trie pruning-related functions.

use hash_db::Hasher;
use heapsize::HeapSizeOf;
use substrate_trie::Recorder;
use proving_backend::ProvingBackendEssence;
use trie_backend_essence::TrieBackendEssence;
use changes_trie::{AnchorBlockId, Configuration, Storage};
use changes_trie::storage::TrieBackendAdapter;

/// Prune obslete changes tries. Puning happens at the same block, where highest
/// level digest is created. Pruning guarantees to save changes tries for last
/// `min_blocks_to_keep` blocks. We only prune changes tries at `max_digest_iterval`
/// ranges.
/// Returns MemoryDB that contains all deleted changes tries nodes.
pub fn prune<S: Storage<H>, H: Hasher, F: FnMut(H::Out)>(
	config: &Configuration,
	storage: &S,
	min_blocks_to_keep: u64,
	current_block: &AnchorBlockId<H::Out>,
	mut remove_trie_node: F,
)
	where
		H::Out: HeapSizeOf,
{
	// we only CAN prune at block where max-level-digest is created
	let digest_interval = match config.digest_level_at_block(current_block.number) {
		Some((digest_level, digest_interval, _)) if digest_level == config.digest_levels =>
			digest_interval,
		_ => return,
	};

	// select range for pruning
	let (first, last) = match pruning_range(min_blocks_to_keep, current_block.number, digest_interval) {
		Some((first, last)) => (first, last),
		None => return,
	};

	// delete changes trie for every block in range
	// TODO: limit `max_digest_interval` so that this cycle won't involve huge ranges
	for block in first..last+1 {
		let root = match storage.root(current_block, block) {
			Ok(Some(root)) => root,
			Ok(None) => continue,
			Err(error) => {
				// try to delete other tries
				warn!(target: "trie", "Failed to read changes trie root from DB: {}", error);
				continue;
			},
		};

		// enumerate all changes trie' keys, recording all nodes that have been 'touched'
		// (effectively - all changes trie nodes)
		let mut proof_recorder: Recorder<H::Out> = Default::default();
		{
			let mut trie = ProvingBackendEssence::<_, H> {
				backend: &TrieBackendEssence::new(TrieBackendAdapter::new(storage), root),
				proof_recorder: &mut proof_recorder,
			};
			trie.record_all_keys();
		}

		// all nodes of this changes trie should be pruned
		remove_trie_node(root);
		for node in proof_recorder.drain().into_iter().map(|n| n.hash) {
			remove_trie_node(node);
		}
	}
}

/// Select blocks range (inclusive from both ends) for pruning changes tries in.
fn pruning_range(min_blocks_to_keep: u64, block: u64, max_digest_interval: u64) -> Option<(u64, u64)> {
	// compute maximal number of high-level digests to keep
	let max_digest_intervals_to_keep = max_digest_intervals_to_keep(min_blocks_to_keep, max_digest_interval);

	// number of blocks BEFORE current block where changes tries are not pruned
	let blocks_to_keep = max_digest_intervals_to_keep.checked_mul(max_digest_interval);

	// last block for which changes trie is pruned
	let last_block_to_prune = blocks_to_keep.and_then(|b| block.checked_sub(b));
	let first_block_to_prune = last_block_to_prune.clone().and_then(|b| b.checked_sub(max_digest_interval));

	last_block_to_prune
		.and_then(|last| first_block_to_prune.map(|first| (first + 1, last)))
}

/// Select pruning delay for the changes tries. To make sure we could build a changes
/// trie at block B, we need an access to previous:
/// max_digest_interval = config.digest_interval ^ config.digest_levels
/// blocks. So we can only prune blocks that are earlier than B - max_digest_interval.
/// The pruning_delay stands for number of max_digest_interval-s that we want to keep:
/// 0 or 1: means that only last changes trie is guaranteed to exists;
/// 2: the last chnages trie + previous changes trie
/// ...
fn max_digest_intervals_to_keep(min_blocks_to_keep: u64, max_digest_interval: u64) -> u64 {
	// config.digest_level_at_block ensures that it is not zero
	debug_assert!(max_digest_interval != 0);

	let max_digest_intervals_to_keep = min_blocks_to_keep / max_digest_interval;
	if max_digest_intervals_to_keep == 0 {
		1
	} else {
		max_digest_intervals_to_keep
	}
}

#[cfg(test)]
mod tests {
	use std::collections::HashSet;
	use trie::MemoryDB;
	use primitives::Blake2Hasher;
	use backend::insert_into_memory_db;
	use changes_trie::storage::InMemoryStorage;
	use super::*;

	fn prune_by_collect<S: Storage<H>, H: Hasher>(
		config: &Configuration,
		storage: &S,
		min_blocks_to_keep: u64,
		current_block: u64,
	) -> HashSet<H::Out>
		where
			H::Out: HeapSizeOf,
	{
		let mut pruned_trie_nodes = HashSet::new();
		prune(config, storage, min_blocks_to_keep, &AnchorBlockId { hash: Default::default(), number: current_block },
			|node| { pruned_trie_nodes.insert(node); });
		pruned_trie_nodes
	}


	#[test]
	fn prune_works() {
		fn prepare_storage() -> InMemoryStorage<Blake2Hasher> {
			let mut mdb1 = MemoryDB::<Blake2Hasher>::default();
			let root1 = insert_into_memory_db::<Blake2Hasher, _>(&mut mdb1, vec![(vec![10], vec![20])]).unwrap();
			let mut mdb2 = MemoryDB::<Blake2Hasher>::default();
			let root2 = insert_into_memory_db::<Blake2Hasher, _>(&mut mdb2, vec![(vec![11], vec![21]), (vec![12], vec![22])]).unwrap();
			let mut mdb3 = MemoryDB::<Blake2Hasher>::default();
			let root3 = insert_into_memory_db::<Blake2Hasher, _>(&mut mdb3, vec![(vec![13], vec![23]), (vec![14], vec![24])]).unwrap();
			let mut mdb4 = MemoryDB::<Blake2Hasher>::default();
			let root4 = insert_into_memory_db::<Blake2Hasher, _>(&mut mdb4, vec![(vec![15], vec![25])]).unwrap();
			let storage = InMemoryStorage::new();
			storage.insert(65, root1, mdb1);
			storage.insert(66, root2, mdb2);
			storage.insert(67, root3, mdb3);
			storage.insert(68, root4, mdb4);

			storage
		}

		// l1-digest is created every 2 blocks
		// l2-digest is created every 4 blocks
		// we do not want to keep any additional changes tries
		// => only one l2-digest is saved AND it is pruned once next is created
		let config = Configuration { digest_interval: 2, digest_levels: 2 };
		let storage = prepare_storage();
		assert!(prune_by_collect(&config, &storage, 0, 69).is_empty());
		assert!(prune_by_collect(&config, &storage, 0, 70).is_empty());
		assert!(prune_by_collect(&config, &storage, 0, 71).is_empty());
		let non_empty = prune_by_collect(&config, &storage, 0, 72);
		assert!(!non_empty.is_empty());
		storage.remove_from_storage(&non_empty);
		assert!(storage.into_mdb().drain().is_empty());

		// l1-digest is created every 2 blocks
		// l2-digest is created every 4 blocks
		// we want keep 1 additional changes tries
		let config = Configuration { digest_interval: 2, digest_levels: 2 };
		let storage = prepare_storage();
		assert!(prune_by_collect(&config, &storage, 8, 69).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 70).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 71).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 72).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 73).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 74).is_empty());
		assert!(prune_by_collect(&config, &storage, 8, 75).is_empty());
		let non_empty = prune_by_collect(&config, &storage, 8, 76);
		assert!(!non_empty.is_empty());
		storage.remove_from_storage(&non_empty);
		assert!(storage.into_mdb().drain().is_empty());

		// l1-digest is created every 2 blocks
		// we want keep 2 additional changes tries
		let config = Configuration { digest_interval: 2, digest_levels: 1 };
		let storage = prepare_storage();
		assert!(prune_by_collect(&config, &storage, 4, 69).is_empty());
		let non_empty = prune_by_collect(&config, &storage, 4, 70);
		assert!(!non_empty.is_empty());
		storage.remove_from_storage(&non_empty);
		assert!(prune_by_collect(&config, &storage, 4, 71).is_empty());
		let non_empty = prune_by_collect(&config, &storage, 4, 72);
		assert!(!non_empty.is_empty());
		storage.remove_from_storage(&non_empty);
		assert!(storage.into_mdb().drain().is_empty());
	}

	#[test]
	fn pruning_range_works() {
		assert_eq!(pruning_range(2, 0, 100), None);
		assert_eq!(pruning_range(2, 30, 100), None);
		assert_eq!(pruning_range(::std::u64::MAX, 1024, 1), None);
		assert_eq!(pruning_range(1, 1024, ::std::u64::MAX), None);
		assert_eq!(pruning_range(::std::u64::MAX, 1024, ::std::u64::MAX), None);
		assert_eq!(pruning_range(1024, 512, 512), None);
		assert_eq!(pruning_range(1024, 1024, 512), None);

		// when we do not want to keep any highest-level-digests
		// (system forces to keep at least one)
		assert_eq!(pruning_range(0, 32, 16), Some((1, 16)));
		assert_eq!(pruning_range(0, 64, 16), Some((33, 48)));
		// when we want to keep 1 (last) highest-level-digest
		assert_eq!(pruning_range(16, 32, 16), Some((1, 16)));
		assert_eq!(pruning_range(16, 64, 16), Some((33, 48)));
		// when we want to keep 1 (last) + 1 additional level digests
		assert_eq!(pruning_range(1024, 1536, 512), Some((1, 512)));
		assert_eq!(pruning_range(1024, 2048, 512), Some((513, 1024)));
	}

	#[test]
	fn max_digest_intervals_to_keep_works() {
		assert_eq!(max_digest_intervals_to_keep(1024, 1025), 1);
		assert_eq!(max_digest_intervals_to_keep(1024, 1023), 1);
		assert_eq!(max_digest_intervals_to_keep(1024, 512), 2);
		assert_eq!(max_digest_intervals_to_keep(1024, 511), 2);
		assert_eq!(max_digest_intervals_to_keep(1024, 100), 10);
	}
}
