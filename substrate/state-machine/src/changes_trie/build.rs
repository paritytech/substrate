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

//! Structures and functions required to build changes trie for given block.

use std::collections::{BTreeMap, BTreeSet};
use codec::Decode;
use hashdb::Hasher;
use heapsize::HeapSizeOf;
use patricia_trie::NodeCodec;
use overlayed_changes::{OverlayedChanges, ExtrinsicChanges};
use trie_backend_essence::{TrieBackendStorage, TrieBackendEssence};
use changes_trie::build_iterator::digest_build_iterator;
use changes_trie::input::{InputKey, InputPair, DigestIndex, ExtrinsicIndex};
use changes_trie::{Configuration, Storage};

/// Prepare input pairs for building a changes trie of given block.
/// Returns None if there's no data required to prepare input pairs.
pub fn prepare_input<'a, S, H, C>(storage: Option<&'a S>, changes: &OverlayedChanges) -> Option<Vec<InputPair>>
	where
		S: Storage<H>,
		&'a S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: HeapSizeOf,
		C: NodeCodec<H>,
{
	// TODO: do not include temporary (whice were created and deleted in the same block) values

	let storage = storage?;
	let extrinsic_changes = changes.extrinsic_changes.as_ref()?;

	let mut input = Vec::new();
	input.extend(prepare_extrinsics_input(extrinsic_changes));
	// TODO: input.extend(prepare_digest_input(extrinsic_changes.block, &extrinsic_changes.changes_trie_config, storage).expect("TODO"));
input.extend(prepare_digest_input::<S, H, C>(extrinsic_changes.block, &Configuration { digest_interval: extrinsic_changes.changes_trie_config.digest_interval, digest_levels: extrinsic_changes.changes_trie_config.digest_levels }, storage).expect("TODO"));
	Some(input)
}

/// Prepare ExtrinsicIndex input pairs.
fn prepare_extrinsics_input(extrinsic_changes: &ExtrinsicChanges) -> impl Iterator<Item=InputPair> {
	let mut extrinsic_map = BTreeMap::<Vec<u8>, BTreeSet<u32>>::new();
	for (key, extrinsics) in extrinsic_changes.prospective.iter().chain(extrinsic_changes.committed.iter()) {
		extrinsic_map.entry(key.clone()).or_default()
			.extend(extrinsics);
	}

	let block = extrinsic_changes.block;
	extrinsic_map.into_iter()
		.map(move |(key, extrinsics)| InputPair::ExtrinsicIndex(ExtrinsicIndex {
			block,
			key: key.clone(),
		}, extrinsics.iter().cloned().collect()))
}

/// Prepare DigestIndex input pairs.
fn prepare_digest_input<'a, S, H, C>(block: u64, config: &Configuration, storage: &'a S) -> Result<impl Iterator<Item=InputPair>, String>
	where
		S: Storage<H>,
		&'a S: TrieBackendStorage<H>,
		H: Hasher,
		H::Out: HeapSizeOf,
		C: NodeCodec<H>,
{
	let mut digest_map = BTreeMap::<Vec<u8>, BTreeSet<u64>>::new();
	for digest_build_block in digest_build_iterator(config, block) {
		let trie_root = storage.root(digest_build_block)?;
		let trie_root = trie_root.ok_or_else(|| format!("No changes trie root for block {}", digest_build_block))?;
//		let trie_storage_adapter = Arc::new(TrieStorageAdapter(storage.clone()));
//		let trie_storage = TrieBackendEssence::<H, C>::with_storage(trie_storage_adapter, trie_root);
		//let trie_backend_storage: &TrieBackendStorage<H> = storage;
		let trie_storage = TrieBackendEssence::<_, H, C>::new(storage, trie_root);

/*		trie_storage.for_keys_with_prefix(&[], |key| match Decode::decode(&mut &key[..]) {
			Some(InputKey::ExtrinsicIndex(trie_key)) => {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block);
			},
			Some(InputKey::DigestIndex(trie_key)) => {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block);
			},
			_ => (),
		});*/

		let extrinsic_prefix = ExtrinsicIndex::key_neutral_prefix(digest_build_block);
		trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
			if let Some(InputKey::ExtrinsicIndex(trie_key)) = Decode::decode(&mut &key[..]) {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block);
			});

		let digest_prefix = DigestIndex::key_neutral_prefix(digest_build_block);
		trie_storage.for_keys_with_prefix(&digest_prefix, |key|
			if let Some(InputKey::DigestIndex(trie_key)) = Decode::decode(&mut &key[..]) {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block);
			});
	}

	Ok(digest_map.into_iter()
		.map(move |(key, set)| InputPair::DigestIndex(DigestIndex {
			block,
			key
		}, set.into_iter().collect())))
}

#[cfg(test)]
mod test {
	use primitives::{KeccakHasher, RlpCodec};
	use changes_trie::storage::InMemoryStorage;
	use super::*;

	fn prepare_for_build(block: u64) -> (InMemoryStorage<KeccakHasher>, OverlayedChanges) {
		let backend = InMemoryStorage::with_inputs::<RlpCodec>(vec![
			(1, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![100] }, vec![1, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![101] }, vec![0, 2]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![105] }, vec![0, 2, 4]),
			]),
			(2, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 2, key: vec![102] }, vec![0]),
			]),
			(3, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 3, key: vec![100] }, vec![0]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 3, key: vec![105] }, vec![1]),
			]),
		]);
		let changes = OverlayedChanges {
			prospective: vec![
				(vec![100], Some(vec![200])),
				(vec![103], None),
			].into_iter().collect(),
			committed: vec![
				(vec![100], Some(vec![202])),
				(vec![101], Some(vec![203])),
			].into_iter().collect(),
			extrinsic_changes: Some(ExtrinsicChanges {
				changes_trie_config: Configuration { digest_interval: 4, digest_levels: 1 },
				block,
				extrinsic_index: 0,
				prospective: vec![
					(vec![100], vec![0, 2].into_iter().collect()),
					(vec![103], vec![0, 1].into_iter().collect()),
				].into_iter().collect(),
				committed: vec![
					(vec![100], vec![3].into_iter().collect()),
					(vec![101], vec![1].into_iter().collect()),
				].into_iter().collect(),
			}),
		};

		(backend, changes)
	}

	#[test]
	fn build_changes_trie_nodes_on_non_digest_block() {
		let (storage, changes) = prepare_for_build(5);
		let changes_trie_nodes = prepare_input::<_, _, RlpCodec>(Some(&storage), &changes);
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![103] }, vec![0, 1]),
		]));
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l1() {
		// TODO
		/*let (storage, changes) = prepare_for_build(4);
		let changes_trie_nodes = prepare_input(Some(storage), &changes);
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
		]));*/
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l2() {
		// TODO
	}

	#[test]
	fn build_changes_trie_nodes_ignores_temporary_storage_values() {
		// TODO
	}
}
