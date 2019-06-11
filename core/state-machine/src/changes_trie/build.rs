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

//! Structures and functions required to build changes trie for given block.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use parity_codec::Decode;
use hash_db::Hasher;
use num_traits::One;
use crate::backend::Backend;
use crate::overlayed_changes::OverlayedChanges;
use crate::trie_backend_essence::TrieBackendEssence;
use crate::changes_trie::build_iterator::digest_build_iterator;
use crate::changes_trie::input::{InputKey, InputPair, DigestIndex, ExtrinsicIndex};
use crate::changes_trie::{AnchorBlockId, Configuration, Storage, BlockNumber};

/// Prepare input pairs for building a changes trie of given block.
///
/// Returns Err if storage error has occured OR if storage haven't returned
/// required data.
pub fn prepare_input<'a, B, S, H, Number>(
	backend: &'a B,
	storage: &'a S,
	config: &'a Configuration,
	changes: &'a OverlayedChanges,
	parent: &'a AnchorBlockId<H::Out, Number>,
) -> Result<impl Iterator<Item=InputPair<Number>> + 'a, String>
	where
		B: Backend<H>,
		S: Storage<H, Number>,
		H: Hasher + 'a,
		Number: BlockNumber,
{
	let number = parent.number.clone() + One::one();
	let extrinsics_input = prepare_extrinsics_input(
		backend,
		&number,
		changes)?;
	let digest_input = prepare_digest_input::<_, H, Number>(
		parent,
		config,
		number,
		storage)?;
	Ok(extrinsics_input.chain(digest_input))
}

/// Prepare ExtrinsicIndex input pairs.
fn prepare_extrinsics_input<'a, B, H, Number>(
	backend: &'a B,
	block: &Number,
	changes: &'a OverlayedChanges,
) -> Result<impl Iterator<Item=InputPair<Number>> + 'a, String>
	where
		B: Backend<H>,
		H: Hasher,
		Number: BlockNumber,
{
	changes.committed.top.iter()
		.chain(changes.prospective.top.iter())
		.filter(|( _, v)| v.extrinsics.is_some())
		.try_fold(BTreeMap::new(), |mut map: BTreeMap<&[u8], (ExtrinsicIndex<Number>, Vec<u32>)>, (k, v)| {
			match map.entry(k) {
				Entry::Vacant(entry) => {
					// ignore temporary values (values that have null value at the end of operation
					// AND are not in storage at the beginning of operation
					if !changes.storage(k).map(|v| v.is_some()).unwrap_or_default() {
						if !backend.exists_storage(k).map_err(|e| format!("{}", e))? {
							return Ok(map);
						}
					}

					let extrinsics = v.extrinsics.as_ref()
						.expect("filtered by filter() call above; qed")
						.iter().cloned().collect();
					entry.insert((ExtrinsicIndex {
						block: block.clone(),
						key: k.to_vec(),
					}, extrinsics));
				},
				Entry::Occupied(mut entry) => {
					// we do not need to check for temporary values here, because entry is Occupied
					// AND we are checking it before insertion
					let extrinsics = &mut entry.get_mut().1;
					extrinsics.extend(
						v.extrinsics.as_ref()
							.expect("filtered by filter() call above; qed")
							.iter()
							.cloned()
					);
					extrinsics.sort_unstable();
				},
			}

			Ok(map)
		})
		.map(|pairs| pairs.into_iter().map(|(_, (k, v))| InputPair::ExtrinsicIndex(k, v)))
}

/// Prepare DigestIndex input pairs.
fn prepare_digest_input<'a, S, H, Number>(
	parent: &'a AnchorBlockId<H::Out, Number>,
	config: &Configuration,
	block: Number,
	storage: &'a S
) -> Result<impl Iterator<Item=InputPair<Number>> + 'a, String>
	where
		S: Storage<H, Number>,
		H: Hasher,
		H::Out: 'a,
		Number: BlockNumber,
{
	digest_build_iterator(config, block.clone())
		.try_fold(BTreeMap::new(), move |mut map, digest_build_block| {
			let trie_root = storage.root(parent, digest_build_block.clone())?;
			let trie_root = trie_root.ok_or_else(|| format!("No changes trie root for block {}", digest_build_block.clone()))?;
			let trie_storage = TrieBackendEssence::<_, H>::new(
				crate::changes_trie::TrieBackendStorageAdapter(storage),
				trie_root,
			);

			let mut insert_to_map = |key: Vec<u8>| {
				match map.entry(key.clone()) {
					Entry::Vacant(entry) => {
						entry.insert((DigestIndex {
							block: block.clone(),
							key,
						}, vec![digest_build_block.clone()]));
					},
					Entry::Occupied(mut entry) => {
						// DigestIndexValue must be sorted. Here we are relying on the fact that digest_build_iterator()
						// returns blocks in ascending order => we only need to check for duplicates
						//
						// is_dup_block could be true when key has been changed in both digest block
						// AND other blocks that it covers
						let is_dup_block = entry.get().1.last() == Some(&digest_build_block);
						if !is_dup_block {
							entry.get_mut().1.push(digest_build_block.clone());
						}
					},
				}
			};

			let extrinsic_prefix = ExtrinsicIndex::key_neutral_prefix(digest_build_block.clone());
			trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
				if let Some(InputKey::ExtrinsicIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
					insert_to_map(trie_key.key);
				});

			let digest_prefix = DigestIndex::key_neutral_prefix(digest_build_block.clone());
			trie_storage.for_keys_with_prefix(&digest_prefix, |key|
				if let Some(InputKey::DigestIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
					insert_to_map(trie_key.key);
				});

			Ok(map)
		})
		.map(|pairs| pairs.into_iter().map(|(_, (k, v))| InputPair::DigestIndex(k, v)))
}

#[cfg(test)]
mod test {
	use parity_codec::Encode;
	use primitives::Blake2Hasher;
	use primitives::storage::well_known_keys::EXTRINSIC_INDEX;
	use crate::backend::InMemory;
	use crate::changes_trie::storage::InMemoryStorage;
	use crate::overlayed_changes::OverlayedValue;
	use super::*;

	fn prepare_for_build() -> (InMemory<Blake2Hasher>, InMemoryStorage<Blake2Hasher, u64>, OverlayedChanges) {
		let backend: InMemory<_> = vec![
			(vec![100], vec![255]),
			(vec![101], vec![255]),
			(vec![102], vec![255]),
			(vec![103], vec![255]),
			(vec![104], vec![255]),
			(vec![105], vec![255]),
		].into_iter().collect::<::std::collections::HashMap<_, _>>().into();
		let storage = InMemoryStorage::with_inputs(vec![
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
			(4, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

				InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
				InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
				InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
				InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
			]),
			(5, Vec::new()),
			(6, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 6, key: vec![105] }, vec![2]),
			]),
			(7, Vec::new()),
			(8, vec![
				InputPair::DigestIndex(DigestIndex { block: 8, key: vec![105] }, vec![6]),
			]),
			(9, Vec::new()), (10, Vec::new()), (11, Vec::new()), (12, Vec::new()), (13, Vec::new()),
			(14, Vec::new()), (15, Vec::new()),
		]);
		let changes = OverlayedChanges {
			prospective: vec![
				(vec![100], OverlayedValue {
					value: Some(vec![200]),
					extrinsics: Some(vec![0, 2].into_iter().collect())
				}),
				(vec![103], OverlayedValue {
					value: None,
					extrinsics: Some(vec![0, 1].into_iter().collect())
				}),
			].into_iter().collect(),
			committed: vec![
				(EXTRINSIC_INDEX.to_vec(), OverlayedValue {
					value: Some(3u32.encode()),
					extrinsics: None,
				}),
				(vec![100], OverlayedValue {
					value: Some(vec![202]),
					extrinsics: Some(vec![3].into_iter().collect())
				}),
				(vec![101], OverlayedValue {
					value: Some(vec![203]),
					extrinsics: Some(vec![1].into_iter().collect())
				}),
			].into_iter().collect(),
			changes_trie_config: Some(Configuration { digest_interval: 4, digest_levels: 2 }),
		};

		(backend, storage, changes)
	}

	#[test]
	fn build_changes_trie_nodes_on_non_digest_block() {
		let (backend, storage, changes) = prepare_for_build();
		let config = changes.changes_trie_config.as_ref().unwrap();
		let parent = AnchorBlockId { hash: Default::default(), number: 4 };
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&parent,
		).unwrap();
		assert_eq!(changes_trie_nodes.collect::<Vec<InputPair<u64>>>(), vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![103] }, vec![0, 1]),
		]);
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l1() {
		let (backend, storage, changes) = prepare_for_build();
		let config = changes.changes_trie_config.as_ref().unwrap();
		let parent = AnchorBlockId { hash: Default::default(), number: 3 };
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&parent,
		).unwrap();
		assert_eq!(changes_trie_nodes.collect::<Vec<InputPair<u64>>>(), vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
		]);
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l2() {
		let (backend, storage, changes) = prepare_for_build();
		let config = changes.changes_trie_config.as_ref().unwrap();
		let parent = AnchorBlockId { hash: Default::default(), number: 15 };
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&parent,
		).unwrap();
		assert_eq!(changes_trie_nodes.collect::<Vec<InputPair<u64>>>(), vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![100] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![101] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![102] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![103] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![105] }, vec![4, 8]),
		]);
	}

	#[test]
	fn build_changes_trie_nodes_ignores_temporary_storage_values() {
		let (backend, storage, mut changes) = prepare_for_build();

		// 110: missing from backend, set to None in overlay
		changes.prospective.top.insert(vec![110], OverlayedValue {
			value: None,
			extrinsics: Some(vec![1].into_iter().collect())
		});

		let config = changes.changes_trie_config.as_ref().unwrap();
		let parent = AnchorBlockId { hash: Default::default(), number: 3 };
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&parent,
		).unwrap();
		assert_eq!(changes_trie_nodes.collect::<Vec<InputPair<u64>>>(), vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
		]);
	}
}
