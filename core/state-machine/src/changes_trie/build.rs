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

use std::collections::{BTreeMap, BTreeSet};
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
/// Returns Ok(None) data required to prepare input pairs is not collected
/// or storage is not provided.
pub fn prepare_input<'a, B, S, H, Number>(
	backend: &B,
	storage: &'a S,
	config: &'a Configuration,
	changes: &OverlayedChanges,
	parent: &'a AnchorBlockId<H::Out, Number>,
) -> Result<Option<Vec<InputPair<Number>>>, String>
	where
		B: Backend<H>,
		S: Storage<H, Number>,
		H: Hasher,
		Number: BlockNumber,
{
	let mut input = Vec::new();
	input.extend(prepare_extrinsics_input(
		backend,
		parent.number.clone() + 1.into(),
		changes)?);
	input.extend(prepare_digest_input::<_, H, Number>(
		parent,
		config,
		storage)?);

	Ok(Some(input))
}

/// Prepare ExtrinsicIndex input pairs.
fn prepare_extrinsics_input<B, H, Number>(
	backend: &B,
	block: Number,
	changes: &OverlayedChanges,
) -> Result<impl Iterator<Item=InputPair<Number>>, String>
	where
		B: Backend<H>,
		H: Hasher,
		Number: BlockNumber,
{
	let mut extrinsic_map = BTreeMap::<Vec<u8>, BTreeSet<u32>>::new();
	for (key, val) in changes.prospective.top.iter().chain(changes.committed.top.iter()) {
		let extrinsics = match val.extrinsics {
			Some(ref extrinsics) => extrinsics,
			None => continue,
		};

		// ignore temporary changes (changes like V1 -> V2 -> V1) by checking if final value differs
		// from the original one
		let old_value = backend.storage(key).map_err(|e| format!("{}", e))?;
		let new_value = changes.storage(key).unwrap_or_default();
		if old_value.as_ref().map(|v| &**v) == new_value {
			continue;
		}

		extrinsic_map.entry(key.clone()).or_default()
			.extend(extrinsics.iter().cloned());
	}

	Ok(extrinsic_map.into_iter()
		.map(move |(key, extrinsics)| InputPair::ExtrinsicIndex(ExtrinsicIndex {
			block: block.clone(),
			key,
		}, extrinsics.iter().cloned().collect())))
}

/// Prepare DigestIndex input pairs.
fn prepare_digest_input<'a, S, H, Number>(
	parent: &'a AnchorBlockId<H::Out, Number>,
	config: &Configuration,
	storage: &'a S
) -> Result<impl Iterator<Item=InputPair<Number>> + 'a, String>
	where
		S: Storage<H, Number>,
		H: Hasher,
		H::Out: 'a,
		Number: BlockNumber,
{
	let mut digest_map = BTreeMap::<Vec<u8>, BTreeSet<Number>>::new();
	for digest_build_block in digest_build_iterator(config, parent.number.clone() + One::one()) {
		let trie_root = storage.root(parent, digest_build_block.clone())?;
		let trie_root = trie_root.ok_or_else(|| format!("No changes trie root for block {}", digest_build_block.clone()))?;
		let trie_storage = TrieBackendEssence::<_, H>::new(
			crate::changes_trie::TrieBackendStorageAdapter(storage),
			trie_root,
		);

		let extrinsic_prefix = ExtrinsicIndex::key_neutral_prefix(digest_build_block.clone());
		trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
			if let Some(InputKey::ExtrinsicIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block.clone());
			});

		let digest_prefix = DigestIndex::key_neutral_prefix(digest_build_block.clone());
		trie_storage.for_keys_with_prefix(&digest_prefix, |key|
			if let Some(InputKey::DigestIndex::<Number>(trie_key)) = Decode::decode(&mut &key[..]) {
				digest_map.entry(trie_key.key).or_default()
					.insert(digest_build_block.clone());
			});
	}

	Ok(digest_map.into_iter()
		.map(move |(key, set)| InputPair::DigestIndex(DigestIndex {
			block: parent.number.clone() + One::one(),
			key
		}, set.into_iter().collect())))
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
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&AnchorBlockId { hash: Default::default(), number: 4 },
		).unwrap();
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![103] }, vec![0, 1]),
		]));
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l1() {
		let (backend, storage, changes) = prepare_for_build();
		let config = changes.changes_trie_config.as_ref().unwrap();
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&AnchorBlockId { hash: Default::default(), number: 3 },
		).unwrap();
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
		]));
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l2() {
		let (backend, storage, changes) = prepare_for_build();
		let config = changes.changes_trie_config.as_ref().unwrap();
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&AnchorBlockId { hash: Default::default(), number: 15 },
		).unwrap();
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 16, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![100] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![101] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![102] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![103] }, vec![4]),
			InputPair::DigestIndex(DigestIndex { block: 16, key: vec![105] }, vec![4, 8]),
		]));
	}

	#[test]
	fn build_changes_trie_nodes_ignores_temporary_storage_changes() {
		let (backend, storage, mut changes) = prepare_for_build();

		// 105: has value 255 in backend && changed to 255 by changes
		changes.prospective.top.insert(vec![105], OverlayedValue {
			value: Some(vec![255]),
			extrinsics: Some(vec![1].into_iter().collect())
		});
		// 110: missing from backend, set to None in overlay
		changes.prospective.top.insert(vec![110], OverlayedValue {
			value: None,
			extrinsics: Some(vec![1].into_iter().collect())
		});

		let config = changes.changes_trie_config.as_ref().unwrap();
		let changes_trie_nodes = prepare_input(
			&backend,
			&storage,
			config,
			&changes,
			&AnchorBlockId { hash: Default::default(), number: 3 },
		).unwrap();
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 4, key: vec![103] }, vec![0, 1]),

			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![100] }, vec![1, 3]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![101] }, vec![1]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![102] }, vec![2]),
			InputPair::DigestIndex(DigestIndex { block: 4, key: vec![105] }, vec![1, 3]),
		]));
	}
}
