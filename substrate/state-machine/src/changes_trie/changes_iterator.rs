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

//! Functions + iterator that traverses changes tries and returns all
//! (block, extrinsic) pairs where given key has been changed.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::Arc;
use codec::{Decode, Encode};
use ethereum_types::H256 as TrieH256;
use patricia_trie::Recorder;
use changes_trie::{Configuration, Storage};
use changes_trie::input::{DigestIndex, ExtrinsicIndex, DigestIndexValue, ExtrinsicIndexValue};
use changes_trie::storage::{TrieStorageAdapter, ProofCheckStorage};
use proving_backend::ProvingBackendEssence;
use trie_backend_essence::TrieBackendEssence;
use {Storage as TrieStorage};

/// Return changes of given key at given blocks range.
pub fn key_changes(
	config: &Configuration,
	storage: Arc<Storage>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8],
) -> Vec<(u64, u32)> {
	DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			storage: Arc::new(TrieStorageAdapter(storage)),
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
	}.collect()
}

/// Returns proof of changes of given key at given blocks range.
pub fn key_changes_proof(
	config: &Configuration,
	storage: Arc<Storage>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8],
) -> Vec<Vec<u8>> {
	let mut iter = ProvingDrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			storage: Arc::new(TrieStorageAdapter(storage)),
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
		proof_recorder: Default::default(),
	};

	// iterate to collect proof
	while iter.next().is_some() { }

	iter.extract_proof()
}

/// Check key changes proog and return changes of the key at given blocks range.
pub fn key_changes_proof_check(
	config: &Configuration,
	roots_storage: Arc<Storage>, // TODO: use RootsStorage is only used to gather root
	proof: Vec<Vec<u8>>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8]
) -> Vec<(u64, u32)> {
	DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			storage: Arc::new(TrieStorageAdapter(
				Arc::new(ProofCheckStorage::new(roots_storage, proof))
			)),
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
	}.collect()
}


/// Surface iterator.
pub struct SurfaceIterator<'a> {
	config: &'a Configuration,
	begin: u64,
	max: u64,
	current: Option<u64>,
	current_begin: u64,
	digest_step: u64,
	digest_level: u8,
}

impl<'a> Iterator for SurfaceIterator<'a> {
	type Item = (u64, u8);

	fn next(&mut self) -> Option<Self::Item> {
		let current = self.current?;
		let digest_level = self.digest_level;

		if current < self.digest_step {
			self.current = None;
		}
		else {
			let next = current - self.digest_step;
			if next == 0 || next < self.begin {
				self.current = None;
			}
			else if next > self.current_begin {
				self.current = Some(next);
			} else {
				let (current, current_begin, digest_step, digest_level) =
					lower_bound_max_digest(self.config, self.max, self.begin, next);

				self.current = Some(current);
				self.current_begin = current_begin;
				self.digest_step = digest_step;
				self.digest_level = digest_level;
			}
		}

		Some((current, digest_level))
	}
}

/// Drilldown iterator essence.
pub struct DrilldownIteratorEssence<'a> {
	key: &'a [u8],
	storage: Arc<TrieStorageAdapter>,
	surface: SurfaceIterator<'a>,

	extrinsics: VecDeque<(u64, u32)>,
	blocks: VecDeque<(u64, u8)>,
}

impl<'a> DrilldownIteratorEssence<'a> {
	pub fn next<F>(&mut self, mut trie_reader: F) -> Option<(u64, u32)>
		where
			F: FnMut(Arc<TrieStorage>, TrieH256, &[u8]) -> Result<Option<Vec<u8>>, String>,
	{
		loop {
			if let Some((block, extrinsic)) = self.extrinsics.pop_front() {
				return Some((block, extrinsic));
			}

			if let Some((block, level)) = self.blocks.pop_front() {
				if let Some(trie_root) = self.storage.0.root(block).expect("TODO") {
					let extrinsics_key = ExtrinsicIndex { block, key: self.key.to_vec() }.encode();
					let extrinsics = trie_reader(self.storage.clone(), trie_root, &extrinsics_key);
					if let Some(extrinsics) = extrinsics.expect("TODO") {
						let extrinsics: Option<ExtrinsicIndexValue> = Decode::decode(&mut &extrinsics[..]);
						if let Some(extrinsics) = extrinsics {
							self.extrinsics.extend(extrinsics.into_iter().rev().map(|e| (block, e)));
						}
					}

					let blocks_key = DigestIndex { block, key: self.key.to_vec() }.encode();
					let blocks = trie_reader(self.storage.clone(), trie_root, &blocks_key);
					if let Some(blocks) = blocks.expect("TODO") {
						let blocks: Option<DigestIndexValue> = Decode::decode(&mut &blocks[..]);
						if let Some(blocks) = blocks {
							self.blocks.extend(blocks.into_iter().rev().map(|b| (b, level - 1)));
						}
					}
				}

				continue;
			}

			self.blocks.push_back(self.surface.next()?);
		}
	}
}

/// Drilldown iterator.
struct DrilldownIterator<'a> {
	essence: DrilldownIteratorEssence<'a>,
}

impl<'a> Iterator for DrilldownIterator<'a> {
	type Item = (u64, u32);

	fn next(&mut self) -> Option<Self::Item> {
		self.essence.next(|storage, root, key|
			TrieBackendEssence::with_storage(storage, root).storage(key))
	}
}

/// Proving drilldown iterator.
struct ProvingDrilldownIterator<'a> {
	essence: DrilldownIteratorEssence<'a>,
	proof_recorder: RefCell<Recorder>,
}

impl<'a> ProvingDrilldownIterator<'a> {
	/// Consume the iterator, extracting the gathered proof in lexicographical order
	/// by value.
	pub fn extract_proof(self) -> Vec<Vec<u8>> {
		self.proof_recorder.into_inner().drain()
			.into_iter()
			.map(|n| n.data.to_vec())
			.collect()
	}
}

impl<'a> Iterator for ProvingDrilldownIterator<'a> {
	type Item = (u64, u32);

	fn next(&mut self) -> Option<Self::Item> {
		let proof_recorder = &mut *self.proof_recorder.try_borrow_mut()
			.expect("only fails when already borrowed; storage() is non-reentrant; qed");
		self.essence.next(|storage, root, key|
			ProvingBackendEssence {
				backend: &TrieBackendEssence::with_storage(storage, root),
				proof_recorder,
			}.storage(key))
	}
}

/// TODO
fn surface_iterator<'a>(config: &'a Configuration, max: u64, begin: u64, end: u64) -> SurfaceIterator<'a> {
	let (current, current_begin, digest_step, digest_level) = lower_bound_max_digest(config, max, begin, end);
	SurfaceIterator {
		config,
		begin,
		max,
		current: Some(current),
		current_begin,
		digest_step,
		digest_level,
	}
}

/// Returns parameters of highest level digest block that includes the end of given range
/// and tends to include the whole range.
fn lower_bound_max_digest(
	config: &Configuration,
	max: u64,
	begin: u64,
	end: u64,
) -> (u64, u64, u64, u8) {
	assert!(end <= max);
	assert!(begin <= end);

	// TODO: bgin || end == zero
	let mut digest_level = 0u8;
	let mut digest_step = 1u64;
	let mut digest_interval = 0u64;
	let mut current = end;
	let mut current_begin = begin;
	if begin != end {
		while digest_level != config.digest_levels {
			let new_digest_level = digest_level + 1;
			let new_digest_step = digest_step * config.digest_interval;
			let new_digest_interval = { if digest_interval == 0 { 1 } else { digest_interval } } * config.digest_interval;
			let new_digest_begin = ((current - 1) / new_digest_interval) * new_digest_interval;
			let new_digest_end = new_digest_begin + new_digest_interval;
			let new_current = new_digest_begin + new_digest_interval;

			if new_digest_end > max {
				if begin < new_digest_begin {
					current_begin = new_digest_begin;
				}
				break;
			}

			digest_level = new_digest_level;
			digest_step = new_digest_step;
			digest_interval = new_digest_interval;
			current = new_current;
			current_begin = new_digest_begin;

			if new_digest_begin <= begin && new_digest_end >= end {
				break;
			}
		}
	}

	(
		current,
		current_begin,
		digest_step,
		digest_level,
	)
}

#[cfg(test)]
mod tests {
	use changes_trie::input::InputPair;
	use changes_trie::storage::InMemoryStorage;
	use super::*;

	fn prepare_for_drilldown() -> (Configuration, Arc<InMemoryStorage>) {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };
		let backend = Arc::new(vec![
			// digest: 1..4 => [(3, 0)]
			(1, vec![]),
			(2, vec![]),
			(3, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 3, key: vec![42] }, vec![0]),
			]),
			(4, vec![
				InputPair::DigestIndex(DigestIndex { block: 4, key: vec![42] }, vec![3]),
			]),
			// digest: 5..8 => [(6, 3), (8, 1+2)]
			(5, vec![]),
			(6, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 6, key: vec![42] }, vec![3]),
			]),
			(7, vec![]),
			(8, vec![
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 8, key: vec![42] }, vec![1, 2]),
				InputPair::DigestIndex(DigestIndex { block: 8, key: vec![42] }, vec![6]),
			]),
			// digest: 9..12 => []
			(9, vec![]),
			(10, vec![]),
			(11, vec![]),
			(12, vec![]),
			// digest: 0..16 => [4, 8]
			(13, vec![]),
			(14, vec![]),
			(15, vec![]),
			(16, vec![
				InputPair::DigestIndex(DigestIndex { block: 16, key: vec![42] }, vec![4, 8]),
			]),
		].into());

		(config, backend)
	}

	#[test]
	fn drilldown_iterator_works() {
		let (config, storage) = prepare_for_drilldown();
		let iter = key_changes(&config, storage.clone(), 0, 100, 1000, &[42]);
		let iter = DrilldownIterator {
			essence: DrilldownIteratorEssence {
				key: &[42],
				storage: Arc::new(TrieStorageAdapter(storage)),
				surface: surface_iterator(&config, 1000, 0, 100),
				extrinsics: Default::default(),
				blocks: Default::default(),
			},
		};

		assert_eq!(iter.collect::<Vec<_>>(), vec![(8, 2), (8, 1), (6, 3), (3, 0)]);
	}

	#[test]
	fn proving_drilldown_iterator_works() {
		// happens on remote full node:

		// create drilldown iterator that records all trie nodes during drilldown
		let (remote_config, remote_storage) = prepare_for_drilldown();
		let local_config = remote_config.clone();
		let local_roots_storage = remote_storage.clone();
		let mut remote_iter = ProvingDrilldownIterator {
			essence: DrilldownIteratorEssence {
				key: &[42],
				storage: Arc::new(TrieStorageAdapter(remote_storage)),
				surface: surface_iterator(&remote_config, 1000, 0, 100),
				extrinsics: Default::default(),
				blocks: Default::default(),
			},
			proof_recorder: RefCell::new(Recorder::new()),
		};

		// collect changes proof
		while remote_iter.next().is_some() {}

		// extract changes proof
		let remote_proof = remote_iter.extract_proof();
		assert!(!remote_proof.is_empty());

		// happens on local light node:

		// create drilldown iterator that works the same, but only depends on trie
		let local_proof_check_storage = Arc::new(ProofCheckStorage::new(local_roots_storage, remote_proof));
		let local_iter = DrilldownIterator {
			essence: DrilldownIteratorEssence {
				key: &[42],
				storage: Arc::new(TrieStorageAdapter(local_proof_check_storage)),
				surface: surface_iterator(&local_config, 1000, 0, 100),
				extrinsics: Default::default(),
				blocks: Default::default(),
			},
		};

		// check that drilldown result is the same as if it was happening at the full node
		assert_eq!(local_iter.collect::<Vec<_>>(), vec![(8, 2), (8, 1), (6, 3), (3, 0)]);
	}
}
