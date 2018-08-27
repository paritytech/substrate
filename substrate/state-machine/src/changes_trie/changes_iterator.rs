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
use hashdb::Hasher;
use heapsize::HeapSizeOf;
use patricia_trie::{NodeCodec, Recorder};
use changes_trie::{Configuration, Storage};
use changes_trie::input::{DigestIndex, ExtrinsicIndex, DigestIndexValue, ExtrinsicIndexValue};
use changes_trie::storage::ProofCheckStorage;
use proving_backend::ProvingBackendEssence;
use trie_backend_essence::{TrieBackendStorage, TrieBackendEssence};

/// Return changes of given key at given blocks range.
pub fn key_changes<H: Hasher, C: NodeCodec<H>>(
	config: &Configuration,
	storage: Arc<Storage<H>>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8],
) -> Vec<(u64, u32)> where H::Out: HeapSizeOf {
	DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage: storage.clone(),
			storage,
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
		_codec: ::std::marker::PhantomData::<C>::default(),
	}.collect()
}

/// Returns proof of changes of given key at given blocks range.
pub fn key_changes_proof<H: Hasher, C: NodeCodec<H>>(
	config: &Configuration,
	storage: Arc<Storage<H>>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8],
) -> Vec<Vec<u8>> where H::Out: HeapSizeOf {
	let mut iter = ProvingDrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage: storage.clone(),
			storage,
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
		proof_recorder: Default::default(),
		_codec: ::std::marker::PhantomData::<C>::default(),
	};

	// iterate to collect proof
	while iter.next().is_some() { }

	iter.extract_proof()
}

/// Check key changes proog and return changes of the key at given blocks range.
pub fn key_changes_proof_check<H: 'static + Hasher, C: NodeCodec<H>>(
	config: &Configuration,
	roots_storage: Arc<Storage<H>>, // TODO: use RootsStorage is only used to gather root
	proof: Vec<Vec<u8>>,
	begin: u64,
	end: u64,
	max: u64,
	key: &[u8]
) -> Vec<(u64, u32)> where H::Out: HeapSizeOf {
/*
		let root = self.roots_storage.root(block)?;

		// every root that we're asking for MUST be a part of proof db
		if let Some(root) = root {
			if !self.proof_db.contains(&root) {
				return Err("TODO".into());
			}
		}

		Ok(root)

*/
	let storage = Arc::new(ProofCheckStorage::new(proof));
	DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage,
			storage,
			surface: surface_iterator(config, max, begin, end),

			extrinsics: Default::default(),
			blocks: Default::default(),
		},
		_codec: ::std::marker::PhantomData::<C>::default(),
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
pub struct DrilldownIteratorEssence<'a, H: Hasher> {
	key: &'a [u8],
	roots_storage: Arc<Storage<H>>,
	storage: Arc<Storage<H>>,
	surface: SurfaceIterator<'a>,

	extrinsics: VecDeque<(u64, u32)>,
	blocks: VecDeque<(u64, u8)>,
}

impl<'a, H: Hasher> DrilldownIteratorEssence<'a, H> {
	pub fn next<F>(&mut self, mut trie_reader: F) -> Option<(u64, u32)>
		where
			F: FnMut(TrieBackendStorage<H>, H::Out, &[u8]) -> Result<Option<Vec<u8>>, String>,
	{
		loop {
			if let Some((block, extrinsic)) = self.extrinsics.pop_front() {
				return Some((block, extrinsic));
			}

			if let Some((block, level)) = self.blocks.pop_front() {
				if let Some(trie_root) = self.roots_storage.root(block).expect("TODO") {
					let extrinsics_key = ExtrinsicIndex { block, key: self.key.to_vec() }.encode();
					let extrinsics = trie_reader(TrieBackendStorage::ChangesTrieStorage(self.storage.clone()), trie_root, &extrinsics_key);
					if let Some(extrinsics) = extrinsics.expect("TODO") {
						let extrinsics: Option<ExtrinsicIndexValue> = Decode::decode(&mut &extrinsics[..]);
						if let Some(extrinsics) = extrinsics {
							self.extrinsics.extend(extrinsics.into_iter().rev().map(|e| (block, e)));
						}
					}

					let blocks_key = DigestIndex { block, key: self.key.to_vec() }.encode();
					let blocks = trie_reader(TrieBackendStorage::ChangesTrieStorage(self.storage.clone()), trie_root, &blocks_key);
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
struct DrilldownIterator<'a, H: Hasher, C: NodeCodec<H>> {
	essence: DrilldownIteratorEssence<'a, H>,
	_codec: ::std::marker::PhantomData<C>,
}

impl<'a, H: Hasher, C: NodeCodec<H>> Iterator for DrilldownIterator<'a, H, C> where H::Out: HeapSizeOf {
	type Item = (u64, u32);

	fn next(&mut self) -> Option<Self::Item> {
		self.essence.next(|storage, root, key|
			TrieBackendEssence::<H, C>::new(storage, root).storage(key))
	}
}

/// Proving drilldown iterator.
struct ProvingDrilldownIterator<'a, H: Hasher, C: NodeCodec<H>> {
	essence: DrilldownIteratorEssence<'a, H>,
	proof_recorder: RefCell<Recorder<H::Out>>,
	_codec: ::std::marker::PhantomData<C>,
}

impl<'a, H: Hasher, C: NodeCodec<H>> ProvingDrilldownIterator<'a, H, C> {
	/// Consume the iterator, extracting the gathered proof in lexicographical order
	/// by value.
	pub fn extract_proof(self) -> Vec<Vec<u8>> {
		self.proof_recorder.into_inner().drain()
			.into_iter()
			.map(|n| n.data.to_vec())
			.collect()
	}
}

impl<'a, H: Hasher, C: NodeCodec<H>> Iterator for ProvingDrilldownIterator<'a, H, C> where H::Out: HeapSizeOf {
	type Item = (u64, u32);

	fn next(&mut self) -> Option<Self::Item> {
		let proof_recorder = &mut *self.proof_recorder.try_borrow_mut()
			.expect("only fails when already borrowed; storage() is non-reentrant; qed");
		self.essence.next(|storage, root, key|
			ProvingBackendEssence::<H, C> {
				backend: &TrieBackendEssence::new(storage, root),
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
	use primitives::{KeccakHasher, RlpCodec};
	use changes_trie::input::InputPair;
	use changes_trie::storage::InMemoryStorage;
	use super::*;

	fn prepare_for_drilldown() -> (Configuration, Arc<InMemoryStorage<KeccakHasher, RlpCodec>>) {
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
		let drilldown_result = key_changes::<KeccakHasher, RlpCodec>(&config, storage.clone(), 0, 100, 1000, &[42]);

		assert_eq!(drilldown_result, vec![(8, 2), (8, 1), (6, 3), (3, 0)]);
	}

	#[test]
	fn proving_drilldown_iterator_works() {
		// happens on remote full node:

		// create drilldown iterator that records all trie nodes during drilldown
		let (remote_config, remote_storage) = prepare_for_drilldown();
		let remote_proof = key_changes_proof::<KeccakHasher, RlpCodec>(&remote_config, remote_storage,
			0, 100, 1000, &[42]);

		// happens on local light node:

		// create drilldown iterator that works the same, but only depends on trie
		let (local_config, mut local_storage) = prepare_for_drilldown();
		Arc::get_mut(&mut local_storage).unwrap().clear_storage();
		let local_result = key_changes_proof_check::<KeccakHasher, RlpCodec>(&local_config, local_storage, remote_proof,
			0, 100, 1000, &[42]);

		// check that drilldown result is the same as if it was happening at the full node
		assert_eq!(local_result, vec![(8, 2), (8, 1), (6, 3), (3, 0)]);
	}
}
