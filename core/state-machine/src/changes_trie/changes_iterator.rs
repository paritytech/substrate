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

//! Functions + iterator that traverses changes tries and returns all
//! (block, extrinsic) pairs where given key has been changed.

use std::cell::RefCell;
use std::collections::VecDeque;
use parity_codec::{Decode, Encode};
use hash_db::{HashDB, Hasher};
use trie::{Recorder, MemoryDB};
use crate::changes_trie::{AnchorBlockId, Configuration, RootsStorage, Storage};
use crate::changes_trie::input::{DigestIndex, ExtrinsicIndex, DigestIndexValue, ExtrinsicIndexValue};
use crate::changes_trie::storage::{TrieBackendAdapter, InMemoryStorage};
use crate::proving_backend::ProvingBackendEssence;
use crate::trie_backend_essence::{TrieBackendEssence};

/// Return changes of given key at given blocks range.
/// `max` is the number of best known block.
/// Changes are returned in descending order (i.e. last block comes first).
pub fn key_changes<'a, S: Storage<H>, H: Hasher>(
	config: &'a Configuration,
	storage: &'a S,
	begin: u64,
	end: &'a AnchorBlockId<H::Out>,
	max: u64,
	key: &'a [u8],
) -> Result<DrilldownIterator<'a, S, S, H>, String> {
	// we can't query any roots before root
	let max = ::std::cmp::min(max, end.number);

	Ok(DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage: storage,
			storage,
			begin,
			end,
			surface: surface_iterator(config, max, begin, end.number)?,

			extrinsics: Default::default(),
			blocks: Default::default(),

			_hasher: ::std::marker::PhantomData::<H>::default(),
		},
	})
}

/// Returns proof of changes of given key at given blocks range.
/// `max` is the number of best known block.
pub fn key_changes_proof<S: Storage<H>, H: Hasher>(
	config: &Configuration,
	storage: &S,
	begin: u64,
	end: &AnchorBlockId<H::Out>,
	max: u64,
	key: &[u8],
) -> Result<Vec<Vec<u8>>, String> {
	// we can't query any roots before root
	let max = ::std::cmp::min(max, end.number);

	let mut iter = ProvingDrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage: storage.clone(),
			storage,
			begin,
			end,
			surface: surface_iterator(config, max, begin, end.number)?,

			extrinsics: Default::default(),
			blocks: Default::default(),

			_hasher: ::std::marker::PhantomData::<H>::default(),
		},
		proof_recorder: Default::default(),
	};

	// iterate to collect proof
	while let Some(item) = iter.next() {
		item?;
	}

	Ok(iter.extract_proof())
}

/// Check key changes proog and return changes of the key at given blocks range.
/// `max` is the number of best known block.
/// Changes are returned in descending order (i.e. last block comes first).
pub fn key_changes_proof_check<S: RootsStorage<H>, H: Hasher>(
	config: &Configuration,
	roots_storage: &S,
	proof: Vec<Vec<u8>>,
	begin: u64,
	end: &AnchorBlockId<H::Out>,
	max: u64,
	key: &[u8]
) -> Result<Vec<(u64, u32)>, String> {
	// we can't query any roots before root
	let max = ::std::cmp::min(max, end.number);

	let mut proof_db = MemoryDB::<H>::default();
	for item in proof {
		proof_db.insert(&[], &item);
	}

	let proof_db = InMemoryStorage::with_db(proof_db);
	DrilldownIterator {
		essence: DrilldownIteratorEssence {
			key,
			roots_storage,
			storage: &proof_db,
			begin,
			end,
			surface: surface_iterator(config, max, begin, end.number)?,

			extrinsics: Default::default(),
			blocks: Default::default(),

			_hasher: ::std::marker::PhantomData::<H>::default(),
		},
	}.collect()
}

/// Surface iterator - only traverses top-level digests from given range and tries to find
/// all digest changes for the key.
pub struct SurfaceIterator<'a> {
	config: &'a Configuration,
	begin: u64,
	max: u64,
	current: Option<u64>,
	current_begin: u64,
	digest_step: u64,
	digest_level: u32,
}

impl<'a> Iterator for SurfaceIterator<'a> {
	type Item = Result<(u64, u32), String>;

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
				let (current, current_begin, digest_step, digest_level) = match
					lower_bound_max_digest(self.config, self.max, self.begin, next) {
					Err(err) => return Some(Err(err)),
					Ok(range) => range,
				};

				self.current = Some(current);
				self.current_begin = current_begin;
				self.digest_step = digest_step;
				self.digest_level = digest_level;
			}
		}

		Some(Ok((current, digest_level)))
	}
}

/// Drilldown iterator - receives 'digest points' from surface iterator and explores
/// every point until extrinsic is found.
pub struct DrilldownIteratorEssence<'a, RS: 'a + RootsStorage<H>, S: 'a + Storage<H>, H: Hasher> where H::Out: 'a {
	key: &'a [u8],
	roots_storage: &'a RS,
	storage: &'a S,
	begin: u64,
	end: &'a AnchorBlockId<H::Out>,
	surface: SurfaceIterator<'a>,

	extrinsics: VecDeque<(u64, u32)>,
	blocks: VecDeque<(u64, u32)>,

	_hasher: ::std::marker::PhantomData<H>,
}

impl<'a, RS: 'a + RootsStorage<H>, S: Storage<H>, H: Hasher> DrilldownIteratorEssence<'a, RS, S, H> {
	pub fn next<F>(&mut self, trie_reader: F) -> Option<Result<(u64, u32), String>>
		where
			F: FnMut(&S, H::Out, &[u8]) -> Result<Option<Vec<u8>>, String>,
	{
		match self.do_next(trie_reader) {
			Ok(Some(res)) => Some(Ok(res)),
			Ok(None) => None,
			Err(err) => Some(Err(err)),
		}
	}

	fn do_next<F>(&mut self, mut trie_reader: F) -> Result<Option<(u64, u32)>, String>
		where
			F: FnMut(&S, H::Out, &[u8]) -> Result<Option<Vec<u8>>, String>,
	{
		loop {
			if let Some((block, extrinsic)) = self.extrinsics.pop_front() {
				return Ok(Some((block, extrinsic)));
			}

			if let Some((block, level)) = self.blocks.pop_front() {
				// not having a changes trie root is an error because:
				// we never query roots for future blocks
				// AND trie roots for old blocks are known (both on full + light node)
				let trie_root = self.roots_storage.root(&self.end, block)?
					.ok_or_else(|| format!("Changes trie root for block {} is not found", block))?;

				// only return extrinsics for blocks before self.max
				// most of blocks will be filtered out before pushing to `self.blocks`
				// here we just throwing away changes at digest blocks we're processing
				debug_assert!(block >= self.begin, "We shall not touch digests earlier than a range' begin");
				if block <= self.end.number {
					let extrinsics_key = ExtrinsicIndex { block, key: self.key.to_vec() }.encode();
					let extrinsics = trie_reader(&self.storage, trie_root, &extrinsics_key);
					if let Some(extrinsics) = extrinsics? {
						let extrinsics: Option<ExtrinsicIndexValue> = Decode::decode(&mut &extrinsics[..]);
						if let Some(extrinsics) = extrinsics {
							self.extrinsics.extend(extrinsics.into_iter().rev().map(|e| (block, e)));
						}
					}
				}

				let blocks_key = DigestIndex { block, key: self.key.to_vec() }.encode();
				let blocks = trie_reader(&self.storage, trie_root, &blocks_key);
				if let Some(blocks) = blocks? {
					let blocks: Option<DigestIndexValue> = Decode::decode(&mut &blocks[..]);
					if let Some(blocks) = blocks {
						// filter level0 blocks here because we tend to use digest blocks,
						// AND digest block changes could also include changes for out-of-range blocks
						let begin = self.begin;
						let end = self.end.number;
						self.blocks.extend(blocks.into_iter()
							.rev()
							.filter(|b| level > 1 || (*b >= begin && *b <= end))
							.map(|b| (b, level - 1))
						);
					}
				}

				continue;
			}

			match self.surface.next() {
				Some(Ok(block)) => self.blocks.push_back(block),
				Some(Err(err)) => return Err(err),
				None => return Ok(None),
			}
		}
	}
}

/// Exploring drilldown operator.
pub struct DrilldownIterator<'a, RS: 'a + RootsStorage<H>, S: 'a + Storage<H>, H: Hasher> where H::Out: 'a {
	essence: DrilldownIteratorEssence<'a, RS, S, H>,
}

impl<'a, RS: 'a + RootsStorage<H>, S: Storage<H>, H: Hasher> Iterator
	for DrilldownIterator<'a, RS, S, H>
{
	type Item = Result<(u64, u32), String>;

	fn next(&mut self) -> Option<Self::Item> {
		self.essence.next(|storage, root, key|
			TrieBackendEssence::<_, H>::new(TrieBackendAdapter::new(storage), root).storage(key))
	}
}

/// Proving drilldown iterator.
struct ProvingDrilldownIterator<'a, RS: 'a + RootsStorage<H>, S: 'a + Storage<H>, H: Hasher> where H::Out: 'a {
	essence: DrilldownIteratorEssence<'a, RS, S, H>,
	proof_recorder: RefCell<Recorder<H::Out>>,
}

impl<'a, RS: 'a + RootsStorage<H>, S: Storage<H>, H: Hasher> ProvingDrilldownIterator<'a, RS, S, H> {
	/// Consume the iterator, extracting the gathered proof in lexicographical order
	/// by value.
	pub fn extract_proof(self) -> Vec<Vec<u8>> {
		self.proof_recorder.into_inner().drain()
			.into_iter()
			.map(|n| n.data.to_vec())
			.collect()
	}
}

impl<'a, RS: 'a + RootsStorage<H>, S: Storage<H>, H: Hasher> Iterator for ProvingDrilldownIterator<'a, RS, S, H> {
	type Item = Result<(u64, u32), String>;

	fn next(&mut self) -> Option<Self::Item> {
		let proof_recorder = &mut *self.proof_recorder.try_borrow_mut()
			.expect("only fails when already borrowed; storage() is non-reentrant; qed");
		self.essence.next(|storage, root, key|
			ProvingBackendEssence::<_, H> {
				backend: &TrieBackendEssence::new(TrieBackendAdapter::new(storage), root),
				proof_recorder,
			}.storage(key))
	}
}

/// Returns surface iterator for given range of blocks.
fn surface_iterator<'a>(config: &'a Configuration, max: u64, begin: u64, end: u64) -> Result<SurfaceIterator<'a>, String> {
	let (current, current_begin, digest_step, digest_level) = lower_bound_max_digest(config, max, begin, end)?;
	Ok(SurfaceIterator {
		config,
		begin,
		max,
		current: Some(current),
		current_begin,
		digest_step,
		digest_level,
	})
}

/// Returns parameters of highest level digest block that includes the end of given range
/// and tends to include the whole range.
fn lower_bound_max_digest(
	config: &Configuration,
	max: u64,
	begin: u64,
	end: u64,
) -> Result<(u64, u64, u64, u32), String> {
	if end > max || begin > end {
		return Err("invalid changes range".into());
	}

	let mut digest_level = 0u32;
	let mut digest_step = 1u64;
	let mut digest_interval = 0u64;
	let mut current = end;
	let mut current_begin = begin;
	if begin != end {
		while digest_level != config.digest_levels {
			let new_digest_level = digest_level + 1;
			let new_digest_step = digest_step * config.digest_interval;
			let new_digest_interval = config.digest_interval * {
				if digest_interval == 0 { 1 } else { digest_interval }
			};
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

	Ok((
		current,
		current_begin,
		digest_step,
		digest_level,
	))
}

#[cfg(test)]
mod tests {
	use std::iter::FromIterator;
	use primitives::Blake2Hasher;
	use crate::changes_trie::input::InputPair;
	use crate::changes_trie::storage::InMemoryStorage;
	use super::*;

	fn prepare_for_drilldown() -> (Configuration, InMemoryStorage<Blake2Hasher>) {
		let config = Configuration { digest_interval: 4, digest_levels: 2 };
		let backend = InMemoryStorage::with_inputs(vec![
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
		]);

		(config, backend)
	}

	#[test]
	fn drilldown_iterator_works() {
		let (config, storage) = prepare_for_drilldown();
		let drilldown_result = key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 0, &AnchorBlockId { hash: Default::default(), number: 16 }, 16, &[42])
			.and_then(Result::from_iter);
		assert_eq!(drilldown_result, Ok(vec![(8, 2), (8, 1), (6, 3), (3, 0)]));

		let drilldown_result = key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 0, &AnchorBlockId { hash: Default::default(), number: 2 }, 4, &[42])
			.and_then(Result::from_iter);
		assert_eq!(drilldown_result, Ok(vec![]));

		let drilldown_result = key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 0, &AnchorBlockId { hash: Default::default(), number: 3 }, 4, &[42])
			.and_then(Result::from_iter);
		assert_eq!(drilldown_result, Ok(vec![(3, 0)]));

		let drilldown_result = key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 7, &AnchorBlockId { hash: Default::default(), number: 8 }, 8, &[42])
			.and_then(Result::from_iter);
		assert_eq!(drilldown_result, Ok(vec![(8, 2), (8, 1)]));

		let drilldown_result = key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 5, &AnchorBlockId { hash: Default::default(), number: 7 }, 8, &[42])
			.and_then(Result::from_iter);
		assert_eq!(drilldown_result, Ok(vec![(6, 3)]));
	}

	#[test]
	fn drilldown_iterator_fails_when_storage_fails() {
		let (config, storage) = prepare_for_drilldown();
		storage.clear_storage();

		assert!(key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 0, &AnchorBlockId { hash: Default::default(), number: 100 }, 1000, &[42])
			.and_then(|i| i.collect::<Result<Vec<_>, _>>()).is_err());
	}

	#[test]
	fn drilldown_iterator_fails_when_range_is_invalid() {
		let (config, storage) = prepare_for_drilldown();
		assert!(key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 0, &AnchorBlockId { hash: Default::default(), number: 100 }, 50, &[42]).is_err());
		assert!(key_changes::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&config, &storage, 20, &AnchorBlockId { hash: Default::default(), number: 10 }, 100, &[42]).is_err());
	}


	#[test]
	fn proving_drilldown_iterator_works() {
		// happens on remote full node:

		// create drilldown iterator that records all trie nodes during drilldown
		let (remote_config, remote_storage) = prepare_for_drilldown();
		let remote_proof = key_changes_proof::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&remote_config, &remote_storage,
			0, &AnchorBlockId { hash: Default::default(), number: 16 }, 16, &[42]).unwrap();

		// happens on local light node:

		// create drilldown iterator that works the same, but only depends on trie
		let (local_config, local_storage) = prepare_for_drilldown();
		local_storage.clear_storage();
		let local_result = key_changes_proof_check::<InMemoryStorage<Blake2Hasher>, Blake2Hasher>(
			&local_config, &local_storage, remote_proof,
			0, &AnchorBlockId { hash: Default::default(), number: 16 }, 16, &[42]);

		// check that drilldown result is the same as if it was happening at the full node
		assert_eq!(local_result, Ok(vec![(8, 2), (8, 1), (6, 3), (3, 0)]));
	}
}
