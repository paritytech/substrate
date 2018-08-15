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

//! TODO

//#![allow(unused_must_use)]
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;
use codec::{Decode, Encode};
use ethereum_types::H256 as TrieH256;
use hashdb::{DBValue, HashDB};
use memorydb::MemoryDB;
use patricia_trie::Recorder;
use overlayed_changes::OverlayedChanges;
use proving_backend::ProvingBackendEssence;
use trie_backend_essence::{TrieBackendEssence, Storage as TrieStorage};
use self::nodes::{KeyIndex, ExtrinsicIndex, ExtrinsicIndexValue, DigestIndex,
	DigestIndexValue, InputPair, InputKey};

/// Changes trie storage trait.
pub trait Storage: Send + Sync {
	/// Get changes trie root for given block.
	fn root(&self, block: u64) -> Result<Option<TrieH256>, String>;

	/// Get a trie node.
	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String>;
}

struct TrieStorageAdapter(Arc<Storage>);

impl TrieStorage for TrieStorageAdapter {
	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		self.0.get(key)
	}
}

struct ProofCheckStorage {
	roots_storage: Arc<Storage>,
	proof_db: MemoryDB,
}

impl ProofCheckStorage {
	fn new(roots_storage: Arc<Storage>, proof: Vec<Vec<u8>>) -> Self {
		let mut proof_db = MemoryDB::new();
		for item in proof {
			proof_db.insert(&item);
		}

		ProofCheckStorage {
			roots_storage,
			proof_db,
		}
	}
}

impl Storage for ProofCheckStorage {
	fn root(&self, block: u64) -> Result<Option<TrieH256>, String> {
		let root = self.roots_storage.root(block)?;

		// every root that we're asking for MUST be a part of proof db
		if let Some(root) = root {
			if !self.proof_db.contains(&root) {
				return Err("TODO".into());
			}
		}

		Ok(root)
	}

	fn get(&self, key: &TrieH256) -> Result<Option<DBValue>, String> {
		Ok(self.proof_db.get(key))
	}
}

/// Configuration of changes trie.
#[derive(Clone, Debug)]
pub struct ChangesTrieConfig {
	/// Digest is created every digest_interval blocks. Digest is not created if
	/// digest_interval is zero or one.
	pub digest_interval: u64,
	/// Number of digest levels in hierarchy.  means that digests are not created at all.
	/// 1 means that every (1 << digest_interval) blocks digest of level1 is created,
	/// which points to digests of level0 where keys have been changed. And so on...
	pub digest_levels: u8,
}

/// Digest build params.
#[derive(Debug, PartialEq)]
pub struct DigestBuildParams {
	/// Current block.
	current: u64,
	/// Begin block.
	begin: u64,
	/// Step.
	step: u64,
}

impl Iterator for DigestBuildParams {
	type Item = u64;

	fn next(&mut self) -> Option<Self::Item> {
		let next_current = self.current.saturating_sub(self.step);
		if next_current <= self.begin {
			None
		} else {
			self.current = next_current;
			Some(next_current)
		}
	}
}

/// Surface iterator.
pub struct SurfaceIterator<'a> {
	config: &'a ChangesTrieConfig,
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
				let (current, current_begin, digest_step, digest_level) = self.config.lower_bound_max_digest(self.max, self.begin, next);

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
	key: Vec<u8>,
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
					let extrinsics_key = ExtrinsicIndex { block, key: self.key.clone() }.encode();
					let extrinsics = trie_reader(self.storage.clone(), trie_root, &extrinsics_key);
					if let Some(extrinsics) = extrinsics.expect("TODO") {
						let extrinsics: Option<ExtrinsicIndexValue> = Decode::decode(&mut &extrinsics[..]);
						if let Some(extrinsics) = extrinsics {
							self.extrinsics.extend(extrinsics.into_iter().rev().map(|e| (block, e)));
						}
					}

					let blocks_key = DigestIndex { block, key: self.key.clone() }.encode();
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
pub struct DrilldownIterator<'a> {
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
pub struct ProvingDrilldownIterator<'a> {
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

impl ChangesTrieConfig {
	/// If given block requires to have digest, return digest build parameters.
	pub fn suggest_digest(&self, block: u64) -> Option<DigestBuildParams> {
		// digest is never built in these cases
		if block == 0 || self.digest_interval <= 1 || self.digest_levels == 0 {
			return None;
		}

		// build digest every digest_multiplier blocks
		let mut digest_interval = self.digest_interval;
		if block % digest_interval != 0 {
			return None;
		}

		// the block is at least l1 digest => try to find highest level
		let mut current_level = 1u8;
		let mut digest_step = 1u64;
		while current_level < self.digest_levels {
			let new_digest_interval = match digest_interval.checked_mul(self.digest_interval) {
				Some(new_digest_interval) => new_digest_interval,
				None => break,
			};
			if block % new_digest_interval != 0 {
				break;
			}

			digest_step = digest_interval;
			digest_interval = new_digest_interval;
			current_level = current_level + 1;
		}

		Some(DigestBuildParams {
			current: block,
			begin: block - digest_interval,
			step: digest_step,
		})
	}

	/// Return topmost digests iterator which returns topmost blocks/digest blocks for given range.
	pub fn surface_iterator<'a>(&'a self, max: u64, begin: u64, end: u64) -> SurfaceIterator<'a> {
		let (current, current_begin, digest_step, digest_level) = self.lower_bound_max_digest(max, begin, end);
		SurfaceIterator {
			config: self,
			begin,
			max,
			current: Some(current),
			current_begin,
			digest_step,
			digest_level,
		}
	}

	/// Returns digest block that we need to read first to query changes for given range.
	pub fn lower_bound_max_digest(&self, max: u64, begin: u64, end: u64) -> (u64, u64, u64, u8) {
		assert!(end <= max);
		assert!(begin <= end);

		// TODO: bgin || end == zero
		let mut digest_level = 0u8;
		let mut digest_step = 1u64;
		let mut digest_interval = 0u64;
		let mut current = end;
		let mut current_begin = begin;
		if begin != end {
			while digest_level != self.digest_levels {
				let new_digest_level = digest_level + 1;
				let new_digest_step = digest_step * self.digest_interval;
				let new_digest_interval = { if digest_interval == 0 { 1 } else { digest_interval } } * self.digest_interval;
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
}

/// Compute changes trie root and transaction for given block.
pub fn compute_changes_trie_root(
	storage: Arc<Storage>,
	changes: &OverlayedChanges,
) -> Option<([u8; 32], Vec<(Vec<u8>, Vec<u8>)>)> {
	let changes_trie_nodes = build_changes_trie_nodes(
		storage,
		changes)?;
	let transaction = changes_trie_nodes.into_iter()
		.map(Into::into)
		.collect::<Vec<_>>();
	let root = ::triehash::trie_root(transaction.iter().map(|(k, v)| (&*k, &*v))).0;

	Some((root, transaction))
}

/// Build changes trie nodes for the given block.
pub fn build_changes_trie_nodes(
	storage: Arc<Storage>,
	changes: &OverlayedChanges,
) -> Option<Vec<InputPair>> {
	let extrinsic_changes = changes.extrinsic_changes.as_ref()?;
	let block = extrinsic_changes.block;

	let mut nodes = Vec::new();

	// TODO: do not include temporary (whice were created and deleted in the same block) values

	// every changes trie contains mapping of { changed key index => key }, ending with sentinel element
	let mut key_count: u32 = 0;
	nodes.extend(changes.prospective.keys()
		.chain(changes.committed.keys())
		.collect::<BTreeSet<_>>()
		.into_iter()
		// assign index to each key
		.map(|key| InputPair::KeyIndex(KeyIndex {
			block,
			index: {
				let key_index = key_count;
				key_count += 1;
				key_index
			},
		}, key.clone())));
	nodes.push(InputPair::KeyIndex(KeyIndex {
		block,
		index: key_count,
	}, vec![]));

	// every changes trie contains mapping of { changes key => Set<extrinsic index it has been changed in> }
	let mut extrinsic_map = BTreeMap::<Vec<u8>, BTreeSet<u32>>::new();
	for (key, extrinsics) in extrinsic_changes.prospective.iter().chain(extrinsic_changes.committed.iter()) {
		extrinsic_map.entry(key.clone()).or_default()
			.extend(extrinsics);
	}
	nodes.extend(extrinsic_map.into_iter()
		.map(|(key, extrinsics)| InputPair::ExtrinsicIndex(ExtrinsicIndex {
			block,
			key: key.clone(),
		}, extrinsics.iter().cloned().collect())));

	// some changes tries also have digest subtree
	if let Some(digest_build_params) = extrinsic_changes.changes_trie_config.suggest_digest(extrinsic_changes.block) {
		let mut digest_nodes = BTreeMap::<Vec<u8>, BTreeSet<u64>>::new();
		for digest_build_block in digest_build_params {
			let trie_root = storage.root(digest_build_block).expect("TODO").expect("TODO");
			let trie_storage = TrieBackendEssence::with_storage(Arc::new(TrieStorageAdapter(storage.clone())), trie_root);

			// TODO: seek currently works wrong (wait until parity-common is merged) && uncomment

			trie_storage.for_keys_with_prefix(&[], |key| match Decode::decode(&mut &key[..]) {
				Some(InputKey::ExtrinsicIndex(trie_key)) => {
					digest_nodes.entry(trie_key.key).or_default()
						.insert(digest_build_block);
				},
				Some(InputKey::DigestIndex(trie_key)) => {
					digest_nodes.entry(trie_key.key).or_default()
						.insert(digest_build_block);
				},
				_ => (),
			});

			/*let extrinsic_prefix = ExtrinsicIndex::key_neutral_prefix(digest_build_block);
			trie_storage.for_keys_with_prefix(&extrinsic_prefix, |key|
				if let Some(InputKey::ExtrinsicIndex(trie_key)) = Decode::decode(&mut &key[..]) {
					digest_nodes.entry(trie_key.key).or_default()
						.insert(digest_build_block);
				});

			let digest_prefix = DigestIndex::key_neutral_prefix(digest_build_block);
			trie_storage.for_keys_with_prefix(&digest_prefix, |key|
				if let Some(InputKey::DigestIndex(trie_key)) = Decode::decode(&mut &key[..]) {
					digest_nodes.entry(trie_key.key).or_default()
						.insert(digest_build_block);
				});*/
		}

		nodes.extend(digest_nodes.into_iter().map(|(key, set)| InputPair::DigestIndex(DigestIndex {
			block,
			key
		}, set.into_iter().collect())));
	}

	Some(nodes)
}

/// Query changes log for given key for given range of blocks.
/*pub fn query_changes_trie<B: Backend>(
	backend: &B,
	config: &ChangesTrieConfig,
	key: &[u8],
	begin: Option<u64>,
	end: Option<u64>,
) -> Result<Option<Vec<KeyChange>>, Box<Error>> {
	// find the latest digest block including the end block
	// traverse all digest blocks down to the begin block
}*/

pub mod nodes {
	use codec::{Decode, Encode, Input, Output};

	/// Key of { changed key index => changed key } mapping.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub struct KeyIndex {
		/// Block at which this key has been inserted in the trie.
		pub block: u64,
		/// Index of changed storage key this node is responsible for.
		pub index: u32,
	}

	/// Value of { changed key index => changed key } mapping.
	pub type KeyIndexValue = Vec<u8>;

	/// Key of { changed key => set of extrinsic indices } mapping.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub struct ExtrinsicIndex {
		/// Block at which this key has been inserted in the trie.
		pub block: u64,
		/// Storage key this node is responsible for.
		pub key: Vec<u8>,
	}

	/// Value of { changed key => set of extrinsic indices } mapping.
	pub type ExtrinsicIndexValue = Vec<u32>;

	/// Key of { changed key => block/digest block numbers } mapping.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub struct DigestIndex {
		/// Block at which this key has been inserted in the trie.
		pub block: u64,
		/// Storage key this node is responsible for.
		pub key: Vec<u8>,
	}

	/// Value of { changed key => block/digest block numbers } mapping.
	pub type DigestIndexValue = Vec<u64>;

	/// Single input pair of changes trie.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub enum InputPair {
		/// Element of { changed key index => key } element mapping.
		KeyIndex(KeyIndex, KeyIndexValue),
		/// Element of { key => set of extrinsics where key has been changed } element mapping.
		ExtrinsicIndex(ExtrinsicIndex, ExtrinsicIndexValue),
		/// Element of { key => set of blocks/digest blocks where key has been changed } element mapping.
		DigestIndex(DigestIndex, DigestIndexValue),
	}

	/// Single input key of changes trie.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub enum InputKey {
		/// Key of { changed key index => key } element mapping.
		KeyIndex(KeyIndex),
		/// Key of { key => set of extrinsics where key has been changed } element mapping.
		ExtrinsicIndex(ExtrinsicIndex),
		/// Key of { key => set of blocks/digest blocks where key has been changed } element mapping.
		DigestIndex(DigestIndex),
	}

	/// Single input value of changes trie.
	#[derive(Clone, Debug, PartialEq, Eq)]
	pub enum InputValue {
		/// Key of { changed key index => key } element mapping.
		KeyIndex(KeyIndexValue),
		/// Key of { key => set of extrinsics where key has been changed } element mapping.
		ExtrinsicIndex(ExtrinsicIndexValue),
		/// Key of { key => set of blocks/digest blocks where key has been changed } element mapping.
		DigestIndex(DigestIndexValue),
	}

	impl InputKey {
		/// Get all possible serialization prefixes of all keys for given block.
		pub fn enumerate_prefixes(block: u64) -> Vec<Vec<u8>> {
			let sblock = block.encode();
			vec![
				::std::iter::once(1u8).chain(sblock.iter().cloned()).collect(),
				::std::iter::once(2u8).chain(sblock.iter().cloned()).collect(),
				::std::iter::once(3u8).chain(sblock.into_iter()).collect(),
			]
		}
	}

	impl Into<(Vec<u8>, Vec<u8>)> for InputPair {
		fn into(self) -> (Vec<u8>, Vec<u8>) {
			match self {
				InputPair::KeyIndex(key, value) => (key.encode(), value.encode()),
				InputPair::ExtrinsicIndex(key, value) => (key.encode(), value.encode()),
				InputPair::DigestIndex(key, value) => (key.encode(), value.encode()),
			}
		}
	}

	impl Into<InputKey> for InputPair {
		fn into(self) -> InputKey {
			match self {
				InputPair::KeyIndex(key, _) => InputKey::KeyIndex(key),
				InputPair::ExtrinsicIndex(key, _) => InputKey::ExtrinsicIndex(key),
				InputPair::DigestIndex(key, _) => InputKey::DigestIndex(key),
			}
		}
	}

	impl Encode for KeyIndex {
		fn encode_to<W: Output>(&self, dest: &mut W) {
			dest.push_byte(1);
			self.block.encode_to(dest);
			self.index.encode_to(dest);
		}
	}

	impl ExtrinsicIndex {
		pub fn key_neutral_prefix(block: u64) -> Vec<u8> {
			let mut prefix = vec![2];
			prefix.extend(block.encode());
			prefix
		}
	}

	impl Encode for ExtrinsicIndex {
		fn encode_to<W: Output>(&self, dest: &mut W) {
			dest.push_byte(2);
			self.block.encode_to(dest);
			self.key.encode_to(dest);
		}
	}

	impl DigestIndex {
		pub fn key_neutral_prefix(block: u64) -> Vec<u8> {
			let mut prefix = vec![3];
			prefix.extend(block.encode());
			prefix
		}
	}


	impl Encode for DigestIndex {
		fn encode_to<W: Output>(&self, dest: &mut W) {
			dest.push_byte(3);
			self.block.encode_to(dest);
			self.key.encode_to(dest);
		}
	}

	impl Decode for InputKey {
		fn decode<I: Input>(input: &mut I) -> Option<Self> {
			match input.read_byte()? {
				1 => Some(InputKey::KeyIndex(KeyIndex {
					block: Decode::decode(input)?,
					index: Decode::decode(input)?,
				})),
				2 => Some(InputKey::ExtrinsicIndex(ExtrinsicIndex {
					block: Decode::decode(input)?,
					key: Decode::decode(input)?,
				})),
				3 => Some(InputKey::DigestIndex(DigestIndex {
					block: Decode::decode(input)?,
					key: Decode::decode(input)?,
				})),
				_ => None,
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use backend::InMemoryChangesTrieStorage;
	use overlayed_changes::ExtrinsicChanges;
	use super::*;

	fn suggest_digest(digest_interval: u64, digest_levels: u8, block: u64) -> Option<DigestBuildParams> {
		ChangesTrieConfig { digest_interval, digest_levels }.suggest_digest(block)
	}

	fn digest_build_params(current: u64, begin: u64, step: u64) -> Option<DigestBuildParams> {
		Some(DigestBuildParams { current, begin, step })
	}

	#[test]
	fn suggest_digest_returns_none() {
		assert_eq!(suggest_digest(4, 16, 0), None, "block is 0");
		assert_eq!(suggest_digest(0, 16, 64), None, "digest_interval is 0");
		assert_eq!(suggest_digest(1, 16, 64), None, "digest_interval is 1");
		assert_eq!(suggest_digest(4, 0, 64), None, "digest_levels is 0");
		assert_eq!(suggest_digest(4, 16, 1), None, "digest is not required for this block");
		assert_eq!(suggest_digest(4, 16, 2), None, "digest is not required for this block");
		assert_eq!(suggest_digest(4, 16, 15), None, "digest is not required for this block");
		assert_eq!(suggest_digest(4, 16, 17), None, "digest is not required for this block");
		assert_eq!(suggest_digest(::std::u64::MAX / 2 + 1, 16, ::std::u64::MAX), None, "digest_interval * 2 is greater than u64::MAX");
	}

	#[test]
	fn suggest_digest_returns_some() {
		assert_eq!(suggest_digest(16, 1, 16), digest_build_params(16, 0, 1), "!(block % interval) && first digest level == block");
		assert_eq!(suggest_digest(16, 1, 256), digest_build_params(256, 240, 1), "!(block % interval^2), but there's only 1 digest level");
		assert_eq!(suggest_digest(16, 2, 32), digest_build_params(32, 16, 1), "second level digest is not required for this block");
		assert_eq!(suggest_digest(16, 2, 256), digest_build_params(256, 0, 16), "second level digest");
		assert_eq!(suggest_digest(16, 2, 4096), digest_build_params(4096, 3840, 16), "!(block % interval^3), but there's only 2 digest levels");
		assert_eq!(suggest_digest(16, 3, 4080), digest_build_params(4080, 4064, 1), "second && third level digest is not required for this block");
		assert_eq!(suggest_digest(16, 3, 4096), digest_build_params(4096, 0, 256), "third level digest: beginning");
		assert_eq!(suggest_digest(16, 3, 8192), digest_build_params(8192, 4096, 256), "third level digest: next");
	}

	fn lower_bound_max_digest(digest_interval: u64, digest_levels: u8, begin: u64, end: u64, max: u64) -> (u64, u64, u64, u8) {
		ChangesTrieConfig { digest_interval, digest_levels }.lower_bound_max_digest(max, begin, end)
	}

	#[test]
	fn lower_bound_max_digest_works() {
		// single-block ranges that are not requiring any digests
		assert_eq!(lower_bound_max_digest(16, 4, 5, 5, 1000), (5, 5, 1, 0),
			"range 5..5 does not require any digest to lookup in");

		// ranges that are falling into first l1-digest
		assert_eq!(lower_bound_max_digest(16, 4, 0, 8, 1000), (16, 0, 16, 1),
			"8 is a part of l1 digest 0..16 AND range 0..8 is covered by this l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 8, 16, 1000), (16, 0, 16, 1),
			"16 is a part of l1 digest 0..16 AND range 8..16 is covered by this l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 0, 16, 1000), (16, 0, 16, 1),
			"16 is a part of l1 digest 0..16 AND range 0..16 is covered by this l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 5, 9, 1000), (16, 0, 16, 1),
			"9 is a part of l1 digest 0..16 AND range 5..9 is covered by this l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 5, 7, 8), (7, 5, 1, 0),
			"7 is a part of l1 digest 0..16 BUT only 8 blocks are mined");
		assert_eq!(lower_bound_max_digest(16, 0, 5, 7, 1000), (7, 5, 1, 0),
			"7 is a part of l1 digest 0..16 BUT no digest is created");

		// ranges that are falling into some l1-digest
		assert_eq!(lower_bound_max_digest(16, 4, 250, 252, 1000), (256, 240, 16, 1),
			"252 is a part of l1 digest 240..256 AND range 250..252 is covered by this l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 250, 252, 255), (252, 250, 1, 0),
			"252 is a part of l1 digest 240..256 BUT only 255 blocks are mined");
		assert_eq!(lower_bound_max_digest(16, 0, 250, 252, 1000), (252, 250, 1, 0),
			"252 is a part of l1 digest 240..256 BUT no digest is created");

		// ranges that are crossing l1-digest borders => require l2 digest
		assert_eq!(lower_bound_max_digest(16, 4, 15, 20, 1000), (256, 0, 256, 2),
			"20 is a part of l2 digest 0..256 AND range 15..20 is NOT covered by any single l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 5, 17, 1000), (256, 0, 256, 2),
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest");
		assert_eq!(lower_bound_max_digest(16, 4, 5, 17, 20), (17, 16, 1, 0),
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT only 20 blocks are mined");
		assert_eq!(lower_bound_max_digest(16, 0, 5, 17, 1000), (17, 5, 1, 0),
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT no digest is created");
		assert_eq!(lower_bound_max_digest(16, 1, 5, 17, 1000), (32, 16, 16, 1),
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT only l1 digests are created");
	}

	fn surface_iterator(digest_interval: u64, digest_levels: u8, begin: u64, end: u64, max: u64) -> Vec<(u64, u8)> {
		ChangesTrieConfig { digest_interval, digest_levels }.surface_iterator(max, begin, end).collect()
	}

	#[test]
	fn surface_iterator_works() {
		// single-block ranges that are not requiring any digests
		assert_eq!(surface_iterator(16, 4, 5, 5, 1000), vec![(5, 0)],
			"range 5..5 does not require any digest to lookup in");

		// ranges that are falling into first l1-digest
		assert_eq!(surface_iterator(16, 4, 0, 8, 1000), vec![(16, 1)],
			"8 is a part of l1 digest 0..16 AND range 0..8 is covered by this l1 digest");
		assert_eq!(surface_iterator(16, 4, 8, 16, 1000), vec![(16, 1)],
			"16 is a part of l1 digest 0..16 AND range 8..16 is covered by this l1 digest");
		assert_eq!(surface_iterator(16, 4, 0, 16, 1000), vec![(16, 1)],
			"16 is a part of l1 digest 0..16 AND range 0..16 is covered by this l1 digest");
		assert_eq!(surface_iterator(16, 4, 5, 9, 1000), vec![(16, 1)],
			"9 is a part of l1 digest 0..16 AND range 5..9 is covered by this l1 digest");
		assert_eq!(surface_iterator(16, 4, 5, 7, 8), vec![(7, 0), (6, 0), (5, 0)],
			"7 is a part of l1 digest 0..16 BUT only 8 blocks are mined");
		assert_eq!(surface_iterator(16, 0, 5, 7, 1000), vec![(7, 0), (6, 0), (5, 0)],
			"7 is a part of l1 digest 0..16 BUT no digest is created");

		// ranges that are falling into some l1-digest
		assert_eq!(surface_iterator(16, 4, 250, 252, 1000), vec![(256, 1)],
			"252 is a part of l1 digest 240..256 AND range 250..252 is covered by this l1 digest");
		assert_eq!(surface_iterator(16, 4, 250, 252, 255), vec![(252, 0), (251, 0), (250, 0)],
			"252 is a part of l1 digest 240..256 BUT only 255 blocks are mined");
		assert_eq!(surface_iterator(16, 0, 250, 252, 1000), vec![(252, 0), (251, 0), (250, 0)],
			"252 is a part of l1 digest 240..256 BUT no digest is created");

		// ranges that are crossing l1-digest borders => require l2 digest
		assert_eq!(surface_iterator(16, 4, 15, 20, 1000), vec![(256, 2)],
			"20 is a part of l2 digest 0..256 AND range 15..20 is NOT covered by any single l1 digest");
		assert_eq!(surface_iterator(16, 4, 5, 17, 1000), vec![(256, 2)],
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest");
		assert_eq!(surface_iterator(16, 4, 5, 17, 20), vec![(17, 0), (16, 1)],
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT only 20 blocks are mined");
		assert_eq!(surface_iterator(16, 0, 5, 17, 1000), vec![(17, 0), (16, 0), (15, 0), (14, 0), (13, 0),
			(12, 0), (11, 0), (10, 0), (9, 0), (8, 0), (7, 0), (6, 0), (5, 0)],
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT no digest is created");
		assert_eq!(surface_iterator(16, 1, 5, 17, 1000), vec![(32, 1), (16, 1)],
			"17 is a part of l2 digest 0..256 AND range 5..17 is NOT covered by any single l1 digest BUT only l1 digests are created");
	}

	fn prepare_for_build(block: u64) -> (Arc<InMemoryChangesTrieStorage>, OverlayedChanges) {
		let backend = Arc::new(vec![
			(1, vec![
				InputPair::KeyIndex(KeyIndex { block: 1, index: 0 }, vec![100]),
				InputPair::KeyIndex(KeyIndex { block: 1, index: 1 }, vec![101]),
				InputPair::KeyIndex(KeyIndex { block: 1, index: 2 }, vec![105]),
				InputPair::KeyIndex(KeyIndex { block: 1, index: 3 }, vec![]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![100] }, vec![1, 3]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![101] }, vec![0, 2]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 1, key: vec![105] }, vec![0, 2, 4]),
			]),
			(2, vec![
				InputPair::KeyIndex(KeyIndex { block: 2, index: 0 }, vec![102]),
				InputPair::KeyIndex(KeyIndex { block: 2, index: 1 }, vec![]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 2, key: vec![102] }, vec![0]),
			]),
			(3, vec![
				InputPair::KeyIndex(KeyIndex { block: 3, index: 0 }, vec![100]),
				InputPair::KeyIndex(KeyIndex { block: 3, index: 1 }, vec![105]),
				InputPair::KeyIndex(KeyIndex { block: 3, index: 2 }, vec![]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 3, key: vec![100] }, vec![0]),
				InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 3, key: vec![105] }, vec![1]),
			]),
		].into());
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
				changes_trie_config: ChangesTrieConfig { digest_interval: 4, digest_levels: 1 },
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
		let changes_trie_nodes = build_changes_trie_nodes(storage, &changes);
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::KeyIndex(KeyIndex { block: 5, index: 0 }, vec![100]),
			InputPair::KeyIndex(KeyIndex { block: 5, index: 1 }, vec![101]),
			InputPair::KeyIndex(KeyIndex { block: 5, index: 2 }, vec![103]),
			InputPair::KeyIndex(KeyIndex { block: 5, index: 3 }, vec![]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![100] }, vec![0, 2, 3]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![101] }, vec![1]),
			InputPair::ExtrinsicIndex(ExtrinsicIndex { block: 5, key: vec![103] }, vec![0, 1]),
		]));
	}

	#[test]
	fn build_changes_trie_nodes_on_digest_block_l1() {
		let (storage, changes) = prepare_for_build(4);
		let changes_trie_nodes = build_changes_trie_nodes(storage, &changes);
		assert_eq!(changes_trie_nodes, Some(vec![
			InputPair::KeyIndex(KeyIndex { block: 4, index: 0 }, vec![100]),
			InputPair::KeyIndex(KeyIndex { block: 4, index: 1 }, vec![101]),
			InputPair::KeyIndex(KeyIndex { block: 4, index: 2 }, vec![103]),
			InputPair::KeyIndex(KeyIndex { block: 4, index: 3 }, vec![]),
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
		// TODO
	}

	#[test]
	fn build_changes_trie_nodes_ignores_temporary_storage_values() {
		// TODO
	}
}
