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

//! Changes trie related structures and functions.
//!
//! Changes trie is a trie built of { storage key => extrinsiscs } pairs
//! at the end of each block. For every changed storage key it contains
//! a pair, mapping key to the set of extrinsics where it has been changed.
//!
//! Optionally, every N blocks, additional level1-digest nodes are appended
//! to the changes trie, containing pairs { storage key => blocks }. For every
//! storage key that has been changed in PREVIOUS N-1 blocks (except for genesis
//! block) it contains a pair, mapping this key to the set of blocks where it
//! has been changed.
//!
//! Optionally, every N^digest_level (where digest_level > 1) blocks, additional
//! digest_level digest is created. It is built out of pairs { storage key => digest
//! block }, containing entries for every storage key that has been changed in
//! the last N*digest_level-1 blocks (except for genesis block), mapping these keys
//! to the set of lower-level digest blocks.
//!
//! Changes trie only contains the top level storage changes. Sub-level changes
//! are propagated through its storage root on the top level storage.

mod build;
mod build_iterator;
mod changes_iterator;
mod input;
mod prune;
mod storage;

pub use self::storage::InMemoryStorage;
pub use self::changes_iterator::{key_changes, key_changes_proof, key_changes_proof_check};
pub use self::prune::{prune, oldest_non_pruned_trie};

use hash_db::Hasher;
use crate::backend::Backend;
use primitives;
use crate::changes_trie::build::prepare_input;
use crate::overlayed_changes::OverlayedChanges;
use crate::trie_backend_essence::TrieBackendStorage;
use trie::{DBValue, trie_root};

/// Changes that are made outside of extrinsics are marked with this index;
pub const NO_EXTRINSIC_INDEX: u32 = 0xffffffff;

/// Block identifier that could be used to determine fork of this block.
#[derive(Debug)]
pub struct AnchorBlockId<Hash: ::std::fmt::Debug> {
	/// Hash of this block.
	pub hash: Hash,
	/// Number of this block.
	pub number: u64,
}

/// Changes trie storage. Provides access to trie roots and trie nodes.
pub trait RootsStorage<H: Hasher>: Send + Sync {
	/// Get changes trie root for the block with given number which is an ancestor (or the block
	/// itself) of the anchor_block (i.e. anchor_block.number >= block).
	fn root(&self, anchor: &AnchorBlockId<H::Out>, block: u64) -> Result<Option<H::Out>, String>;
}

/// Changes trie storage. Provides access to trie roots and trie nodes.
pub trait Storage<H: Hasher>: RootsStorage<H> {
	/// Get a trie node.
	fn get(&self, key: &H::Out, prefix: &[u8]) -> Result<Option<DBValue>, String>;
}

/// Changes trie configuration.
pub type Configuration = primitives::ChangesTrieConfiguration;

/// Compute the changes trie root and transaction for given block.
/// Returns None if there's no data to perform computation.
pub fn compute_changes_trie_root<'a, B: Backend<H>, S: Storage<H>, H: Hasher>(
	backend: &B,
	storage: Option<&'a S>,
	changes: &OverlayedChanges,
	parent: &'a AnchorBlockId<H::Out>,
) -> Option<(H::Out, Vec<(Vec<u8>, Vec<u8>)>)>
	where
		&'a S: TrieBackendStorage<H>,
		H::Out: Ord,
{
	let input_pairs = prepare_input::<B, S, H>(backend, storage, changes, parent)
		.expect("storage is not allowed to fail within runtime")?;
	let transaction = input_pairs.into_iter()
		.map(Into::into)
		.collect::<Vec<_>>();
	let root = trie_root::<H, _, _, _>(transaction.iter().map(|(k, v)| (&*k, &*v)));

	Some((root, transaction))
}
