// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate Client data backend

use crate::{
	blockchain::{well_known_cache_keys, Backend as BlockchainBackend},
	UsageInfo,
};
use parking_lot::RwLock;
use sp_blockchain;
use sp_consensus::BlockOrigin;
use sp_core::offchain::OffchainStorage;
use sp_runtime::{
	traits::{Block as BlockT, HashFor, NumberFor},
	Justification, Justifications, StateVersion, Storage,
};
use sp_state_machine::{
	backend::AsTrieBackend, ChildStorageCollection, IndexOperation, OffchainChangesCollection,
	StorageCollection,
};
use sp_storage::{ChildInfo, StorageData, StorageKey};
use std::collections::{HashMap, HashSet};

pub use sp_state_machine::{Backend as StateBackend, KeyValueStates};
use std::marker::PhantomData;

/// Extracts the state backend type for the given backend.
pub type StateBackendFor<B, Block> = <B as Backend<Block>>::State;

/// Extracts the transaction for the given state backend.
pub type TransactionForSB<B, Block> = <B as StateBackend<HashFor<Block>>>::Transaction;

/// Extracts the transaction for the given backend.
pub type TransactionFor<B, Block> = TransactionForSB<StateBackendFor<B, Block>, Block>;

/// Import operation summary.
///
/// Contains information about the block that just got imported,
/// including storage changes, reorged blocks, etc.
pub struct ImportSummary<Block: BlockT> {
	/// Block hash of the imported block.
	pub hash: Block::Hash,
	/// Import origin.
	pub origin: BlockOrigin,
	/// Header of the imported block.
	pub header: Block::Header,
	/// Is this block a new best block.
	pub is_new_best: bool,
	/// Optional storage changes.
	pub storage_changes: Option<(StorageCollection, ChildStorageCollection)>,
	/// Tree route from old best to new best.
	///
	/// If `None`, there was no re-org while importing.
	pub tree_route: Option<sp_blockchain::TreeRoute<Block>>,
}

/// Finalization operation summary.
///
/// Contains information about the block that just got finalized,
/// including tree heads that became stale at the moment of finalization.
pub struct FinalizeSummary<Block: BlockT> {
	/// Last finalized block header.
	pub header: Block::Header,
	/// Blocks that were finalized.
	/// The last entry is the one that has been explicitly finalized.
	pub finalized: Vec<Block::Hash>,
	/// Heads that became stale during this finalization operation.
	pub stale_heads: Vec<Block::Hash>,
}

/// Import operation wrapper.
pub struct ClientImportOperation<Block: BlockT, B: Backend<Block>> {
	/// DB Operation.
	pub op: B::BlockImportOperation,
	/// Summary of imported block.
	pub notify_imported: Option<ImportSummary<Block>>,
	/// Summary of finalized block.
	pub notify_finalized: Option<FinalizeSummary<Block>>,
}

/// Helper function to apply auxiliary data insertion into an operation.
pub fn apply_aux<'a, 'b: 'a, 'c: 'a, B, Block, D, I>(
	operation: &mut ClientImportOperation<Block, B>,
	insert: I,
	delete: D,
) -> sp_blockchain::Result<()>
where
	Block: BlockT,
	B: Backend<Block>,
	I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
	D: IntoIterator<Item = &'a &'b [u8]>,
{
	operation.op.insert_aux(
		insert
			.into_iter()
			.map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
			.chain(delete.into_iter().map(|k| (k.to_vec(), None))),
	)
}

/// State of a new block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NewBlockState {
	/// Normal block.
	Normal,
	/// New best block.
	Best,
	/// Newly finalized block (implicitly best).
	Final,
}

impl NewBlockState {
	/// Whether this block is the new best block.
	pub fn is_best(self) -> bool {
		match self {
			NewBlockState::Best | NewBlockState::Final => true,
			NewBlockState::Normal => false,
		}
	}

	/// Whether this block is considered final.
	pub fn is_final(self) -> bool {
		match self {
			NewBlockState::Final => true,
			NewBlockState::Best | NewBlockState::Normal => false,
		}
	}
}

/// Block insertion operation.
///
/// Keeps hold if the inserted block state and data.
pub trait BlockImportOperation<Block: BlockT> {
	/// Associated state backend type.
	type State: StateBackend<HashFor<Block>>;

	/// Returns pending state.
	///
	/// Returns None for backends with locally-unavailable state data.
	fn state(&self) -> sp_blockchain::Result<Option<&Self::State>>;

	/// Append block data to the transaction.
	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		indexed_body: Option<Vec<Vec<u8>>>,
		justifications: Option<Justifications>,
		state: NewBlockState,
	) -> sp_blockchain::Result<()>;

	/// Update cached data.
	fn update_cache(&mut self, cache: HashMap<well_known_cache_keys::Id, Vec<u8>>);

	/// Inject storage data into the database.
	fn update_db_storage(
		&mut self,
		update: TransactionForSB<Self::State, Block>,
	) -> sp_blockchain::Result<()>;

	/// Set genesis state. If `commit` is `false` the state is saved in memory, but is not written
	/// to the database.
	fn set_genesis_state(
		&mut self,
		storage: Storage,
		commit: bool,
		state_version: StateVersion,
	) -> sp_blockchain::Result<Block::Hash>;

	/// Inject storage data into the database replacing any existing data.
	fn reset_storage(
		&mut self,
		storage: Storage,
		state_version: StateVersion,
	) -> sp_blockchain::Result<Block::Hash>;

	/// Set storage changes.
	fn update_storage(
		&mut self,
		update: StorageCollection,
		child_update: ChildStorageCollection,
	) -> sp_blockchain::Result<()>;

	/// Write offchain storage changes to the database.
	fn update_offchain_storage(
		&mut self,
		_offchain_update: OffchainChangesCollection,
	) -> sp_blockchain::Result<()> {
		Ok(())
	}

	/// Insert auxiliary keys.
	///
	/// Values are `None` if should be deleted.
	fn insert_aux<I>(&mut self, ops: I) -> sp_blockchain::Result<()>
	where
		I: IntoIterator<Item = (Vec<u8>, Option<Vec<u8>>)>;

	/// Mark a block as finalized.
	fn mark_finalized(
		&mut self,
		hash: Block::Hash,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;

	/// Mark a block as new head. If both block import and set head are specified, set head
	/// overrides block import's best block rule.
	fn mark_head(&mut self, hash: Block::Hash) -> sp_blockchain::Result<()>;

	/// Add a transaction index operation.
	fn update_transaction_index(&mut self, index: Vec<IndexOperation>)
		-> sp_blockchain::Result<()>;
}

/// Interface for performing operations on the backend.
pub trait LockImportRun<Block: BlockT, B: Backend<Block>> {
	/// Lock the import lock, and run operations inside.
	fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err>
	where
		F: FnOnce(&mut ClientImportOperation<Block, B>) -> Result<R, Err>,
		Err: From<sp_blockchain::Error>;
}

/// Finalize Facilities
pub trait Finalizer<Block: BlockT, B: Backend<Block>> {
	/// Mark all blocks up to given as finalized in operation.
	///
	/// If `justification` is provided it is stored with the given finalized
	/// block (any other finalized blocks are left unjustified).
	///
	/// If the block being finalized is on a different fork from the current
	/// best block the finalized block is set as best, this might be slightly
	/// inaccurate (i.e. outdated). Usages that require determining an accurate
	/// best block should use `SelectChain` instead of the client.
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		block: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()>;

	/// Finalize a block.
	///
	/// This will implicitly finalize all blocks up to it and
	/// fire finality notifications.
	///
	/// If the block being finalized is on a different fork from the current
	/// best block, the finalized block is set as best. This might be slightly
	/// inaccurate (i.e. outdated). Usages that require determining an accurate
	/// best block should use `SelectChain` instead of the client.
	///
	/// Pass a flag to indicate whether finality notifications should be propagated.
	/// This is usually tied to some synchronization state, where we don't send notifications
	/// while performing major synchronization work.
	fn finalize_block(
		&self,
		block: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()>;
}

/// Provides access to an auxiliary database.
///
/// This is a simple global database not aware of forks. Can be used for storing auxiliary
/// information like total block weight/difficulty for fork resolution purposes as a common use
/// case.
pub trait AuxStore {
	/// Insert auxiliary data into key-value store.
	///
	/// Deletions occur after insertions.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()>;

	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>>;
}

/// An `Iterator` that iterates keys in a given block under a prefix.
pub struct KeyIterator<State, Block> {
	state: State,
	child_storage: Option<ChildInfo>,
	prefix: Option<StorageKey>,
	current_key: Vec<u8>,
	_phantom: PhantomData<Block>,
}

impl<State, Block> KeyIterator<State, Block> {
	/// create a KeyIterator instance
	pub fn new(state: State, prefix: Option<StorageKey>, current_key: Vec<u8>) -> Self {
		Self { state, child_storage: None, prefix, current_key, _phantom: PhantomData }
	}

	/// Create a `KeyIterator` instance for a child storage.
	pub fn new_child(
		state: State,
		child_info: ChildInfo,
		prefix: Option<StorageKey>,
		current_key: Vec<u8>,
	) -> Self {
		Self { state, child_storage: Some(child_info), prefix, current_key, _phantom: PhantomData }
	}
}

impl<State, Block> Iterator for KeyIterator<State, Block>
where
	Block: BlockT,
	State: StateBackend<HashFor<Block>>,
{
	type Item = StorageKey;

	fn next(&mut self) -> Option<Self::Item> {
		let next_key = if let Some(child_info) = self.child_storage.as_ref() {
			self.state.next_child_storage_key(child_info, &self.current_key)
		} else {
			self.state.next_storage_key(&self.current_key)
		}
		.ok()
		.flatten()?;
		// this terminates the iterator the first time it fails.
		if let Some(ref prefix) = self.prefix {
			if !next_key.starts_with(&prefix.0[..]) {
				return None
			}
		}
		self.current_key = next_key.clone();
		Some(StorageKey(next_key))
	}
}

/// Provides acess to storage primitives
pub trait StorageProvider<Block: BlockT, B: Backend<Block>> {
	/// Given a block's `Hash` and a key, return the value under the key in that block.
	fn storage(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>>;

	/// Given a block's `Hash` and a key prefix, return the matching storage keys in that block.
	fn storage_keys(
		&self,
		hash: Block::Hash,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<StorageKey>>;

	/// Given a block's `Hash` and a key, return the value under the hash in that block.
	fn storage_hash(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>>;

	/// Given a block's `Hash` and a key prefix, return the matching child storage keys and values
	/// in that block.
	fn storage_pairs(
		&self,
		hash: Block::Hash,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<(StorageKey, StorageData)>>;

	/// Given a block's `Hash` and a key prefix, return a `KeyIterator` iterates matching storage
	/// keys in that block.
	fn storage_keys_iter(
		&self,
		hash: Block::Hash,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeyIterator<B::State, Block>>;

	/// Given a block's `Hash`, a key and a child storage key, return the value under the key in
	/// that block.
	fn child_storage(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>>;

	/// Given a block's `Hash`, a key prefix, and a child storage key, return the matching child
	/// storage keys.
	fn child_storage_keys(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<StorageKey>>;

	/// Given a block's `Hash` and a key `prefix` and a child storage key,
	/// return a `KeyIterator` that iterates matching storage keys in that block.
	fn child_storage_keys_iter(
		&self,
		hash: Block::Hash,
		child_info: ChildInfo,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeyIterator<B::State, Block>>;

	/// Given a block's `Hash`, a key and a child storage key, return the hash under the key in that
	/// block.
	fn child_storage_hash(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>>;
}

/// Client backend.
///
/// Manages the data layer.
///
/// # State Pruning
///
/// While an object from `state_at` is alive, the state
/// should not be pruned. The backend should internally reference-count
/// its state objects.
///
/// The same applies for live `BlockImportOperation`s: while an import operation building on a
/// parent `P` is alive, the state for `P` should not be pruned.
///
/// # Block Pruning
///
/// Users can pin blocks in memory by calling `pin_block`. When
/// a block would be pruned, its value is kept in an in-memory cache
/// until it is unpinned via `unpin_block`.
///
/// While a block is pinned, its state is also preserved.
///
/// The backend should internally reference count the number of pin / unpin calls.
pub trait Backend<Block: BlockT>: AuxStore + Send + Sync {
	/// Associated block insertion operation type.
	type BlockImportOperation: BlockImportOperation<Block, State = Self::State>;
	/// Associated blockchain backend type.
	type Blockchain: BlockchainBackend<Block>;
	/// Associated state backend type.
	type State: StateBackend<HashFor<Block>>
		+ Send
		+ AsTrieBackend<
			HashFor<Block>,
			TrieBackendStorage = <Self::State as StateBackend<HashFor<Block>>>::TrieBackendStorage,
		>;
	/// Offchain workers local storage.
	type OffchainStorage: OffchainStorage;

	/// Begin a new block insertion transaction with given parent block id.
	///
	/// When constructing the genesis, this is called with all-zero hash.
	fn begin_operation(&self) -> sp_blockchain::Result<Self::BlockImportOperation>;

	/// Note an operation to contain state transition.
	fn begin_state_operation(
		&self,
		operation: &mut Self::BlockImportOperation,
		block: Block::Hash,
	) -> sp_blockchain::Result<()>;

	/// Commit block insertion.
	fn commit_operation(
		&self,
		transaction: Self::BlockImportOperation,
	) -> sp_blockchain::Result<()>;

	/// Finalize block with given `hash`.
	///
	/// This should only be called if the parent of the given block has been finalized.
	fn finalize_block(
		&self,
		hash: Block::Hash,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;

	/// Append justification to the block with the given `hash`.
	///
	/// This should only be called for blocks that are already finalized.
	fn append_justification(
		&self,
		hash: Block::Hash,
		justification: Justification,
	) -> sp_blockchain::Result<()>;

	/// Returns reference to blockchain backend.
	fn blockchain(&self) -> &Self::Blockchain;

	/// Returns current usage statistics.
	fn usage_info(&self) -> Option<UsageInfo>;

	/// Returns a handle to offchain storage.
	fn offchain_storage(&self) -> Option<Self::OffchainStorage>;

	/// Pin the block to keep body, justification and state available after pruning.
	/// Number of pins are reference counted. Users need to make sure to perform
	/// one call to [`Self::unpin_block`] per call to [`Self::pin_block`].
	fn pin_block(&self, hash: Block::Hash) -> sp_blockchain::Result<()>;

	/// Unpin the block to allow pruning.
	fn unpin_block(&self, hash: Block::Hash);

	/// Returns true if state for given block is available.
	fn have_state_at(&self, hash: Block::Hash, _number: NumberFor<Block>) -> bool {
		self.state_at(hash).is_ok()
	}

	/// Returns state backend with post-state of given block.
	fn state_at(&self, hash: Block::Hash) -> sp_blockchain::Result<Self::State>;

	/// Attempts to revert the chain by `n` blocks. If `revert_finalized` is set it will attempt to
	/// revert past any finalized block, this is unsafe and can potentially leave the node in an
	/// inconsistent state. All blocks higher than the best block are also reverted and not counting
	/// towards `n`.
	///
	/// Returns the number of blocks that were successfully reverted and the list of finalized
	/// blocks that has been reverted.
	fn revert(
		&self,
		n: NumberFor<Block>,
		revert_finalized: bool,
	) -> sp_blockchain::Result<(NumberFor<Block>, HashSet<Block::Hash>)>;

	/// Discard non-best, unfinalized leaf block.
	fn remove_leaf_block(&self, hash: Block::Hash) -> sp_blockchain::Result<()>;

	/// Insert auxiliary data into key-value store.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()> {
		AuxStore::insert_aux(self, insert, delete)
	}
	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		AuxStore::get_aux(self, key)
	}

	/// Gain access to the import lock around this backend.
	///
	/// _Note_ Backend isn't expected to acquire the lock by itself ever. Rather
	/// the using components should acquire and hold the lock whenever they do
	/// something that the import of a block would interfere with, e.g. importing
	/// a new block or calculating the best head.
	fn get_import_lock(&self) -> &RwLock<()>;

	/// Tells whether the backend requires full-sync mode.
	fn requires_full_sync(&self) -> bool;
}

/// Mark for all Backend implementations, that are making use of state data, stored locally.
pub trait LocalBackend<Block: BlockT>: Backend<Block> {}
