// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate Client data backend

use std::sync::Arc;
use std::collections::HashMap;
use sp_core::ChangesTrieConfigurationRange;
use sp_core::offchain::OffchainStorage;
use sp_runtime::{generic::BlockId, Justification, Storage};
use sp_runtime::traits::{Block as BlockT, NumberFor, HasherFor};
use sp_state_machine::{
	ChangesTrieState, ChangesTrieStorage as StateChangesTrieStorage, ChangesTrieTransaction,
	StorageCollection, ChildStorageCollection,
};
use crate::{
	blockchain::{
		Backend as BlockchainBackend, well_known_cache_keys
	},
	light::RemoteBlockchain,
	UsageInfo,
};
use sp_blockchain;
use sp_consensus::BlockOrigin;
use parking_lot::RwLock;

pub use sp_state_machine::Backend as StateBackend;

/// Extracts the state backend type for the given backend.
pub type StateBackendFor<B, Block> = <B as Backend<Block>>::State;

/// Extracts the transaction for the given state backend.
pub type TransactionForSB<B, Block> = <B as StateBackend<HasherFor<Block>>>::Transaction;

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
	/// Blocks that got retracted because of this one got imported.
	pub retracted: Vec<Block::Hash>,
}

/// Import operation wrapper
pub struct ClientImportOperation<Block: BlockT, B: Backend<Block>> {
	/// DB Operation.
	pub op: B::BlockImportOperation,
	/// Summary of imported block.
	pub notify_imported: Option<ImportSummary<Block>>,
	/// A list of hashes of blocks that got finalized.
	pub notify_finalized: Vec<Block::Hash>,
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
	type State: StateBackend<HasherFor<Block>>;

	/// Returns pending state.
	///
	/// Returns None for backends with locally-unavailable state data.
	fn state(&self) -> sp_blockchain::Result<Option<&Self::State>>;

	/// Append block data to the transaction.
	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		justification: Option<Justification>,
		state: NewBlockState,
	) -> sp_blockchain::Result<()>;

	/// Update cached data.
	fn update_cache(&mut self, cache: HashMap<well_known_cache_keys::Id, Vec<u8>>);

	/// Inject storage data into the database.
	fn update_db_storage(
		&mut self,
		update: TransactionForSB<Self::State, Block>,
	) -> sp_blockchain::Result<()>;

	/// Inject storage data into the database replacing any existing data.
	fn reset_storage(&mut self, storage: Storage) -> sp_blockchain::Result<Block::Hash>;

	/// Set storage changes.
	fn update_storage(
		&mut self,
		update: StorageCollection,
		child_update: ChildStorageCollection,
	) -> sp_blockchain::Result<()>;

	/// Inject changes trie data into the database.
	fn update_changes_trie(
		&mut self,
		update: ChangesTrieTransaction<HasherFor<Block>, NumberFor<Block>>,
	) -> sp_blockchain::Result<()>;

	/// Insert auxiliary keys.
	///
	/// Values are `None` if should be deleted.
	fn insert_aux<I>(&mut self, ops: I) -> sp_blockchain::Result<()>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>;

	/// Mark a block as finalized.
	fn mark_finalized(
		&mut self,
		id: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;
	/// Mark a block as new head. If both block import and set head are specified, set head
	/// overrides block import's best block rule.
	fn mark_head(&mut self, id: BlockId<Block>) -> sp_blockchain::Result<()>;
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
		id: BlockId<Block>,
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
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()>;

}

/// Provides access to an auxiliary database.
pub trait AuxStore {
	/// Insert auxiliary data into key-value store.
	///
	/// Deletions occur after insertions.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()>;

	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>>;
}

/// Client backend.
///
/// Manages the data layer.
///
/// Note on state pruning: while an object from `state_at` is alive, the state
/// should not be pruned. The backend should internally reference-count
/// its state objects.
///
/// The same applies for live `BlockImportOperation`s: while an import operation building on a
/// parent `P` is alive, the state for `P` should not be pruned.
pub trait Backend<Block: BlockT>: AuxStore + Send + Sync {
	/// Associated block insertion operation type.
	type BlockImportOperation: BlockImportOperation<Block, State = Self::State>;
	/// Associated blockchain backend type.
	type Blockchain: BlockchainBackend<Block>;
	/// Associated state backend type.
	type State: StateBackend<HasherFor<Block>> + Send;
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
		block: BlockId<Block>,
	) -> sp_blockchain::Result<()>;

	/// Commit block insertion.
	fn commit_operation(&self, transaction: Self::BlockImportOperation) -> sp_blockchain::Result<()>;

	/// Finalize block with given Id.
	///
	/// This should only be called if the parent of the given block has been finalized.
	fn finalize_block(
		&self,
		block: BlockId<Block>,
		justification: Option<Justification>,
	) -> sp_blockchain::Result<()>;

	/// Returns reference to blockchain backend.
	fn blockchain(&self) -> &Self::Blockchain;

	/// Returns current usage statistics.
	fn usage_info(&self) -> Option<UsageInfo>;

	/// Returns reference to changes trie storage.
	fn changes_trie_storage(&self) -> Option<&dyn PrunableStateChangesTrieStorage<Block>>;

	/// Returns a handle to offchain storage.
	fn offchain_storage(&self) -> Option<Self::OffchainStorage>;

	/// Returns true if state for given block is available.
	fn have_state_at(&self, hash: &Block::Hash, _number: NumberFor<Block>) -> bool {
		self.state_at(BlockId::Hash(hash.clone())).is_ok()
	}

	/// Returns state backend with post-state of given block.
	fn state_at(&self, block: BlockId<Block>) -> sp_blockchain::Result<Self::State>;

	/// Destroy state and save any useful data, such as cache.
	fn destroy_state(&self, _state: Self::State) -> sp_blockchain::Result<()> {
		Ok(())
	}

	/// Attempts to revert the chain by `n` blocks. If `revert_finalized` is set
	/// it will attempt to revert past any finalized block, this is unsafe and
	/// can potentially leave the node in an inconsistent state.
	///
	/// Returns the number of blocks that were successfully reverted.
	fn revert(
		&self,
		n: NumberFor<Block>,
		revert_finalized: bool,
	) -> sp_blockchain::Result<NumberFor<Block>>;

	/// Insert auxiliary data into key-value store.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()>
	{
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
}

/// Changes trie storage that supports pruning.
pub trait PrunableStateChangesTrieStorage<Block: BlockT>:
	StateChangesTrieStorage<HasherFor<Block>, NumberFor<Block>>
{
	/// Get reference to StateChangesTrieStorage.
	fn storage(&self) -> &dyn StateChangesTrieStorage<HasherFor<Block>, NumberFor<Block>>;
	/// Get configuration at given block.
	fn configuration_at(&self, at: &BlockId<Block>) -> sp_blockchain::Result<
		ChangesTrieConfigurationRange<NumberFor<Block>, Block::Hash>
	>;
	/// Get end block (inclusive) of oldest pruned max-level (or skewed) digest trie blocks range.
	/// It is guaranteed that we have no any changes tries before (and including) this block.
	/// It is guaranteed that all existing changes tries after this block are not yet pruned (if created).
	fn oldest_pruned_digest_range_end(&self) -> NumberFor<Block>;
}

/// Mark for all Backend implementations, that are making use of state data, stored locally.
pub trait LocalBackend<Block: BlockT>: Backend<Block> {}

/// Mark for all Backend implementations, that are fetching required state data from remote nodes.
pub trait RemoteBackend<Block: BlockT>: Backend<Block> {
	/// Returns true if the state for given block is available locally.
	fn is_local_state_available(&self, block: &BlockId<Block>) -> bool;

	/// Returns reference to blockchain backend.
	///
	/// Returned backend either resolves blockchain data
	/// locally, or prepares request to fetch that data from remote node.
	fn remote_blockchain(&self) -> Arc<dyn RemoteBlockchain<Block>>;
}

/// Return changes tries state at given block.
pub fn changes_tries_state_at_block<'a, Block: BlockT>(
	block: &BlockId<Block>,
	maybe_storage: Option<&'a dyn PrunableStateChangesTrieStorage<Block>>,
) -> sp_blockchain::Result<Option<ChangesTrieState<'a, HasherFor<Block>, NumberFor<Block>>>> {
	let storage = match maybe_storage {
		Some(storage) => storage,
		None => return Ok(None),
	};

	let config_range = storage.configuration_at(block)?;
	match config_range.config {
		Some(config) => Ok(Some(ChangesTrieState::new(config, config_range.zero.0, storage.storage()))),
		None => Ok(None),
	}
}
