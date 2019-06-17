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

//! Client backend that uses RocksDB database as storage.
//!
//! # Canonicality vs. Finality
//!
//! Finality indicates that a block will not be reverted, according to the consensus algorithm,
//! while canonicality indicates that the block may be reverted, but we will be unable to do so,
//! having discarded heavy state that will allow a chain reorganization.
//!
//! Finality implies canonicality but not vice-versa.

pub mod light;

mod cache;
mod storage_cache;
mod utils;

use std::sync::Arc;
use std::path::PathBuf;
use std::io;
use std::collections::HashMap;

use client::backend::NewBlockState;
use client::blockchain::HeaderBackend;
use client::ExecutionStrategies;
use client::backend::{StorageCollection, ChildStorageCollection};
use parity_codec::{Decode, Encode};
use hash_db::Hasher;
use kvdb::{KeyValueDB, DBTransaction};
use trie::{MemoryDB, PrefixedMemoryDB, prefixed_key};
use parking_lot::{Mutex, RwLock};
use primitives::{H256, Blake2Hasher, ChangesTrieConfiguration, convert_hash};
use primitives::storage::well_known_keys;
use runtime_primitives::{
	generic::{BlockId, DigestItem}, Justification, StorageOverlay, ChildrenStorageOverlay,
	BuildStorage
};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, One, SaturatedConversion
};
use state_machine::backend::Backend as StateBackend;
use executor::RuntimeInfo;
use state_machine::{CodeExecutor, DBValue};
use crate::utils::{Meta, db_err, meta_keys, read_db, block_id_to_lookup_key, read_meta};
use client::leaves::{LeafSet, FinalizationDisplaced};
use client::children;
use state_db::StateDb;
use consensus_common::well_known_cache_keys;
use crate::storage_cache::{CachingState, SharedCache, new_shared_cache};
use log::{trace, debug, warn};
pub use state_db::PruningMode;

#[cfg(feature = "test-helpers")]
use client::in_mem::Backend as InMemoryBackend;

const CANONICALIZATION_DELAY: u64 = 4096;
const MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR: u32 = 32768;

/// Default value for storage cache child ratio.
const DEFAULT_CHILD_RATIO: (usize, usize) = (1, 10);

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
pub type DbState = state_machine::TrieBackend<Arc<dyn state_machine::Storage<Blake2Hasher>>, Blake2Hasher>;

pub struct RefTrackingState<Block: BlockT> {
	state: DbState,
	storage: Arc<StorageDb<Block>>,
	parent_hash: Option<Block::Hash>,
}

impl<B: BlockT> RefTrackingState<B> {
	fn new(state: DbState, storage: Arc<StorageDb<B>>, parent_hash: Option<B::Hash>) -> RefTrackingState<B> {
		if let Some(hash) = &parent_hash {
			storage.state_db.pin(hash);
		}
		RefTrackingState {
			state,
			parent_hash,
			storage,
		}
	}
}

impl<B: BlockT> Drop for RefTrackingState<B> {
	fn drop(&mut self) {
		if let Some(hash) = &self.parent_hash {
			self.storage.state_db.unpin(hash);
		}
	}
}

impl<B: BlockT> StateBackend<Blake2Hasher> for RefTrackingState<B> {
	type Error =  <DbState as StateBackend<Blake2Hasher>>::Error;
	type Transaction = <DbState as StateBackend<Blake2Hasher>>::Transaction;
	type TrieBackendStorage = <DbState as StateBackend<Blake2Hasher>>::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<H256>, Self::Error> {
		self.state.storage_hash(key)
	}

	fn child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.child_storage(storage_key, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_storage(key)
	}

	fn exists_child_storage(&self, storage_key: &[u8], key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(storage_key, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], f: F) {
		self.state.for_keys_in_child_storage(storage_key, f)
	}

	fn storage_root<I>(&self, delta: I) -> (H256, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.state.storage_root(delta)
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
		where
			I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
	{
		self.state.child_storage_root(storage_key, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(&self, child_key: &[u8], prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.child_keys(child_key, prefix)
	}

	fn as_trie_backend(&mut self) -> Option<&state_machine::TrieBackend<Self::TrieBackendStorage, Blake2Hasher>> {
		self.state.as_trie_backend()
	}
}

/// Database settings.
pub struct DatabaseSettings {
	/// Cache size in bytes. If `None` default is used.
	pub cache_size: Option<usize>,
	/// State cache size.
	pub state_cache_size: usize,
	/// Ratio of cache size dedicated to child tries.
	pub state_cache_child_ratio: Option<(usize, usize)>,
	/// Path to the database.
	pub path: PathBuf,
	/// Pruning mode.
	pub pruning: PruningMode,
}

/// Create an instance of db-backed client.
pub fn new_client<E, S, Block, RA>(
	settings: DatabaseSettings,
	executor: E,
	genesis_storage: S,
	execution_strategies: ExecutionStrategies,
) -> Result<
	client::Client<Backend<Block>,
	client::LocalCallExecutor<Backend<Block>, E>, Block, RA>, client::error::Error
>
	where
		Block: BlockT<Hash=H256>,
		E: CodeExecutor<Blake2Hasher> + RuntimeInfo,
		S: BuildStorage,
{
	let backend = Arc::new(Backend::new(settings, CANONICALIZATION_DELAY)?);
	let executor = client::LocalCallExecutor::new(backend.clone(), executor);
	Ok(client::Client::new(backend, executor, genesis_storage, execution_strategies)?)
}

mod columns {
	pub const META: Option<u32> = crate::utils::COLUMN_META;
	pub const STATE: Option<u32> = Some(1);
	pub const STATE_META: Option<u32> = Some(2);
	/// maps hashes to lookup keys and numbers to canon hashes.
	pub const KEY_LOOKUP: Option<u32> = Some(3);
	pub const HEADER: Option<u32> = Some(4);
	pub const BODY: Option<u32> = Some(5);
	pub const JUSTIFICATION: Option<u32> = Some(6);
	pub const CHANGES_TRIE: Option<u32> = Some(7);
	pub const AUX: Option<u32> = Some(8);
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justification: Option<Justification>,
	body: Option<Vec<Block::Extrinsic>>,
	leaf_state: NewBlockState,
}

// wrapper that implements trait required for state_db
struct StateMetaDb<'a>(&'a dyn KeyValueDB);

impl<'a> state_db::MetaDb for StateMetaDb<'a> {
	type Error = io::Error;

	fn get_meta(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.0.get(columns::STATE_META, key).map(|r| r.map(|v| v.to_vec()))
	}
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<dyn KeyValueDB>,
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
}

impl<Block: BlockT> BlockchainDb<Block> {
	fn new(db: Arc<dyn KeyValueDB>) -> Result<Self, client::error::Error> {
		let meta = read_meta::<Block>(&*db, columns::META, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		Ok(BlockchainDb {
			db,
			leaves: RwLock::new(leaves),
			meta: Arc::new(RwLock::new(meta)),
		})
	}

	fn update_meta(
		&self,
		hash: Block::Hash,
		number: <Block::Header as HeaderT>::Number,
		is_best: bool,
		is_finalized: bool
	) {
		let mut meta = self.meta.write();
		if number.is_zero() {
			meta.genesis_hash = hash;
			meta.finalized_hash = hash;
		}

		if is_best {
			meta.best_number = number;
			meta.best_hash = hash;
		}

		if is_finalized {
			meta.finalized_number = number;
			meta.finalized_hash = hash;
		}
	}
}

impl<Block: BlockT> client::blockchain::HeaderBackend<Block> for BlockchainDb<Block> {
	fn header(&self, id: BlockId<Block>) -> Result<Option<Block::Header>, client::error::Error> {
		utils::read_header(&*self.db, columns::KEY_LOOKUP, columns::HEADER, id)
	}

	fn info(&self) -> client::blockchain::Info<Block> {
		let meta = self.meta.read();
		client::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
			finalized_hash: meta.finalized_hash,
			finalized_number: meta.finalized_number,
		}
	}

	fn status(&self, id: BlockId<Block>) -> Result<client::blockchain::BlockStatus, client::error::Error> {
		let exists = match id {
			BlockId::Hash(_) => read_db(
				&*self.db,
				columns::KEY_LOOKUP,
				columns::HEADER,
				id
			)?.is_some(),
			BlockId::Number(n) => n <= self.meta.read().best_number,
		};
		match exists {
			true => Ok(client::blockchain::BlockStatus::InChain),
			false => Ok(client::blockchain::BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> Result<Option<NumberFor<Block>>, client::error::Error> {
		if let Some(lookup_key) = block_id_to_lookup_key::<Block>(&*self.db, columns::KEY_LOOKUP, BlockId::Hash(hash))? {
			let number = utils::lookup_key_to_number(&lookup_key)?;
			Ok(Some(number))
		} else {
			Ok(None)
		}
	}

	fn hash(&self, number: NumberFor<Block>) -> Result<Option<Block::Hash>, client::error::Error> {
		self.header(BlockId::Number(number)).and_then(|maybe_header| match maybe_header {
			Some(header) => Ok(Some(header.hash().clone())),
			None => Ok(None),
		})
	}
}

impl<Block: BlockT> client::blockchain::Backend<Block> for BlockchainDb<Block> {
	fn body(&self, id: BlockId<Block>) -> Result<Option<Vec<Block::Extrinsic>>, client::error::Error> {
		match read_db(&*self.db, columns::KEY_LOOKUP, columns::BODY, id)? {
			Some(body) => match Decode::decode(&mut &body[..]) {
				Some(body) => Ok(Some(body)),
				None => return Err(client::error::Error::Backend("Error decoding body".into())),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId<Block>) -> Result<Option<Justification>, client::error::Error> {
		match read_db(&*self.db, columns::KEY_LOOKUP, columns::JUSTIFICATION, id)? {
			Some(justification) => match Decode::decode(&mut &justification[..]) {
				Some(justification) => Ok(Some(justification)),
				None => return Err(client::error::Error::Backend("Error decoding justification".into())),
			}
			None => Ok(None),
		}
	}

	fn last_finalized(&self) -> Result<Block::Hash, client::error::Error> {
		Ok(self.meta.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<Arc<dyn client::blockchain::Cache<Block>>> {
		None
	}

	fn leaves(&self) -> Result<Vec<Block::Hash>, client::error::Error> {
		Ok(self.leaves.read().hashes())
	}

	fn children(&self, parent_hash: Block::Hash) -> Result<Vec<Block::Hash>, client::error::Error> {
		children::read_children(&*self.db, columns::META, meta_keys::CHILDREN_PREFIX, parent_hash)
	}
}

impl<Block: BlockT> client::blockchain::ProvideCache<Block> for BlockchainDb<Block> {
	fn cache(&self) -> Option<Arc<dyn client::blockchain::Cache<Block>>> {
		None
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT, H: Hasher> {
	old_state: CachingState<Blake2Hasher, RefTrackingState<Block>, Block>,
	db_updates: PrefixedMemoryDB<H>,
	storage_updates: StorageCollection,
	child_storage_updates: ChildStorageCollection,
	changes_trie_updates: MemoryDB<H>,
	pending_block: Option<PendingBlock<Block>>,
	aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(BlockId<Block>, Option<Justification>)>,
	set_head: Option<BlockId<Block>>,
}

impl<Block: BlockT, H: Hasher> BlockImportOperation<Block, H> {
	fn apply_aux(&mut self, transaction: &mut DBTransaction) {
		for (key, maybe_val) in self.aux_ops.drain(..) {
			match maybe_val {
				Some(val) => transaction.put_vec(columns::AUX, &key, val),
				None => transaction.delete(columns::AUX, &key),
			}
		}
	}
}

impl<Block> client::backend::BlockImportOperation<Block, Blake2Hasher>
for BlockImportOperation<Block, Blake2Hasher>
where Block: BlockT<Hash=H256>,
{
	type State = CachingState<Blake2Hasher, RefTrackingState<Block>, Block>;

	fn state(&self) -> Result<Option<&Self::State>, client::error::Error> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		justification: Option<Justification>,
		leaf_state: NewBlockState,
	) -> Result<(), client::error::Error> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			header,
			body,
			justification,
			leaf_state,
		});
		Ok(())
	}

	fn update_cache(&mut self, _cache: HashMap<well_known_cache_keys::Id, Vec<u8>>) {
		// Currently cache isn't implemented on full nodes.
	}

	fn update_db_storage(&mut self, update: PrefixedMemoryDB<Blake2Hasher>) -> Result<(), client::error::Error> {
		self.db_updates = update;
		Ok(())
	}

	fn reset_storage(
		&mut self,
		top: StorageOverlay,
		children: ChildrenStorageOverlay
	) -> Result<H256, client::error::Error> {

		if top.iter().any(|(k, _)| well_known_keys::is_child_storage_key(k)) {
			return Err(client::error::Error::GenesisInvalid.into());
		}

		for child_key in children.keys() {
			if !well_known_keys::is_child_storage_key(&child_key) {
				return Err(client::error::Error::GenesisInvalid.into());
			}
		}

		let child_delta = children.into_iter()
			.map(|(storage_key, child_overlay)|
				(storage_key, child_overlay.into_iter().map(|(k, v)| (k, Some(v)))));

		let (root, transaction) = self.old_state.full_storage_root(
			top.into_iter().map(|(k, v)| (k, Some(v))),
			child_delta
		);

		self.db_updates = transaction;
		Ok(root)
	}

	fn update_changes_trie(&mut self, update: MemoryDB<Blake2Hasher>) -> Result<(), client::error::Error> {
		self.changes_trie_updates = update;
		Ok(())
	}

	fn insert_aux<I>(&mut self, ops: I) -> Result<(), client::error::Error>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.aux_ops.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(
		&mut self,
		update: StorageCollection,
		child_update: ChildStorageCollection,
	) -> Result<(), client::error::Error> {
		self.storage_updates = update;
		self.child_storage_updates = child_update;
		Ok(())
	}

	fn mark_finalized(&mut self, block: BlockId<Block>, justification: Option<Justification>) -> Result<(), client::error::Error> {
		self.finalized_blocks.push((block, justification));
		Ok(())
	}

	fn mark_head(&mut self, block: BlockId<Block>) -> Result<(), client::error::Error> {
		assert!(self.set_head.is_none(), "Only one set head per operation is allowed");
		self.set_head = Some(block);
		Ok(())
	}
}

struct StorageDb<Block: BlockT> {
	pub db: Arc<dyn KeyValueDB>,
	pub state_db: StateDb<Block::Hash, Vec<u8>>,
}

impl<Block: BlockT> state_machine::Storage<Blake2Hasher> for StorageDb<Block> {
	fn get(&self, key: &H256, prefix: &[u8]) -> Result<Option<DBValue>, String> {
		let key = prefixed_key::<Blake2Hasher>(key, prefix);
		self.state_db.get(&key, self).map(|r| r.map(|v| DBValue::from_slice(&v)))
			.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

impl<Block: BlockT> state_db::NodeDb for StorageDb<Block> {
	type Error = io::Error;
	type Key = [u8];

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.db.get(columns::STATE, key).map(|r| r.map(|v| v.to_vec()))
	}
}

struct DbGenesisStorage(pub H256);

impl DbGenesisStorage {
	pub fn new() -> Self {
		let mut root = H256::default();
		let mut mdb = MemoryDB::<Blake2Hasher>::default();
		state_machine::TrieDBMut::<Blake2Hasher>::new(&mut mdb, &mut root);
		DbGenesisStorage(root)
	}
}

impl state_machine::Storage<Blake2Hasher> for DbGenesisStorage {
	fn get(&self, _key: &H256, _prefix: &[u8]) -> Result<Option<DBValue>, String> {
		Ok(None)
	}
}

pub struct DbChangesTrieStorage<Block: BlockT> {
	db: Arc<dyn KeyValueDB>,
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	min_blocks_to_keep: Option<u32>,
	_phantom: ::std::marker::PhantomData<Block>,
}

impl<Block: BlockT<Hash=H256>> DbChangesTrieStorage<Block> {
	/// Commit new changes trie.
	pub fn commit(&self, tx: &mut DBTransaction, mut changes_trie: MemoryDB<Blake2Hasher>) {
		for (key, (val, _)) in changes_trie.drain() {
			tx.put(columns::CHANGES_TRIE, &key[..], &val);
		}
	}

	/// Prune obsolete changes tries.
	pub fn prune(
		&self,
		config: &ChangesTrieConfiguration,
		tx: &mut DBTransaction,
		block_hash: Block::Hash,
		block_num: NumberFor<Block>,
	) {
		// never prune on archive nodes
		let min_blocks_to_keep = match self.min_blocks_to_keep {
			Some(min_blocks_to_keep) => min_blocks_to_keep,
			None => return,
		};

		state_machine::prune_changes_tries(
			config,
			&*self,
			min_blocks_to_keep.into(),
			&state_machine::ChangesTrieAnchorBlockId {
				hash: convert_hash(&block_hash),
				number: block_num,
			},
			|node| tx.delete(columns::CHANGES_TRIE, node.as_ref()));
	}
}

impl<Block> client::backend::PrunableStateChangesTrieStorage<Block, Blake2Hasher>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn oldest_changes_trie_block(
		&self,
		config: &ChangesTrieConfiguration,
		best_finalized_block: NumberFor<Block>,
	) -> NumberFor<Block> {
		match self.min_blocks_to_keep {
			Some(min_blocks_to_keep) => state_machine::oldest_non_pruned_changes_trie(
				config,
				min_blocks_to_keep.into(),
				best_finalized_block,
			),
			None => One::one(),
		}
	}
}

impl<Block> state_machine::ChangesTrieRootsStorage<Blake2Hasher, NumberFor<Block>>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn build_anchor(
		&self,
		hash: H256,
	) -> Result<state_machine::ChangesTrieAnchorBlockId<H256, NumberFor<Block>>, String> {
		utils::read_header::<Block>(&*self.db, columns::KEY_LOOKUP, columns::HEADER, BlockId::Hash(hash))
			.map_err(|e| e.to_string())
			.and_then(|maybe_header| maybe_header.map(|header|
				state_machine::ChangesTrieAnchorBlockId {
					hash,
					number: *header.number(),
				}
			).ok_or_else(|| format!("Unknown header: {}", hash)))
	}

	fn root(
		&self,
		anchor: &state_machine::ChangesTrieAnchorBlockId<H256, NumberFor<Block>>,
		block: NumberFor<Block>,
	) -> Result<Option<H256>, String> {
		// check API requirement: we can't get NEXT block(s) based on anchor
		if block > anchor.number {
			return Err(format!("Can't get changes trie root at {} using anchor at {}", block, anchor.number));
		}

		// we need to get hash of the block to resolve changes trie root
		let block_id = if block <= self.meta.read().finalized_number {
			// if block is finalized, we could just read canonical hash
			BlockId::Number(block)
		} else {
			// the block is not finalized
			let mut current_num = anchor.number;
			let mut current_hash: Block::Hash = convert_hash(&anchor.hash);
			let maybe_anchor_header: Block::Header = utils::require_header::<Block>(
				&*self.db, columns::KEY_LOOKUP, columns::HEADER, BlockId::Number(current_num)
			).map_err(|e| e.to_string())?;
			if maybe_anchor_header.hash() == current_hash {
				// if anchor is canonicalized, then the block is also canonicalized
				BlockId::Number(block)
			} else {
				// else (block is not finalized + anchor is not canonicalized):
				// => we should find the required block hash by traversing
				// back from the anchor to the block with given number
				while current_num != block {
					let current_header: Block::Header = utils::require_header::<Block>(
						&*self.db, columns::KEY_LOOKUP, columns::HEADER, BlockId::Hash(current_hash)
					).map_err(|e| e.to_string())?;

					current_hash = *current_header.parent_hash();
					current_num = current_num - One::one();
				}

				BlockId::Hash(current_hash)
			}
		};

		Ok(utils::require_header::<Block>(&*self.db, columns::KEY_LOOKUP, columns::HEADER, block_id)
			.map_err(|e| e.to_string())?
			.digest().log(DigestItem::as_changes_trie_root)
			.map(|root| H256::from_slice(root.as_ref())))
	}
}

impl<Block> state_machine::ChangesTrieStorage<Blake2Hasher, NumberFor<Block>>
	for DbChangesTrieStorage<Block>
where
	Block: BlockT<Hash=H256>,
{
	fn get(&self, key: &H256, _prefix: &[u8]) -> Result<Option<DBValue>, String> {
		self.db.get(columns::CHANGES_TRIE, &key[..])
			.map_err(|err| format!("{}", err))
	}
}

/// Disk backend. Keeps data in a key-value store. In archive mode, trie nodes are kept from all blocks.
/// Otherwise, trie nodes are kept only from some recent blocks.
pub struct Backend<Block: BlockT> {
	storage: Arc<StorageDb<Block>>,
	changes_tries_storage: DbChangesTrieStorage<Block>,
	/// None<*> means that the value hasn't been cached yet. Some(*) means that the value (either None or
	/// Some(*)) has been cached and is valid.
	changes_trie_config: Mutex<Option<Option<ChangesTrieConfiguration>>>,
	blockchain: BlockchainDb<Block>,
	canonicalization_delay: u64,
	shared_cache: SharedCache<Block, Blake2Hasher>,
	import_lock: Mutex<()>,
}

impl<Block: BlockT<Hash=H256>> Backend<Block> {
	/// Create a new instance of database backend.
	///
	/// The pruning window is how old a block must be before the state is pruned.
	pub fn new(config: DatabaseSettings, canonicalization_delay: u64) -> Result<Self, client::error::Error> {
		Self::new_inner(config, canonicalization_delay)
	}

	#[cfg(feature = "kvdb-rocksdb")]
	fn new_inner(config: DatabaseSettings, canonicalization_delay: u64) -> Result<Self, client::error::Error> {
		let db = crate::utils::open_database(&config, columns::META, "full")?;
		Backend::from_kvdb(db as Arc<_>, canonicalization_delay, &config)
	}

	#[cfg(not(feature = "kvdb-rocksdb"))]
	fn new_inner(config: DatabaseSettings, canonicalization_delay: u64) -> Result<Self, client::error::Error> {
		log::warn!("Running without the RocksDB feature. The database will NOT be saved.");
		let db = Arc::new(kvdb_memorydb::create(crate::utils::NUM_COLUMNS));
		Backend::from_kvdb(db as Arc<_>, canonicalization_delay, &config)
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test(keep_blocks: u32, canonicalization_delay: u64) -> Self {
		use utils::NUM_COLUMNS;

		let db = Arc::new(::kvdb_memorydb::create(NUM_COLUMNS));
		Self::new_test_db(keep_blocks, canonicalization_delay, db as Arc<_>)
	}

	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test_db(keep_blocks: u32, canonicalization_delay: u64, db: Arc<dyn KeyValueDB>) -> Self {

		let db_setting = DatabaseSettings {
			cache_size: None,
			state_cache_size: 16777216,
			state_cache_child_ratio: Some((50, 100)),
			path: Default::default(),
			pruning: PruningMode::keep_blocks(keep_blocks),
		};
		Backend::from_kvdb(
			db,
			canonicalization_delay,
			&db_setting,
		).expect("failed to create test-db")
	}

	fn from_kvdb(
		db: Arc<dyn KeyValueDB>,
		canonicalization_delay: u64,
		config: &DatabaseSettings
	) -> Result<Self, client::error::Error> {
		let is_archive_pruning = config.pruning.is_archive();
		let blockchain = BlockchainDb::new(db.clone())?;
		let meta = blockchain.meta.clone();
		let map_e = |e: state_db::Error<io::Error>| ::client::error::Error::from(format!("State database error: {:?}", e));
		let state_db: StateDb<_, _> = StateDb::new(config.pruning.clone(), &StateMetaDb(&*db)).map_err(map_e)?;
		let storage_db = StorageDb {
			db: db.clone(),
			state_db,
		};
		let changes_tries_storage = DbChangesTrieStorage {
			db,
			meta,
			min_blocks_to_keep: if is_archive_pruning { None } else { Some(MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR) },
			_phantom: Default::default(),
		};

		Ok(Backend {
			storage: Arc::new(storage_db),
			changes_tries_storage,
			changes_trie_config: Mutex::new(None),
			blockchain,
			canonicalization_delay,
			shared_cache: new_shared_cache(
				config.state_cache_size,
				config.state_cache_child_ratio.unwrap_or(DEFAULT_CHILD_RATIO),
			),
			import_lock: Default::default(),
		})
	}

	/// Returns in-memory blockchain that contains the same set of blocks that the self.
	#[cfg(feature = "test-helpers")]
	pub fn as_in_memory(&self) -> InMemoryBackend<Block, Blake2Hasher> {
		use client::backend::{Backend as ClientBackend, BlockImportOperation};
		use client::blockchain::Backend as BlockchainBackend;

		let inmem = InMemoryBackend::<Block, Blake2Hasher>::new();

		// get all headers hashes && sort them by number (could be duplicate)
		let mut headers: Vec<(NumberFor<Block>, Block::Hash, Block::Header)> = Vec::new();
		for (_, header) in self.blockchain.db.iter(columns::HEADER) {
			let header = Block::Header::decode(&mut &header[..]).unwrap();
			let hash = header.hash();
			let number = *header.number();
			let pos = headers.binary_search_by(|item| item.0.cmp(&number));
			match pos {
				Ok(pos) => headers.insert(pos, (number, hash, header)),
				Err(pos) => headers.insert(pos, (number, hash, header)),
			}
		}

		// insert all other headers + bodies + justifications
		let info = self.blockchain.info();
		for (number, hash, header) in headers {
			let id = BlockId::Hash(hash);
			let justification = self.blockchain.justification(id).unwrap();
			let body = self.blockchain.body(id).unwrap();
			let state = self.state_at(id).unwrap().pairs();

			let new_block_state = if number.is_zero() {
				NewBlockState::Final
			} else if hash == info.best_hash {
				NewBlockState::Best
			} else {
				NewBlockState::Normal
			};
			let mut op = inmem.begin_operation().unwrap();
			op.set_block_data(header, body, justification, new_block_state).unwrap();
			op.update_db_storage(state.into_iter().map(|(k, v)| (None, k, Some(v))).collect()).unwrap();
			inmem.commit_operation(op).unwrap();
		}

		// and now finalize the best block we have
		inmem.finalize_block(BlockId::Hash(info.finalized_hash), None).unwrap();

		inmem
	}

	/// Read (from storage or cache) changes trie config.
	///
	/// Currently changes tries configuration is set up once (at genesis) and could not
	/// be changed. Thus, we'll actually read value once and then just use cached value.
	fn changes_trie_config(&self, block: Block::Hash) -> Result<Option<ChangesTrieConfiguration>, client::error::Error> {
		let mut cached_changes_trie_config = self.changes_trie_config.lock();
		match cached_changes_trie_config.clone() {
			Some(cached_changes_trie_config) => Ok(cached_changes_trie_config),
			None => {
				use client::backend::Backend;
				let changes_trie_config = self
					.state_at(BlockId::Hash(block))?
					.storage(well_known_keys::CHANGES_TRIE_CONFIG)?
					.and_then(|v| Decode::decode(&mut &*v));
				*cached_changes_trie_config = Some(changes_trie_config.clone());
				Ok(changes_trie_config)
			},
		}
	}

	/// Handle setting head within a transaction. `route_to` should be the last
	/// block that existed in the database. `best_to` should be the best block
	/// to be set.
	///
	/// In the case where the new best block is a block to be imported, `route_to`
	/// should be the parent of `best_to`. In the case where we set an existing block
	/// to be best, `route_to` should equal to `best_to`.
	fn set_head_with_transaction(&self, transaction: &mut DBTransaction, route_to: Block::Hash, best_to: (NumberFor<Block>, Block::Hash)) -> Result<(Vec<Block::Hash>, Vec<Block::Hash>), client::error::Error> {
		let mut enacted = Vec::default();
		let mut retracted = Vec::default();

		let meta = self.blockchain.meta.read();

		// cannot find tree route with empty DB.
		if meta.best_hash != Default::default() {
			let tree_route = ::client::blockchain::tree_route(
				&self.blockchain,
				BlockId::Hash(meta.best_hash),
				BlockId::Hash(route_to),
			)?;

			// uncanonicalize: check safety violations and ensure the numbers no longer
			// point to these block hashes in the key mapping.
			for r in tree_route.retracted() {
				if r.hash == meta.finalized_hash {
					warn!(
						"Potential safety failure: reverting finalized block {:?}",
						(&r.number, &r.hash)
					);

					return Err(::client::error::Error::NotInFinalizedChain.into());
				}

				retracted.push(r.hash.clone());
				utils::remove_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					r.number
				);
			}

			// canonicalize: set the number lookup to map to this block's hash.
			for e in tree_route.enacted() {
				enacted.push(e.hash.clone());
				utils::insert_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					e.number,
					e.hash
				);
			}
		}

		let lookup_key = utils::number_and_hash_to_lookup_key(best_to.0, &best_to.1);
		transaction.put(columns::META, meta_keys::BEST_BLOCK, &lookup_key);
		utils::insert_number_to_key_mapping(
			transaction,
			columns::KEY_LOOKUP,
			best_to.0,
			best_to.1,
		);

		Ok((enacted, retracted))
	}

	fn ensure_sequential_finalization(
		&self,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
	) -> Result<(), client::error::Error> {
		let last_finalized = last_finalized.unwrap_or_else(|| self.blockchain.meta.read().finalized_hash);
		if *header.parent_hash() != last_finalized {
			return Err(::client::error::Error::NonSequentialFinalization(
				format!("Last finalized {:?} not parent of {:?}", last_finalized, header.hash()),
			).into());
		}
		Ok(())
	}

	fn finalize_block_with_transaction(
		&self,
		transaction: &mut DBTransaction,
		hash: &Block::Hash,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
		justification: Option<Justification>,
		finalization_displaced: &mut Option<FinalizationDisplaced<Block::Hash, NumberFor<Block>>>,
	) -> Result<(Block::Hash, <Block::Header as HeaderT>::Number, bool, bool), client::error::Error> {
		// TODO: ensure best chain contains this block.
		let number = *header.number();
		self.ensure_sequential_finalization(header, last_finalized)?;
		self.note_finalized(
			transaction,
			header,
			*hash,
			finalization_displaced,
		)?;

		if let Some(justification) = justification {
			transaction.put(
				columns::JUSTIFICATION,
				&utils::number_and_hash_to_lookup_key(number, hash),
				&justification.encode(),
			);
		}
		Ok((*hash, number, false, true))
	}

	// performs forced canonicaliziation with a delay after importing a non-finalized block.
	fn force_delayed_canonicalize(
		&self,
		transaction: &mut DBTransaction,
		hash: Block::Hash,
		number: NumberFor<Block>,
	)
		-> Result<(), client::error::Error>
	{
		let number_u64 = number.saturated_into::<u64>();
		if number_u64 > self.canonicalization_delay {
			let new_canonical = number_u64 - self.canonicalization_delay;

			if new_canonical <= self.storage.state_db.best_canonical().unwrap_or(0) {
				return Ok(())
			}

			let hash = if new_canonical == number_u64 {
				hash
			} else {
				::client::blockchain::HeaderBackend::hash(&self.blockchain, new_canonical.saturated_into())?
					.expect("existence of block with number `new_canonical` \
						implies existence of blocks with all numbers before it; qed")
			};

			trace!(target: "db", "Canonicalize block #{} ({:?})", new_canonical, hash);
			let commit = self.storage.state_db.canonicalize_block(&hash)
				.map_err(|e: state_db::Error<io::Error>| client::error::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(transaction, commit);
		};

		Ok(())
	}

	fn try_commit_operation(&self, mut operation: BlockImportOperation<Block, Blake2Hasher>)
		-> Result<(), client::error::Error>
	{
		let mut transaction = DBTransaction::new();
		let mut finalization_displaced_leaves = None;

		operation.apply_aux(&mut transaction);

		let mut meta_updates = Vec::new();
		let mut last_finalized_hash = self.blockchain.meta.read().finalized_hash;

		if !operation.finalized_blocks.is_empty() {
			for (block, justification) in operation.finalized_blocks {
				let block_hash = self.blockchain.expect_block_hash_from_id(&block)?;
				let block_header = self.blockchain.expect_header(BlockId::Hash(block_hash))?;

				meta_updates.push(self.finalize_block_with_transaction(
					&mut transaction,
					&block_hash,
					&block_header,
					Some(last_finalized_hash),
					justification,
					&mut finalization_displaced_leaves,
				)?);
				last_finalized_hash = block_hash;
			}
		}

		let imported = if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();
			let parent_hash = *pending_block.header.parent_hash();
			let number = pending_block.header.number().clone();

			// blocks are keyed by number + hash.
			let lookup_key = utils::number_and_hash_to_lookup_key(number, hash);

			let (enacted, retracted) = if pending_block.leaf_state.is_best() {
				self.set_head_with_transaction(&mut transaction, parent_hash, (number, hash))?
			} else {
				(Default::default(), Default::default())
			};

			utils::insert_hash_to_key_mapping(
				&mut transaction,
				columns::KEY_LOOKUP,
				number,
				hash,
			);

			transaction.put(columns::HEADER, &lookup_key, &pending_block.header.encode());
			if let Some(body) = pending_block.body {
				transaction.put(columns::BODY, &lookup_key, &body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.put(columns::JUSTIFICATION, &lookup_key, &justification.encode());
			}

			if number.is_zero() {
				transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, &lookup_key);
				transaction.put(columns::META, meta_keys::GENESIS_HASH, hash.as_ref());
			}

			let mut changeset: state_db::ChangeSet<Vec<u8>> = state_db::ChangeSet::default();
			for (key, (val, rc)) in operation.db_updates.drain() {
				if rc > 0 {
					changeset.inserted.push((key, val.to_vec()));
				} else if rc < 0 {
					changeset.deleted.push(key);
				}
			}
			let number_u64 = number.saturated_into::<u64>();
			let commit = self.storage.state_db.insert_block(&hash, number_u64, &pending_block.header.parent_hash(), changeset)
				.map_err(|e: state_db::Error<io::Error>| client::error::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(&mut transaction, commit);

			// Check if need to finalize. Genesis is always finalized instantly.
			let finalized = number_u64 == 0 || pending_block.leaf_state.is_final();

			let header = &pending_block.header;
			let is_best = pending_block.leaf_state.is_best();
			let changes_trie_updates = operation.changes_trie_updates;

			self.changes_tries_storage.commit(&mut transaction, changes_trie_updates);
			let cache = operation.old_state.release(); // release state reference so that it can be finalized


			if finalized {
				// TODO: ensure best chain contains this block.
				self.ensure_sequential_finalization(header, Some(last_finalized_hash))?;
				self.note_finalized(
					&mut transaction,
					header,
					hash,
					&mut finalization_displaced_leaves,
				)?;
			} else {
				// canonicalize blocks which are old enough, regardless of finality.
				self.force_delayed_canonicalize(&mut transaction, hash, *header.number())?
			}

			debug!(target: "db", "DB Commit {:?} ({}), best = {}", hash, number, is_best);

			let displaced_leaf = {
				let mut leaves = self.blockchain.leaves.write();
				let displaced_leaf = leaves.import(hash, number, parent_hash);
				leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);

				displaced_leaf
			};

			let mut children = children::read_children(&*self.storage.db, columns::META, meta_keys::CHILDREN_PREFIX, parent_hash)?;
			children.push(hash);
			children::write_children(&mut transaction, columns::META, meta_keys::CHILDREN_PREFIX, parent_hash, children);

			meta_updates.push((hash, number, pending_block.leaf_state.is_best(), finalized));

			Some((number, hash, enacted, retracted, displaced_leaf, is_best, cache))
		} else {
			None
		};

		if let Some(set_head) = operation.set_head {
			if let Some(header) = ::client::blockchain::HeaderBackend::header(&self.blockchain, set_head)? {
				let number = header.number();
				let hash = header.hash();

				self.set_head_with_transaction(
					&mut transaction,
					hash.clone(),
					(number.clone(), hash.clone())
				)?;
			} else {
				return Err(client::error::Error::UnknownBlock(format!("Cannot set head {:?}", set_head)))
			}
		}

		let write_result = self.storage.db.write(transaction).map_err(db_err);

		if let Some((number, hash, enacted, retracted, displaced_leaf, is_best, mut cache)) = imported {
			if let Err(e) = write_result {
				let mut leaves = self.blockchain.leaves.write();
				let mut undo = leaves.undo();
				if let Some(displaced_leaf) = displaced_leaf {
					undo.undo_import(displaced_leaf);
				}

				if let Some(finalization_displaced) = finalization_displaced_leaves {
					undo.undo_finalization(finalization_displaced);
				}

				return Err(e)
			}

			cache.sync_cache(
				&enacted,
				&retracted,
				operation.storage_updates,
				operation.child_storage_updates,
				Some(hash),
				Some(number),
				|| is_best,
			);
		}

		for (hash, number, is_best, is_finalized) in meta_updates {
			self.blockchain.update_meta(hash, number, is_best, is_finalized);
		}

		Ok(())
	}


	// write stuff to a transaction after a new block is finalized.
	// this canonicalizes finalized blocks. Fails if called with a block which
	// was not a child of the last finalized block.
	fn note_finalized(
		&self,
		transaction: &mut DBTransaction,
		f_header: &Block::Header,
		f_hash: Block::Hash,
		displaced: &mut Option<FinalizationDisplaced<Block::Hash, NumberFor<Block>>>
	) -> Result<(), client::error::Error> where
		Block: BlockT<Hash=H256>,
	{
		let f_num = f_header.number().clone();

		if self.storage.state_db.best_canonical().map(|c| f_num.saturated_into::<u64>() > c).unwrap_or(true) {
			let parent_hash = f_header.parent_hash().clone();

			let lookup_key = utils::number_and_hash_to_lookup_key(f_num, f_hash.clone());
			transaction.put(columns::META, meta_keys::FINALIZED_BLOCK, &lookup_key);

			let commit = self.storage.state_db.canonicalize_block(&f_hash)
				.map_err(|e: state_db::Error<io::Error>| client::error::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(transaction, commit);

			let changes_trie_config = self.changes_trie_config(parent_hash)?;
			if let Some(changes_trie_config) = changes_trie_config {
				self.changes_tries_storage.prune(&changes_trie_config, transaction, f_hash, f_num);
			}
		}

		let new_displaced = self.blockchain.leaves.write().finalize_height(f_num);
		match displaced {
			x @ &mut None => *x = Some(new_displaced),
			&mut Some(ref mut displaced) => displaced.merge(new_displaced),
		}

		Ok(())
	}
}

fn apply_state_commit(transaction: &mut DBTransaction, commit: state_db::CommitSet<Vec<u8>>) {
	for (key, val) in commit.data.inserted.into_iter() {
		transaction.put(columns::STATE, &key[..], &val);
	}
	for key in commit.data.deleted.into_iter() {
		transaction.delete(columns::STATE, &key[..]);
	}
	for (key, val) in commit.meta.inserted.into_iter() {
		transaction.put(columns::STATE_META, &key[..], &val);
	}
	for key in commit.meta.deleted.into_iter() {
		transaction.delete(columns::STATE_META, &key[..]);
	}
}

impl<Block> client::backend::AuxStore for Backend<Block> where Block: BlockT<Hash=H256> {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> client::error::Result<()> {
		let mut transaction = DBTransaction::new();
		for (k, v) in insert {
			transaction.put(columns::AUX, k, v);
		}
		for k in delete {
			transaction.delete(columns::AUX, k);
		}
		self.storage.db.write(transaction).map_err(db_err)?;
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> Result<Option<Vec<u8>>, client::error::Error> {
		Ok(self.storage.db.get(columns::AUX, key).map(|r| r.map(|v| v.to_vec())).map_err(db_err)?)
	}
}

impl<Block> client::backend::Backend<Block, Blake2Hasher> for Backend<Block> where Block: BlockT<Hash=H256> {
	type BlockImportOperation = BlockImportOperation<Block, Blake2Hasher>;
	type Blockchain = BlockchainDb<Block>;
	type State = CachingState<Blake2Hasher, RefTrackingState<Block>, Block>;
	type ChangesTrieStorage = DbChangesTrieStorage<Block>;

	fn begin_operation(&self) -> Result<Self::BlockImportOperation, client::error::Error> {
		let old_state = self.state_at(BlockId::Hash(Default::default()))?;
		Ok(BlockImportOperation {
			pending_block: None,
			old_state,
			db_updates: PrefixedMemoryDB::default(),
			storage_updates: Default::default(),
			child_storage_updates: Default::default(),
			changes_trie_updates: MemoryDB::default(),
			aux_ops: Vec::new(),
			finalized_blocks: Vec::new(),
			set_head: None,
		})
	}

	fn begin_state_operation(&self, operation: &mut Self::BlockImportOperation, block: BlockId<Block>) -> Result<(), client::error::Error> {
		operation.old_state = self.state_at(block)?;
		Ok(())
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation)
		-> Result<(), client::error::Error>
	{
		match self.try_commit_operation(operation) {
			Ok(_) => {
				self.storage.state_db.apply_pending();
				Ok(())
			},
			e @ Err(_) => {
				self.storage.state_db.revert_pending();
				e
			}
		}
	}

	fn finalize_block(&self, block: BlockId<Block>, justification: Option<Justification>)
		-> Result<(), client::error::Error>
	{
		let mut transaction = DBTransaction::new();
		let hash = self.blockchain.expect_block_hash_from_id(&block)?;
		let header = self.blockchain.expect_header(block)?;
		let mut displaced = None;
		let commit = |displaced| {
			let (hash, number, is_best, is_finalized) = self.finalize_block_with_transaction(
				&mut transaction,
				&hash,
				&header,
				None,
				justification,
				displaced,
			)?;
			self.storage.db.write(transaction).map_err(db_err)?;
			self.blockchain.update_meta(hash, number, is_best, is_finalized);
			Ok(())
		};
		match commit(&mut displaced) {
			Ok(()) => self.storage.state_db.apply_pending(),
			e @ Err(_) => {
				self.storage.state_db.revert_pending();
				if let Some(displaced) = displaced {
					self.blockchain.leaves.write().undo().undo_finalization(displaced);
				}
				return e;
			}
		}
		Ok(())
	}

	fn changes_trie_storage(&self) -> Option<&Self::ChangesTrieStorage> {
		Some(&self.changes_tries_storage)
	}

	fn revert(&self, n: NumberFor<Block>) -> Result<NumberFor<Block>, client::error::Error> {
		let mut best = self.blockchain.info().best_number;
		let finalized = self.blockchain.info().finalized_number;
		let revertible = best - finalized;
		let n = if revertible < n { revertible } else { n };

		for c in 0 .. n.saturated_into::<u64>() {
			if best.is_zero() {
				return Ok(c.saturated_into::<NumberFor<Block>>())
			}
			let mut transaction = DBTransaction::new();
			match self.storage.state_db.revert_one() {
				Some(commit) => {
					apply_state_commit(&mut transaction, commit);
					let removed = self.blockchain.header(BlockId::Number(best))?.ok_or_else(
						|| client::error::Error::UnknownBlock(
							format!("Error reverting to {}. Block hash not found.", best)))?;

					best -= One::one();	// prev block
					let hash = self.blockchain.hash(best)?.ok_or_else(
						|| client::error::Error::UnknownBlock(
							format!("Error reverting to {}. Block hash not found.", best)))?;
					let key = utils::number_and_hash_to_lookup_key(best.clone(), &hash);
					transaction.put(columns::META, meta_keys::BEST_BLOCK, &key);
					transaction.delete(columns::KEY_LOOKUP, removed.hash().as_ref());
					children::remove_children(&mut transaction, columns::META, meta_keys::CHILDREN_PREFIX, hash);
					self.storage.db.write(transaction).map_err(db_err)?;
					self.blockchain.update_meta(hash, best, true, false);
					self.blockchain.leaves.write().revert(removed.hash().clone(), removed.number().clone(), removed.parent_hash().clone());
				}
				None => return Ok(c.saturated_into::<NumberFor<Block>>())
			}
		}
		Ok(n)
	}

	fn blockchain(&self) -> &BlockchainDb<Block> {
		&self.blockchain
	}

	fn used_state_cache_size(&self) -> Option<usize> {
		let used = (*&self.shared_cache).lock().used_storage_cache_size();
		Some(used)
	}

	fn state_at(&self, block: BlockId<Block>) -> Result<Self::State, client::error::Error> {
		use client::blockchain::HeaderBackend as BcHeaderBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				let genesis_storage = DbGenesisStorage::new();
				let root = genesis_storage.0.clone();
				let db_state = DbState::new(Arc::new(genesis_storage), root);
				let state = RefTrackingState::new(db_state, self.storage.clone(), None);
				return Ok(CachingState::new(state, self.shared_cache.clone(), None));
			},
			_ => {}
		}

		match self.blockchain.header(block) {
			Ok(Some(ref hdr)) => {
				let hash = hdr.hash();
				if !self.storage.state_db.is_pruned(&hash, (*hdr.number()).saturated_into::<u64>()) {
					let root = H256::from_slice(hdr.state_root().as_ref());
					let db_state = DbState::new(self.storage.clone(), root);
					let state = RefTrackingState::new(db_state, self.storage.clone(), Some(hash.clone()));
					Ok(CachingState::new(state, self.shared_cache.clone(), Some(hash)))
				} else {
					Err(client::error::Error::UnknownBlock(format!("State already discarded for {:?}", block)))
				}
			},
			Ok(None) => Err(client::error::Error::UnknownBlock(format!("Unknown state for block {:?}", block))),
			Err(e) => Err(e),
		}
	}

	fn have_state_at(&self, hash: &Block::Hash, number: NumberFor<Block>) -> bool {
		!self.storage.state_db.is_pruned(hash, number.saturated_into::<u64>())
	}

	fn destroy_state(&self, state: Self::State) -> Result<(), client::error::Error> {
		if let Some(hash) = state.cache.parent_hash.clone() {
			let is_best = || self.blockchain.meta.read().best_hash == hash;
			state.release().sync_cache(&[], &[], vec![], vec![], None, None, is_best);
		}
		Ok(())
	}

	fn get_import_lock(&self) -> &Mutex<()> {
		&self.import_lock
	}
}

impl<Block> client::backend::LocalBackend<Block, Blake2Hasher> for Backend<Block>
where Block: BlockT<Hash=H256> {}

#[cfg(test)]
mod tests {
	use hash_db::HashDB;
	use super::*;
	use crate::columns;
	use client::backend::Backend as BTrait;
	use client::blockchain::Backend as BLBTrait;
	use client::backend::BlockImportOperation as Op;
	use runtime_primitives::testing::{Header, Block as RawBlock, ExtrinsicWrapper};
	use runtime_primitives::traits::{Hash, BlakeTwo256};
	use state_machine::{TrieMut, TrieDBMut, ChangesTrieRootsStorage, ChangesTrieStorage};
	use test_client;

	type Block = RawBlock<ExtrinsicWrapper<u64>>;

	fn prepare_changes(changes: Vec<(Vec<u8>, Vec<u8>)>) -> (H256, MemoryDB<Blake2Hasher>) {
		let mut changes_root = H256::default();
		let mut changes_trie_update = MemoryDB::<Blake2Hasher>::default();
		{
			let mut trie = TrieDBMut::<Blake2Hasher>::new(
				&mut changes_trie_update,
				&mut changes_root
			);
			for (key, value) in changes {
				trie.insert(&key, &value).unwrap();
			}
		}

		(changes_root, changes_trie_update)
	}

	fn insert_header(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		changes: Vec<(Vec<u8>, Vec<u8>)>,
		extrinsics_root: H256,
	) -> H256 {
		use runtime_primitives::testing::Digest;

		let (changes_root, changes_trie_update) = prepare_changes(changes);
		let digest = Digest {
			logs: vec![
				DigestItem::ChangesTrieRoot(changes_root),
			],
		};
		let header = Header {
			number,
			parent_hash,
			state_root: BlakeTwo256::trie_root::<_, &[u8], &[u8]>(Vec::new()),
			digest,
			extrinsics_root,
		};
		let header_hash = header.hash();

		let block_id = if number == 0 {
			BlockId::Hash(Default::default())
		} else {
			BlockId::Number(number - 1)
		};
		let mut op = backend.begin_operation().unwrap();
		backend.begin_state_operation(&mut op, block_id).unwrap();
		op.set_block_data(header, None, None, NewBlockState::Best).unwrap();
		op.update_changes_trie(changes_trie_update).unwrap();
		backend.commit_operation(op).unwrap();

		header_hash
	}

	#[test]
	fn block_hash_inserted_correctly() {
		let backing = {
			let db = Backend::<Block>::new_test(1, 0);
			for i in 0..10 {
				assert!(db.blockchain().hash(i).unwrap().is_none());

				{
					let id = if i == 0 {
						BlockId::Hash(Default::default())
					} else {
						BlockId::Number(i - 1)
					};

					let mut op = db.begin_operation().unwrap();
					db.begin_state_operation(&mut op, id).unwrap();
					let header = Header {
						number: i,
						parent_hash: if i == 0 {
							Default::default()
						} else {
							db.blockchain.hash(i - 1).unwrap().unwrap()
						},
						state_root: Default::default(),
						digest: Default::default(),
						extrinsics_root: Default::default(),
					};

					op.set_block_data(
						header,
						Some(vec![]),
						None,
						NewBlockState::Best,
					).unwrap();
					db.commit_operation(op).unwrap();
				}

				assert!(db.blockchain().hash(i).unwrap().is_some())
			}
			db.storage.db.clone()
		};

		let backend = Backend::<Block>::new_test_db(1, 0, backing);
		assert_eq!(backend.blockchain().info().best_number, 9);
		for i in 0..10 {
			assert!(backend.blockchain().hash(i).unwrap().is_some())
		}
	}

	#[test]
	fn set_state_data() {
		let db = Backend::<Block>::new_test(2, 0);
		let hash = {
			let mut op = db.begin_operation().unwrap();
			db.begin_state_operation(&mut op, BlockId::Hash(Default::default())).unwrap();
			let mut header = Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![
				(vec![1, 3, 5], vec![2, 4, 6]),
				(vec![1, 2, 3], vec![9, 9, 9]),
			];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();
			let hash = header.hash();

			op.reset_storage(storage.iter().cloned().collect(), Default::default()).unwrap();
			op.set_block_data(
				header.clone(),
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(BlockId::Number(0)).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), Some(vec![2, 4, 6]));
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), None);

			hash
		};

		{
			let mut op = db.begin_operation().unwrap();
			db.begin_state_operation(&mut op, BlockId::Number(0)).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage = vec![
				(vec![1, 3, 5], None),
				(vec![5, 5, 5], Some(vec![4, 5, 6])),
			];

			let (root, overlay) = op.old_state.storage_root(storage.iter().cloned());
			op.update_db_storage(overlay).unwrap();
			header.state_root = root.into();

			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			db.commit_operation(op).unwrap();

			let state = db.state_at(BlockId::Number(1)).unwrap();

			assert_eq!(state.storage(&[1, 3, 5]).unwrap(), None);
			assert_eq!(state.storage(&[1, 2, 3]).unwrap(), Some(vec![9, 9, 9]));
			assert_eq!(state.storage(&[5, 5, 5]).unwrap(), Some(vec![4, 5, 6]));
		}
	}

	#[test]
	fn delete_only_when_negative_rc() {
		let _ = ::env_logger::try_init();
		let key;
		let backend = Backend::<Block>::new_test(1, 0);

		let hash = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(Default::default())).unwrap();
			let mut header = Header {
				number: 0,
				parent_hash: Default::default(),
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();
			let hash = header.hash();

			op.reset_storage(storage.iter().cloned().collect(), Default::default()).unwrap();

			key = op.db_updates.insert(&[], b"hello");
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert_eq!(backend.storage.db.get(columns::STATE, key.as_bytes()).unwrap().unwrap(), &b"hello"[..]);
			hash
		};

		let hash = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Number(0)).unwrap();
			let mut header = Header {
				number: 1,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();
			let hash = header.hash();

			op.db_updates.insert(&[], b"hello");
			op.db_updates.remove(&key, &[]);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert_eq!(backend.storage.db.get(columns::STATE, key.as_bytes()).unwrap().unwrap(), &b"hello"[..]);
			hash
		};

		let hash = {
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Number(1)).unwrap();
			let mut header = Header {
				number: 2,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();
			let hash = header.hash();

			op.db_updates.remove(&key, &[]);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert!(backend.storage.db.get(columns::STATE, key.as_bytes()).unwrap().is_some());
			hash
		};

		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Number(2)).unwrap();
			let mut header = Header {
				number: 3,
				parent_hash: hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			};

			let storage: Vec<(_, _)> = vec![];

			header.state_root = op.old_state.storage_root(storage
				.iter()
				.cloned()
				.map(|(x, y)| (x, Some(y)))
			).0.into();

			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert!(backend.storage.db.get(columns::STATE, key.as_bytes()).unwrap().is_none());
		}

		backend.finalize_block(BlockId::Number(1), None).unwrap();
		backend.finalize_block(BlockId::Number(2), None).unwrap();
		backend.finalize_block(BlockId::Number(3), None).unwrap();
		assert!(backend.storage.db.get(columns::STATE, key.as_bytes()).unwrap().is_none());
	}

	#[test]
	fn changes_trie_storage_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		backend.changes_tries_storage.meta.write().finalized_number = 1000;


		let check_changes = |backend: &Backend<Block>, block: u64, changes: Vec<(Vec<u8>, Vec<u8>)>| {
			let (changes_root, mut changes_trie_update) = prepare_changes(changes);
			let anchor = state_machine::ChangesTrieAnchorBlockId {
				hash: backend.blockchain().header(BlockId::Number(block)).unwrap().unwrap().hash(),
				number: block
			};
			assert_eq!(backend.changes_tries_storage.root(&anchor, block), Ok(Some(changes_root)));

			for (key, (val, _)) in changes_trie_update.drain() {
				assert_eq!(backend.changes_trie_storage().unwrap().get(&key, &[]), Ok(Some(val)));
			}
		};

		let changes0 = vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())];
		let changes1 = vec![
			(b"key_at_1".to_vec(), b"val_at_1".to_vec()),
			(b"another_key_at_1".to_vec(), b"another_val_at_1".to_vec()),
		];
		let changes2 = vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())];

		let block0 = insert_header(&backend, 0, Default::default(), changes0.clone(), Default::default());
		let block1 = insert_header(&backend, 1, block0, changes1.clone(), Default::default());
		let _ = insert_header(&backend, 2, block1, changes2.clone(), Default::default());

		// check that the storage contains tries for all blocks
		check_changes(&backend, 0, changes0);
		check_changes(&backend, 1, changes1);
		check_changes(&backend, 2, changes2);
	}

	#[test]
	fn changes_trie_storage_works_with_forks() {
		let backend = Backend::<Block>::new_test(1000, 100);

		let changes0 = vec![(b"k0".to_vec(), b"v0".to_vec())];
		let changes1 = vec![(b"k1".to_vec(), b"v1".to_vec())];
		let changes2 = vec![(b"k2".to_vec(), b"v2".to_vec())];
		let block0 = insert_header(&backend, 0, Default::default(), changes0.clone(), Default::default());
		let block1 = insert_header(&backend, 1, block0, changes1.clone(), Default::default());
		let block2 = insert_header(&backend, 2, block1, changes2.clone(), Default::default());

		let changes2_1_0 = vec![(b"k3".to_vec(), b"v3".to_vec())];
		let changes2_1_1 = vec![(b"k4".to_vec(), b"v4".to_vec())];
		let block2_1_0 = insert_header(&backend, 3, block2, changes2_1_0.clone(), Default::default());
		let block2_1_1 = insert_header(&backend, 4, block2_1_0, changes2_1_1.clone(), Default::default());

		let changes2_2_0 = vec![(b"k5".to_vec(), b"v5".to_vec())];
		let changes2_2_1 = vec![(b"k6".to_vec(), b"v6".to_vec())];
		let block2_2_0 = insert_header(&backend, 3, block2, changes2_2_0.clone(), Default::default());
		let block2_2_1 = insert_header(&backend, 4, block2_2_0, changes2_2_1.clone(), Default::default());

		// finalize block1
		backend.changes_tries_storage.meta.write().finalized_number = 1;

		// branch1: when asking for finalized block hash
		let (changes1_root, _) = prepare_changes(changes1);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1), Ok(Some(changes1_root)));

		// branch2: when asking for finalized block hash
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_2_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 1), Ok(Some(changes1_root)));

		// branch1: when asking for non-finalized block hash (search by traversal)
		let (changes2_1_0_root, _) = prepare_changes(changes2_1_0);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_1_0_root)));

		// branch2: when asking for non-finalized block hash (search using canonicalized hint)
		let (changes2_2_0_root, _) = prepare_changes(changes2_2_0);
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_2_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));

		// finalize first block of branch2 (block2_2_0)
		backend.changes_tries_storage.meta.write().finalized_number = 3;

		// branch2: when asking for finalized block of this branch
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));

		// branch1: when asking for finalized block of other branch
		// => result is incorrect (returned for the block of branch1), but this is expected,
		// because the other fork is abandoned (forked before finalized header)
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block2_1_1, number: 4 };
		assert_eq!(backend.changes_tries_storage.root(&anchor, 3), Ok(Some(changes2_2_0_root)));
	}

	#[test]
	fn changes_tries_with_digest_are_pruned_on_finalization() {
		let mut backend = Backend::<Block>::new_test(1000, 100);
		backend.changes_tries_storage.min_blocks_to_keep = Some(8);
		let config = ChangesTrieConfiguration {
			digest_interval: 2,
			digest_levels: 2,
		};

		// insert some blocks
		let block0 = insert_header(&backend, 0, Default::default(), vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())], Default::default());
		let block1 = insert_header(&backend, 1, block0, vec![(b"key_at_1".to_vec(), b"val_at_1".to_vec())], Default::default());
		let block2 = insert_header(&backend, 2, block1, vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())], Default::default());
		let block3 = insert_header(&backend, 3, block2, vec![(b"key_at_3".to_vec(), b"val_at_3".to_vec())], Default::default());
		let block4 = insert_header(&backend, 4, block3, vec![(b"key_at_4".to_vec(), b"val_at_4".to_vec())], Default::default());
		let block5 = insert_header(&backend, 5, block4, vec![(b"key_at_5".to_vec(), b"val_at_5".to_vec())], Default::default());
		let block6 = insert_header(&backend, 6, block5, vec![(b"key_at_6".to_vec(), b"val_at_6".to_vec())], Default::default());
		let block7 = insert_header(&backend, 7, block6, vec![(b"key_at_7".to_vec(), b"val_at_7".to_vec())], Default::default());
		let block8 = insert_header(&backend, 8, block7, vec![(b"key_at_8".to_vec(), b"val_at_8".to_vec())], Default::default());
		let block9 = insert_header(&backend, 9, block8, vec![(b"key_at_9".to_vec(), b"val_at_9".to_vec())], Default::default());
		let block10 = insert_header(&backend, 10, block9, vec![(b"key_at_10".to_vec(), b"val_at_10".to_vec())], Default::default());
		let block11 = insert_header(&backend, 11, block10, vec![(b"key_at_11".to_vec(), b"val_at_11".to_vec())], Default::default());
		let block12 = insert_header(&backend, 12, block11, vec![(b"key_at_12".to_vec(), b"val_at_12".to_vec())], Default::default());
		let block13 = insert_header(&backend, 13, block12, vec![(b"key_at_13".to_vec(), b"val_at_13".to_vec())], Default::default());
		backend.changes_tries_storage.meta.write().finalized_number = 13;

		// check that roots of all tries are in the columns::CHANGES_TRIE
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block13, number: 13 };
		fn read_changes_trie_root(backend: &Backend<Block>, num: u64) -> H256 {
			backend.blockchain().header(BlockId::Number(num)).unwrap().unwrap().digest().logs().iter()
				.find(|i| i.as_changes_trie_root().is_some()).unwrap().as_changes_trie_root().unwrap().clone()
		}
		let root1 = read_changes_trie_root(&backend, 1); assert_eq!(backend.changes_tries_storage.root(&anchor, 1).unwrap(), Some(root1));
		let root2 = read_changes_trie_root(&backend, 2); assert_eq!(backend.changes_tries_storage.root(&anchor, 2).unwrap(), Some(root2));
		let root3 = read_changes_trie_root(&backend, 3); assert_eq!(backend.changes_tries_storage.root(&anchor, 3).unwrap(), Some(root3));
		let root4 = read_changes_trie_root(&backend, 4); assert_eq!(backend.changes_tries_storage.root(&anchor, 4).unwrap(), Some(root4));
		let root5 = read_changes_trie_root(&backend, 5); assert_eq!(backend.changes_tries_storage.root(&anchor, 5).unwrap(), Some(root5));
		let root6 = read_changes_trie_root(&backend, 6); assert_eq!(backend.changes_tries_storage.root(&anchor, 6).unwrap(), Some(root6));
		let root7 = read_changes_trie_root(&backend, 7); assert_eq!(backend.changes_tries_storage.root(&anchor, 7).unwrap(), Some(root7));
		let root8 = read_changes_trie_root(&backend, 8); assert_eq!(backend.changes_tries_storage.root(&anchor, 8).unwrap(), Some(root8));
		let root9 = read_changes_trie_root(&backend, 9); assert_eq!(backend.changes_tries_storage.root(&anchor, 9).unwrap(), Some(root9));
		let root10 = read_changes_trie_root(&backend, 10); assert_eq!(backend.changes_tries_storage.root(&anchor, 10).unwrap(), Some(root10));
		let root11 = read_changes_trie_root(&backend, 11); assert_eq!(backend.changes_tries_storage.root(&anchor, 11).unwrap(), Some(root11));
		let root12 = read_changes_trie_root(&backend, 12); assert_eq!(backend.changes_tries_storage.root(&anchor, 12).unwrap(), Some(root12));

		// now simulate finalization of block#12, causing prune of tries at #1..#4
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&config, &mut tx, Default::default(), 12);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root1, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root3, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root4, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root5, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root6, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root7, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root8, &[]).unwrap().is_some());

		// now simulate finalization of block#16, causing prune of tries at #5..#8
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&config, &mut tx, Default::default(), 16);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root5, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root6, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root7, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root8, &[]).unwrap().is_none());

		// now "change" pruning mode to archive && simulate finalization of block#20
		// => no changes tries are pruned, because we never prune in archive mode
		backend.changes_tries_storage.min_blocks_to_keep = None;
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&config, &mut tx, Default::default(), 20);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root9, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root10, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root11, &[]).unwrap().is_some());
		assert!(backend.changes_tries_storage.get(&root12, &[]).unwrap().is_some());
	}

	#[test]
	fn changes_tries_without_digest_are_pruned_on_finalization() {
		let mut backend = Backend::<Block>::new_test(1000, 100);
		backend.changes_tries_storage.min_blocks_to_keep = Some(4);
		let config = ChangesTrieConfiguration {
			digest_interval: 0,
			digest_levels: 0,
		};

		// insert some blocks
		let block0 = insert_header(&backend, 0, Default::default(), vec![(b"key_at_0".to_vec(), b"val_at_0".to_vec())], Default::default());
		let block1 = insert_header(&backend, 1, block0, vec![(b"key_at_1".to_vec(), b"val_at_1".to_vec())], Default::default());
		let block2 = insert_header(&backend, 2, block1, vec![(b"key_at_2".to_vec(), b"val_at_2".to_vec())], Default::default());
		let block3 = insert_header(&backend, 3, block2, vec![(b"key_at_3".to_vec(), b"val_at_3".to_vec())], Default::default());
		let block4 = insert_header(&backend, 4, block3, vec![(b"key_at_4".to_vec(), b"val_at_4".to_vec())], Default::default());
		let block5 = insert_header(&backend, 5, block4, vec![(b"key_at_5".to_vec(), b"val_at_5".to_vec())], Default::default());
		let block6 = insert_header(&backend, 6, block5, vec![(b"key_at_6".to_vec(), b"val_at_6".to_vec())], Default::default());

		// check that roots of all tries are in the columns::CHANGES_TRIE
		let anchor = state_machine::ChangesTrieAnchorBlockId { hash: block6, number: 6 };
		fn read_changes_trie_root(backend: &Backend<Block>, num: u64) -> H256 {
			backend.blockchain().header(BlockId::Number(num)).unwrap().unwrap().digest().logs().iter()
				.find(|i| i.as_changes_trie_root().is_some()).unwrap().as_changes_trie_root().unwrap().clone()
		}

		let root1 = read_changes_trie_root(&backend, 1); assert_eq!(backend.changes_tries_storage.root(&anchor, 1).unwrap(), Some(root1));
		let root2 = read_changes_trie_root(&backend, 2); assert_eq!(backend.changes_tries_storage.root(&anchor, 2).unwrap(), Some(root2));
		let root3 = read_changes_trie_root(&backend, 3); assert_eq!(backend.changes_tries_storage.root(&anchor, 3).unwrap(), Some(root3));
		let root4 = read_changes_trie_root(&backend, 4); assert_eq!(backend.changes_tries_storage.root(&anchor, 4).unwrap(), Some(root4));
		let root5 = read_changes_trie_root(&backend, 5); assert_eq!(backend.changes_tries_storage.root(&anchor, 5).unwrap(), Some(root5));
		let root6 = read_changes_trie_root(&backend, 6); assert_eq!(backend.changes_tries_storage.root(&anchor, 6).unwrap(), Some(root6));

		// now simulate finalization of block#5, causing prune of trie at #1
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&config, &mut tx, block5, 5);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root1, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_some());

		// now simulate finalization of block#6, causing prune of tries at #2
		let mut tx = DBTransaction::new();
		backend.changes_tries_storage.prune(&config, &mut tx, block6, 6);
		backend.storage.db.write(tx).unwrap();
		assert!(backend.changes_tries_storage.get(&root2, &[]).unwrap().is_none());
		assert!(backend.changes_tries_storage.get(&root3, &[]).unwrap().is_some());
	}

	#[test]
	fn tree_route_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let block0 = insert_header(&backend, 0, Default::default(), Vec::new(), Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, Vec::new(), Default::default());
		let a2 = insert_header(&backend, 2, a1, Vec::new(), Default::default());
		let a3 = insert_header(&backend, 3, a2, Vec::new(), Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, Vec::new(), H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, Vec::new(), Default::default());

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a3),
				BlockId::Hash(b2)
			).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2, a1]);
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![b1, b2]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a1),
				BlockId::Hash(a3),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a2, a3]);
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a3),
				BlockId::Hash(a1),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2]);
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(a2),
				BlockId::Hash(a2),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, a2);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}
	}

	#[test]
	fn tree_route_child() {
		let backend = Backend::<Block>::new_test(1000, 100);

		let block0 = insert_header(&backend, 0, Default::default(), Vec::new(), Default::default());
		let block1 = insert_header(&backend, 1, block0, Vec::new(), Default::default());

		{
			let tree_route = ::client::blockchain::tree_route(
				backend.blockchain(),
				BlockId::Hash(block0),
				BlockId::Hash(block1),
			).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![block1]);
		}
	}

	#[test]
	fn test_leaves_with_complex_block_tree() {
		let backend: Arc<Backend<test_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		test_client::trait_tests::test_leaves_for_backend(backend);
	}

	#[test]
	fn test_children_with_complex_block_tree() {
		let backend: Arc<Backend<test_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		test_client::trait_tests::test_children_for_backend(backend);
	}

	#[test]
	fn test_blockchain_query_by_number_gets_canonical() {
		let backend: Arc<Backend<test_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		test_client::trait_tests::test_blockchain_query_by_number_gets_canonical(backend);
	}

	#[test]
	fn test_leaves_pruned_on_finality() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), Default::default(), Default::default());

		let block1_a = insert_header(&backend, 1, block0, Default::default(), Default::default());
		let block1_b = insert_header(&backend, 1, block0, Default::default(), [1; 32].into());
		let block1_c = insert_header(&backend, 1, block0, Default::default(), [2; 32].into());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block1_a, block1_b, block1_c]);

		let block2_a = insert_header(&backend, 2, block1_a, Default::default(), Default::default());
		let block2_b = insert_header(&backend, 2, block1_b, Default::default(), Default::default());
		let block2_c = insert_header(&backend, 2, block1_b, Default::default(), [1; 32].into());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a, block2_b, block2_c, block1_c]);

		backend.finalize_block(BlockId::hash(block1_a), None).unwrap();
		backend.finalize_block(BlockId::hash(block2_a), None).unwrap();

		// leaves at same height stay. Leaves at lower heights pruned.
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a, block2_b, block2_c]);
	}

	#[test]
	fn test_aux() {
		let backend: Backend<test_client::runtime::Block> = Backend::new_test(0, 0);
		assert!(backend.get_aux(b"test").unwrap().is_none());
		backend.insert_aux(&[(&b"test"[..], &b"hello"[..])], &[]).unwrap();
		assert_eq!(b"hello", &backend.get_aux(b"test").unwrap().unwrap()[..]);
		backend.insert_aux(&[], &[&b"test"[..]]).unwrap();
		assert!(backend.get_aux(b"test").unwrap().is_none());
	}

	#[test]
	fn test_finalize_block_with_justification() {
		use client::blockchain::{Backend as BlockChainBackend};

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), Default::default(), Default::default());
		let _ = insert_header(&backend, 1, block0, Default::default(), Default::default());

		let justification = Some(vec![1, 2, 3]);
		backend.finalize_block(BlockId::Number(1), justification.clone()).unwrap();

		assert_eq!(
			backend.blockchain().justification(BlockId::Number(1)).unwrap(),
			justification,
		);
	}

	#[test]
	fn test_finalize_multiple_blocks_in_single_op() {
		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), Default::default(), Default::default());
		let block1 = insert_header(&backend, 1, block0, Default::default(), Default::default());
		let block2 = insert_header(&backend, 2, block1, Default::default(), Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(block0)).unwrap();
			op.mark_finalized(BlockId::Hash(block1), None).unwrap();
			op.mark_finalized(BlockId::Hash(block2), None).unwrap();
			backend.commit_operation(op).unwrap();
		}
	}

	#[test]
	fn test_finalize_non_sequential() {
		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), Default::default(), Default::default());
		let block1 = insert_header(&backend, 1, block0, Default::default(), Default::default());
		let block2 = insert_header(&backend, 2, block1, Default::default(), Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(block0)).unwrap();
			op.mark_finalized(BlockId::Hash(block2), None).unwrap();
			backend.commit_operation(op).unwrap_err();
		}
	}
}
