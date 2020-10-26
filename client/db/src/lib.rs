// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Client backend that is backed by a database.
//!
//! # Canonicality vs. Finality
//!
//! Finality indicates that a block will not be reverted, according to the consensus algorithm,
//! while canonicality indicates that the block may be reverted, but we will be unable to do so,
//! having discarded heavy state that will allow a chain reorganization.
//!
//! Finality implies canonicality but not vice-versa.

#![warn(missing_docs)]

pub mod light;
pub mod offchain;

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
pub mod bench;

mod children;
mod cache;
mod changes_tries_storage;
mod storage_cache;
#[cfg(any(feature = "with-kvdb-rocksdb", test))]
mod upgrade;
mod utils;
mod stats;
#[cfg(feature = "with-parity-db")]
mod parity_db;

use historied_db::{
	Management, ForkableManagement, DecodeWithContext,
	historied::Value,
	simple_db::TransactionalSerializeDB,
	backend::nodes::ContextHead,
};

use std::sync::Arc;
use std::path::{Path, PathBuf};
use std::io;
use std::collections::{HashMap, HashSet};
use offchain::{BlockNodes, BranchNodes};

use sc_client_api::{
	UsageInfo, MemoryInfo, IoInfo, MemorySize,
	backend::{NewBlockState, PrunableStateChangesTrieStorage, ProvideChtRoots},
	leaves::{LeafSet, FinalizationDisplaced}, cht,
};
use sp_blockchain::{
	Result as ClientResult, Error as ClientError,
	well_known_cache_keys, HeaderBackend,
};
use codec::{Decode, Encode};
use hash_db::Prefix;
use sp_trie::{MemoryDB, PrefixedMemoryDB, prefixed_key};
use sp_database::{Transaction, RadixTreeDatabase};
use parking_lot::RwLock;
use sp_core::{ChangesTrieConfiguration, Hasher};
use sp_core::offchain::storage::{OffchainOverlayedChange, OffchainOverlayedChanges};
use sp_core::storage::{well_known_keys, ChildInfo};
use sp_arithmetic::traits::Saturating;
use sp_runtime::{generic::{DigestItem, BlockId}, Justification, Storage};
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, One, SaturatedConversion, HashFor,
};
use sp_state_machine::{
	DBValue, ChangesTrieTransaction, ChangesTrieCacheAction, UsageInfo as StateUsageInfo,
	StorageCollection, ChildStorageCollection,
	backend::Backend as StateBackend, StateMachineStats,
};
use crate::utils::{DatabaseType, Meta, meta_keys, read_db, read_meta};
use crate::changes_tries_storage::{DbChangesTrieStorage, DbChangesTrieStorageTransaction};
use sc_state_db::StateDb;
use sp_blockchain::{CachedHeaderMetadata, HeaderMetadata, HeaderMetadataCache};
use crate::storage_cache::{CachingState, SyncingCachingState, SharedCache, new_shared_cache};
use crate::stats::StateUsageStats;
use log::{trace, debug, warn};

// Re-export the Database trait so that one can pass an implementation of it.
pub use sp_database::Database;
pub use sc_state_db::PruningMode;

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
pub use bench::BenchmarkingState;

const MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR: u32 = 32768;

/// Default value for storage cache child ratio.
const DEFAULT_CHILD_RATIO: (usize, usize) = (1, 10);

/// DB-backed patricia trie state, transaction type is an overlay of changes to commit.
pub type DbState<B> = sp_state_machine::TrieBackend<
	Arc<dyn sp_state_machine::Storage<HashFor<B>>>, HashFor<B>
>;

/// Key value db change for at a given block of an historied DB.
pub struct HistoriedDBMut {
	/// Branch head indexes to change values of a latest block.
	pub current_state: historied_db::Latest<(u32, u64)>,
	/// Inner database to modify historied values.
	pub db: Arc<dyn Database<DbHash>>,
}

impl HistoriedDBMut {
	/// Create a transaction for this historied db.
	pub fn transaction(&self) -> Transaction<DbHash> {
		Transaction::new()
	}

	/// Update transaction for a offchain local storage historied value.
	pub fn update_single_offchain(
		&mut self,
		k: &[u8],
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
		branch_nodes: &BranchNodes,
		block_nodes: &BlockNodes,
	) {
		use crate::offchain::HValue;
		let column = crate::columns::OFFCHAIN;
		let init_nodes = ContextHead {
			key: k.to_vec(),
			backend: block_nodes.clone(),
			node_init_from: (),
		};
		let init = ContextHead {
			key: k.to_vec(),
			backend: branch_nodes.clone(),
			node_init_from: init_nodes.clone(),
		};

		let histo = if let Some(histo) = self.db.get(column, k) {
			Some(HValue::decode_with_context(&mut &histo[..], &(init.clone(), init_nodes.clone()))
				.expect("Bad encoded value in db, closing"))
		} else {
			if change.is_none() {
				return;
			}
			None
		};

		let mut new_value;
		match if let Some(histo) = histo {
			new_value = histo;
			new_value.set(change, &self.current_state)
		} else {
			new_value = HValue::new(change, &self.current_state, (init, init_nodes));
			historied_db::UpdateResult::Changed(())
		} {
			historied_db::UpdateResult::Changed(()) => {
				use historied_db::Trigger;
				new_value.trigger_flush();
				change_set.set_from_vec(column, k, new_value.encode());
			},
			historied_db::UpdateResult::Cleared(()) => {
				use historied_db::Trigger;
				new_value.trigger_flush();
				change_set.remove(column, k);
			},
			historied_db::UpdateResult::Unchanged => (),
		}
	}
}

const DB_HASH_LEN: usize = 32;

/// Hash type that this backend uses for the database.
pub type DbHash = [u8; DB_HASH_LEN];

/// A reference tracking state.
///
/// It makes sure that the hash we are using stays pinned in storage
/// until this structure is dropped.
pub struct RefTrackingState<Block: BlockT> {
	state: DbState<Block>,
	storage: Arc<StorageDb<Block>>,
	parent_hash: Option<Block::Hash>,
}

impl<B: BlockT> RefTrackingState<B> {
	fn new(state: DbState<B>, storage: Arc<StorageDb<B>>, parent_hash: Option<B::Hash>) -> Self {
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

impl<Block: BlockT> std::fmt::Debug for RefTrackingState<Block> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Block {:?}", self.parent_hash)
	}
}

impl<B: BlockT> StateBackend<HashFor<B>> for RefTrackingState<B> {
	type Error =  <DbState<B> as StateBackend<HashFor<B>>>::Error;
	type Transaction = <DbState<B> as StateBackend<HashFor<B>>>::Transaction;
	type TrieBackendStorage = <DbState<B> as StateBackend<HashFor<B>>>::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.storage(key)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.state.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.child_storage(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(child_info, key)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_key_values_with_prefix(prefix, f)
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		f: F,
	) {
		self.state.for_keys_in_child_storage(child_info, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.state.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, Self::Transaction) where B::Hash: Ord {
		self.state.storage_root(delta)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item=(&'a [u8], Option<&'a [u8]>)>,
	) -> (B::Hash, bool, Self::Transaction) where B::Hash: Ord {
		self.state.child_storage_root(child_info, delta)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
	) -> Vec<Vec<u8>> {
		self.state.child_keys(child_info, prefix)
	}

	fn as_trie_backend(&mut self)
		-> Option<&sp_state_machine::TrieBackend<Self::TrieBackendStorage, HashFor<B>>>
	{
		self.state.as_trie_backend()
	}

	fn register_overlay_stats(&mut self, stats: &StateMachineStats) {
		self.state.register_overlay_stats(stats);
	}

	fn usage_info(&self) -> StateUsageInfo {
		self.state.usage_info()
	}
}

/// Database settings.
pub struct DatabaseSettings {
	/// State cache size.
	pub state_cache_size: usize,
	/// Ratio of cache size dedicated to child tries.
	pub state_cache_child_ratio: Option<(usize, usize)>,
	/// Pruning mode.
	pub pruning: PruningMode,
	/// Where to find the database.
	pub source: DatabaseSettingsSrc,
}

/// Where to find the database..
#[derive(Debug, Clone)]
pub enum DatabaseSettingsSrc {
	/// Load a RocksDB database from a given path. Recommended for most uses.
	RocksDb {
		/// Path to the database.
		path: PathBuf,
		/// Cache size in MiB.
		cache_size: usize,
	},

	/// Load a ParityDb database from a given path.
	ParityDb {
		/// Path to the database.
		path: PathBuf,
	},

	/// Use a custom already-open database.
	Custom(Arc<dyn Database<DbHash>>),
}

impl DatabaseSettingsSrc {
	/// Return dabase path for databases that are on the disk.
	pub fn path(&self) -> Option<&Path> {
		match self {
			DatabaseSettingsSrc::RocksDb { path, .. } => Some(path.as_path()),
			DatabaseSettingsSrc::ParityDb { path, .. } => Some(path.as_path()),
			DatabaseSettingsSrc::Custom(_) => None,
		}
	}
	/// Check if database supports internal ref counting for state data.
	pub fn supports_ref_counting(&self) -> bool {
		match self {
			DatabaseSettingsSrc::ParityDb { .. } => true,
			_ => false,
		}
	}
}

impl std::fmt::Display for DatabaseSettingsSrc {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let name = match self {
			DatabaseSettingsSrc::RocksDb { .. } => "RocksDb",
			DatabaseSettingsSrc::ParityDb { .. } => "ParityDb",
			DatabaseSettingsSrc::Custom(_) => "Custom",
		};
		write!(f, "{}", name)
	}
}

pub(crate) mod columns {
	pub const META: u32 = crate::utils::COLUMN_META;
	pub const STATE: u32 = 1;
	pub const STATE_META: u32 = 2;
	/// maps hashes to lookup keys and numbers to canon hashes.
	pub const KEY_LOOKUP: u32 = 3;
	pub const HEADER: u32 = 4;
	pub const BODY: u32 = 5;
	pub const JUSTIFICATION: u32 = 6;
	pub const CHANGES_TRIE: u32 = 7;
	pub const AUX: u32 = 8;
	/// Offchain workers local storage
	pub const OFFCHAIN: u32 = 9;
	pub const CACHE: u32 = 10;
}

#[derive(Clone)]
/// Database backed tree management.
///
/// Definitions for storage of historied
/// db tree state (maps block hashes to internal
/// history index).
pub struct TreeManagementPersistence;

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
/// Database backed tree management for a rocksdb database.
pub struct RocksdbStorage(Arc<kvdb_rocksdb::Database>);

/// Database backed tree management for an unordered database.
///
/// This internaly use radix tree to index nodes.
pub struct DatabaseStorage<H: Clone + PartialEq + std::fmt::Debug>(RadixTreeDatabase<H>);

impl historied_db::management::tree::TreeManagementStorage for TreeManagementPersistence {
	const JOURNAL_DELETE: bool = true;
	// Use pointer to serialize db with a transactional layer.
	type Storage = TransactionalSerializeDB<historied_db::simple_db::SerializeDBDyn>;
	type Mapping = historied_tree_bindings::Mapping;
	type JournalDelete = historied_tree_bindings::JournalDelete;
	type TouchedGC = historied_tree_bindings::TouchedGC;
	type CurrentGC = historied_tree_bindings::CurrentGC;
	type LastIndex = historied_tree_bindings::LastIndex;
	type NeutralElt = historied_tree_bindings::NeutralElt;
	type TreeMeta = historied_tree_bindings::TreeMeta;
	type TreeState = historied_tree_bindings::TreeState;
}

macro_rules! subcollection_prefixed_key {
	($prefix: ident, $key: ident) => {
		let mut prefixed_key;
		let $key = if let Some(k) = $prefix {
			prefixed_key = Vec::with_capacity(k.len() + $key.len());
			prefixed_key.extend_from_slice(&k[..]);
			prefixed_key.extend_from_slice(&$key[..]);
			&prefixed_key[..]
		} else {
			&$key[..]
		};
	}
}

/// We resolve rocksdb collection or subcollection.
/// Collections are defined by four byte encoding of their index.
/// Subcollection are located into the collection defined by four first byte,
/// and behind a prefixed location (remaining bytes).
/// Note that subcollection should define their prefix in a way that no key
/// collision happen.
pub fn resolve_collection<'a>(c: &'a [u8]) -> Option<(u32, Option<&'a [u8]>)> {
	if c.len() < 4 {
		return None;
	}
	let index = resolve_collection_inner(&c[..4]);
	let prefix = if c.len() == 4 {
		None
	} else {
		Some(&c[4..])
	};
	if index < crate::utils::NUM_COLUMNS {
		return Some((index, prefix));
	}
	None
}
const fn resolve_collection_inner<'a>(c: &'a [u8]) -> u32 {
	let mut buf = [0u8; 4];
	buf[0] = c[0];
	buf[1] = c[1];
	buf[2] = c[2];
	buf[3] = c[3];
	u32::from_le_bytes(buf)
}

#[cfg(any(feature = "with-kvdb-rocksdb", test))]
impl historied_db::simple_db::SerializeDB for RocksdbStorage {
	#[inline(always)]
	fn is_active(&self) -> bool {
		true
	}

	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
		resolve_collection(c).map(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			let mut tx = self.0.transaction();
			tx.put(c, k, v);
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn remove(&mut self, c: &'static [u8], k: &[u8]) {
		resolve_collection(c).map(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			let mut tx = self.0.transaction();
			tx.delete(c, k);
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn clear(&mut self, c: &'static [u8]) {
		resolve_collection(c).map(|(c, p)| {
			let mut tx = self.0.transaction();
			tx.delete_prefix(c, p.unwrap_or(&[]));
			self.0.write(tx)
				.expect("Unsupported serialize error")
		});
	}

	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
		resolve_collection(c).and_then(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			self.0.get(c, k)
				.expect("Unsupported readdb error")
		})
	}

	fn iter<'a>(&'a self, c: &'static [u8]) -> historied_db::simple_db::SerializeDBIter<'a> {
		let iter = resolve_collection(c).map(|(c, p)| {
			use kvdb::KeyValueDB;
			if let Some(p) = p {
				self.0.iter_with_prefix(c, p)
			} else {
				<kvdb_rocksdb::Database as KeyValueDB>::iter(&*self.0, c)
			}.map(|(k, v)| (Vec::<u8>::from(k), Vec::<u8>::from(v)))
		}).into_iter().flat_map(|i| i);

		Box::new(iter)
	}

	fn contains_collection(&self, collection: &'static [u8]) -> bool {
		resolve_collection(collection).is_some()
	}
}

impl<H> historied_db::simple_db::SerializeDB for DatabaseStorage<H>
	where H: Clone + PartialEq + std::fmt::Debug + Default + 'static,
{
	#[inline(always)]
	fn is_active(&self) -> bool {
		true
	}

	fn write(&mut self, c: &'static [u8], k: &[u8], v: &[u8]) {
		resolve_collection(c).map(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			self.0.set(c, k, v)
				.expect("Unsupported database error");
		});
	}

	fn remove(&mut self, c: &'static [u8], k: &[u8]) {
		resolve_collection(c).map(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			self.0.remove(c, k)
				.expect("Unsupported database error");
		});
	}

	fn clear(&mut self, c: &'static [u8]) {
		// Inefficient implementation.
		let keys: Vec<Vec<u8>> = self.iter(c).map(|kv| kv.0).collect();
		for key in keys {
			self.remove(c, key.as_slice());
		}
	}

	fn read(&self, c: &'static [u8], k: &[u8]) -> Option<Vec<u8>> {
		resolve_collection(c).and_then(|(c, p)| {
			subcollection_prefixed_key!(p, k);
			self.0.get(c, k)
		})
	}

	fn iter<'a>(&'a self, c: &'static [u8]) -> historied_db::simple_db::SerializeDBIter<'a> {
		let iter = resolve_collection(c).map(|(c, p)| {
			if let Some(p) = p {
				self.0.prefix_iter(c, p, true)
			} else {
				self.0.iter(c)
			}
		}).into_iter().flat_map(|i| i);

		Box::new(iter)
	}

	fn contains_collection(&self, collection: &'static [u8]) -> bool {
		resolve_collection(collection).is_some()
	}
}

/// Trait for serializing historied db tree management.
pub mod historied_tree_bindings {
	macro_rules! static_instance {
		($name: ident, $col: expr) => {

		/// Simple db map or instance definition for $name.
		#[derive(Default, Clone)]
		pub struct $name;
		impl historied_db::simple_db::SerializeInstanceMap for $name {
			const STATIC_COL: &'static [u8] = $col;
		}
	}}
	macro_rules! static_instance_variable {
		($name: ident, $col: expr, $path: expr, $lazy: expr) => {
			static_instance!($name, $col);
		impl historied_db::simple_db::SerializeInstanceVariable for $name {
			const PATH: &'static [u8] = $path;
			const LAZY: bool = $lazy;
		}
	}}
	static_instance!(Mapping, b"\x08\x00\x00\x00tree_mgmt/mapping");
	static_instance!(TreeState, b"\x08\x00\x00\x00tree_mgmt/state");
	static_instance!(JournalDelete, b"\x08\x00\x00\x00tree_mgmt/journal_delete");
	const CST: &'static[u8] = &[8u8, 0, 0, 0]; // AUX collection
	static_instance_variable!(TouchedGC, CST, b"tree_mgmt/touched_gc", false);
	static_instance_variable!(CurrentGC, CST, b"tree_mgmt/current_gc", false);
	static_instance_variable!(LastIndex, CST, b"tree_mgmt/last_index", false);
	static_instance_variable!(NeutralElt,CST, b"tree_mgmt/neutral_elt", false);
	static_instance_variable!(TreeMeta, CST, b"tree_mgmt/tree_meta", true);
	static_instance!(LocalOffchainDelete, b"\x08\x00\x00\x00offchain/journal_delete");
}

struct PendingBlock<Block: BlockT> {
	header: Block::Header,
	justification: Option<Justification>,
	body: Option<Vec<Block::Extrinsic>>,
	leaf_state: NewBlockState,
}

// wrapper that implements trait required for state_db
struct StateMetaDb<'a>(&'a dyn Database<DbHash>);

impl<'a> sc_state_db::MetaDb for StateMetaDb<'a> {
	type Error = io::Error;

	fn get_meta(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.0.get(columns::STATE_META, key))
	}
}

/// Block database
pub struct BlockchainDb<Block: BlockT> {
	db: Arc<dyn Database<DbHash>>,
	meta: Arc<RwLock<Meta<NumberFor<Block>, Block::Hash>>>,
	leaves: RwLock<LeafSet<Block::Hash, NumberFor<Block>>>,
	header_metadata_cache: Arc<HeaderMetadataCache<Block>>,
}

impl<Block: BlockT> BlockchainDb<Block> {
	fn new(db: Arc<dyn Database<DbHash>>) -> ClientResult<Self> {
		let meta = read_meta::<Block>(&*db, columns::HEADER)?;
		let leaves = LeafSet::read_from_db(&*db, columns::META, meta_keys::LEAF_PREFIX)?;
		Ok(BlockchainDb {
			db,
			leaves: RwLock::new(leaves),
			meta: Arc::new(RwLock::new(meta)),
			header_metadata_cache: Arc::new(HeaderMetadataCache::default()),
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

	// Get block changes trie root, if available.
	fn changes_trie_root(&self, block: BlockId<Block>) -> ClientResult<Option<Block::Hash>> {
		self.header(block)
			.map(|header| header.and_then(|header|
				header.digest().log(DigestItem::as_changes_trie_root)
					.cloned()))
	}
}

impl<Block: BlockT> sc_client_api::blockchain::HeaderBackend<Block> for BlockchainDb<Block> {
	fn header(&self, id: BlockId<Block>) -> ClientResult<Option<Block::Header>> {
		utils::read_header(&*self.db, columns::KEY_LOOKUP, columns::HEADER, id)
	}

	fn info(&self) -> sc_client_api::blockchain::Info<Block> {
		let meta = self.meta.read();
		sc_client_api::blockchain::Info {
			best_hash: meta.best_hash,
			best_number: meta.best_number,
			genesis_hash: meta.genesis_hash,
			finalized_hash: meta.finalized_hash,
			finalized_number: meta.finalized_number,
			number_leaves: self.leaves.read().count(),
		}
	}

	fn status(&self, id: BlockId<Block>) -> ClientResult<sc_client_api::blockchain::BlockStatus> {
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
			true => Ok(sc_client_api::blockchain::BlockStatus::InChain),
			false => Ok(sc_client_api::blockchain::BlockStatus::Unknown),
		}
	}

	fn number(&self, hash: Block::Hash) -> ClientResult<Option<NumberFor<Block>>> {
		Ok(self.header_metadata(hash).ok().map(|header_metadata| header_metadata.number))
	}

	fn hash(&self, number: NumberFor<Block>) -> ClientResult<Option<Block::Hash>> {
		self.header(BlockId::Number(number)).and_then(|maybe_header| match maybe_header {
			Some(header) => Ok(Some(header.hash().clone())),
			None => Ok(None),
		})
	}
}

impl<Block: BlockT> sc_client_api::blockchain::Backend<Block> for BlockchainDb<Block> {
	fn body(&self, id: BlockId<Block>) -> ClientResult<Option<Vec<Block::Extrinsic>>> {
		match read_db(&*self.db, columns::KEY_LOOKUP, columns::BODY, id)? {
			Some(body) => match Decode::decode(&mut &body[..]) {
				Ok(body) => Ok(Some(body)),
				Err(err) => return Err(sp_blockchain::Error::Backend(
					format!("Error decoding body: {}", err)
				)),
			}
			None => Ok(None),
		}
	}

	fn justification(&self, id: BlockId<Block>) -> ClientResult<Option<Justification>> {
		match read_db(&*self.db, columns::KEY_LOOKUP, columns::JUSTIFICATION, id)? {
			Some(justification) => match Decode::decode(&mut &justification[..]) {
				Ok(justification) => Ok(Some(justification)),
				Err(err) => return Err(sp_blockchain::Error::Backend(
					format!("Error decoding justification: {}", err)
				)),
			}
			None => Ok(None),
		}
	}

	fn last_finalized(&self) -> ClientResult<Block::Hash> {
		Ok(self.meta.read().finalized_hash.clone())
	}

	fn cache(&self) -> Option<Arc<dyn sc_client_api::blockchain::Cache<Block>>> {
		None
	}

	fn leaves(&self) -> ClientResult<Vec<Block::Hash>> {
		Ok(self.leaves.read().hashes())
	}

	fn children(&self, parent_hash: Block::Hash) -> ClientResult<Vec<Block::Hash>> {
		children::read_children(&*self.db, columns::META, meta_keys::CHILDREN_PREFIX, parent_hash)
	}
}

impl<Block: BlockT> sc_client_api::blockchain::ProvideCache<Block> for BlockchainDb<Block> {
	fn cache(&self) -> Option<Arc<dyn sc_client_api::blockchain::Cache<Block>>> {
		None
	}
}

impl<Block: BlockT> HeaderMetadata<Block> for BlockchainDb<Block> {
	type Error = sp_blockchain::Error;

	fn header_metadata(&self, hash: Block::Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.header_metadata_cache.header_metadata(hash).map_or_else(|| {
			self.header(BlockId::hash(hash))?.map(|header| {
				let header_metadata = CachedHeaderMetadata::from(&header);
				self.header_metadata_cache.insert_header_metadata(
					header_metadata.hash,
					header_metadata.clone(),
				);
				header_metadata
			}).ok_or_else(|| ClientError::UnknownBlock(format!("header not found in db: {}", hash)))
		}, Ok)
	}

	fn insert_header_metadata(&self, hash: Block::Hash, metadata: CachedHeaderMetadata<Block>) {
		self.header_metadata_cache.insert_header_metadata(hash, metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.header_metadata_cache.remove_header_metadata(hash);
	}
}

impl<Block: BlockT> ProvideChtRoots<Block> for BlockchainDb<Block> {
	fn header_cht_root(
		&self,
		cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		let cht_number = match cht::block_to_cht_number(cht_size, block) {
			Some(number) => number,
			None => return Ok(None),
		};

		let cht_start: NumberFor<Block> = cht::start_number(cht::size(), cht_number);

		let mut current_num = cht_start;
		let cht_range = ::std::iter::from_fn(|| {
			let old_current_num = current_num;
			current_num = current_num + One::one();
			Some(old_current_num)
		});

		cht::compute_root::<Block::Header, HashFor<Block>, _>(
			cht::size(), cht_number, cht_range.map(|num| self.hash(num))
		).map(Some)
	}

	fn changes_trie_cht_root(
		&self,
		cht_size: NumberFor<Block>,
		block: NumberFor<Block>,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		let cht_number = match cht::block_to_cht_number(cht_size, block) {
			Some(number) => number,
			None => return Ok(None),
		};

		let cht_start: NumberFor<Block> = cht::start_number(cht::size(), cht_number);

		let mut current_num = cht_start;
		let cht_range = ::std::iter::from_fn(|| {
			let old_current_num = current_num;
			current_num = current_num + One::one();
			Some(old_current_num)
		});

		cht::compute_root::<Block::Header, HashFor<Block>, _>(
			cht::size(),
			cht_number,
			cht_range.map(|num| self.changes_trie_root(BlockId::Number(num))),
		).map(Some)
	}
}

/// Database transaction
pub struct BlockImportOperation<Block: BlockT> {
	old_state: SyncingCachingState<RefTrackingState<Block>, Block>,
	db_updates: PrefixedMemoryDB<HashFor<Block>>,
	storage_updates: StorageCollection,
	child_storage_updates: ChildStorageCollection,
	offchain_storage_updates: OffchainOverlayedChanges,
	changes_trie_updates: MemoryDB<HashFor<Block>>,
	changes_trie_build_cache_update: Option<ChangesTrieCacheAction<Block::Hash, NumberFor<Block>>>,
	changes_trie_config_update: Option<Option<ChangesTrieConfiguration>>,
	pending_block: Option<PendingBlock<Block>>,
	aux_ops: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	finalized_blocks: Vec<(BlockId<Block>, Option<Justification>)>,
	set_head: Option<BlockId<Block>>,
	commit_state: bool,
}

impl<Block: BlockT> BlockImportOperation<Block> {
	fn apply_offchain(
		&mut self,
		transaction: &mut Transaction<DbHash>,
		historied: Option<&mut HistoriedDBMut>,
		journals: Option<&mut TransactionalSerializeDB<historied_db::simple_db::SerializeDBDyn>>,
	) {
		let mut historied = historied.map(|historied_db| {
			let block_nodes = BlockNodes::new(historied_db.db.clone());
			let branch_nodes = BranchNodes::new(historied_db.db.clone());
			(historied_db, block_nodes, branch_nodes)
		});
		let mut journal_keys = journals.as_ref().map(|_| Vec::new());
		for ((prefix, key), value_operation) in self.offchain_storage_updates.drain() {
			let key: Vec<u8> = prefix
				.into_iter()
				.chain(sp_core::sp_std::iter::once(b'/'))
				.chain(key.into_iter())
				.collect();
			match value_operation {
				OffchainOverlayedChange::SetValue(val) => transaction.set_from_vec(columns::OFFCHAIN, &key, val),
				OffchainOverlayedChange::Remove => transaction.remove(columns::OFFCHAIN, &key),
				OffchainOverlayedChange::SetLocalValue(val) => {
					historied.as_mut().map(|(historied_db, block_nodes, branch_nodes)|
						historied_db.update_single_offchain(&key, Some(val), transaction, branch_nodes, block_nodes)
					);
					journal_keys.as_mut().map(|journal| journal.push(key));
				},
				OffchainOverlayedChange::RemoveLocal => {
					historied.as_mut().map(|(historied_db, block_nodes, branch_nodes)|
						historied_db.update_single_offchain(&key, None, transaction, branch_nodes, block_nodes)
					);
					journal_keys.as_mut().map(|journal| journal.push(key));
				},
			}
		}
		if let (
			Some(journal_keys),
			Some(ordered_db),
			Some(historied),
		) = (journal_keys, journals, historied.as_ref()) {
			// Note that this is safe because we import a new block.
			// Otherwhise we would need to share cache with a single journal instance.
			let mut journals = historied_db::management::JournalForMigrationBasis
				::<_, _, _, crate::historied_tree_bindings::LocalOffchainDelete>
				::from_db(ordered_db);
			journals.add_changes(
				ordered_db,
				historied.0.current_state.latest().clone(),
				journal_keys,
				true, // New block, no need for fetch
			)
		}

		historied.as_mut().map(|(_historied_db, block_nodes, branch_nodes)| {
			block_nodes.apply_transaction(transaction);
			branch_nodes.apply_transaction(transaction);
		});
	}

	fn apply_aux(&mut self, transaction: &mut Transaction<DbHash>) {
		for (key, maybe_val) in self.aux_ops.drain(..) {
			match maybe_val {
				Some(val) => transaction.set_from_vec(columns::AUX, &key, val),
				None => transaction.remove(columns::AUX, &key),
			}
		}
	}
}

impl<Block: BlockT> sc_client_api::backend::BlockImportOperation<Block> for BlockImportOperation<Block> {
	type State = SyncingCachingState<RefTrackingState<Block>, Block>;

	fn state(&self) -> ClientResult<Option<&Self::State>> {
		Ok(Some(&self.old_state))
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		body: Option<Vec<Block::Extrinsic>>,
		justification: Option<Justification>,
		leaf_state: NewBlockState,
	) -> ClientResult<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		if let Some(changes_trie_config_update) = changes_tries_storage::extract_new_configuration(&header) {
			self.changes_trie_config_update = Some(changes_trie_config_update.clone());
		}
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

	fn update_db_storage(&mut self, update: PrefixedMemoryDB<HashFor<Block>>) -> ClientResult<()> {
		self.db_updates = update;
		Ok(())
	}

	fn reset_storage(
		&mut self,
		storage: Storage,
	) -> ClientResult<Block::Hash> {
		if storage.top.keys().any(|k| well_known_keys::is_child_storage_key(&k)) {
			return Err(sp_blockchain::Error::GenesisInvalid.into());
		}

		let child_delta = storage.children_default.iter().map(|(_storage_key, child_content)|(
			&child_content.child_info,
			child_content.data.iter().map(|(k, v)| (&k[..], Some(&v[..]))),
		));

		let mut changes_trie_config: Option<ChangesTrieConfiguration> = None;
		let (root, transaction) = self.old_state.full_storage_root(
			storage.top.iter().map(|(k, v)| {
				if &k[..] == well_known_keys::CHANGES_TRIE_CONFIG {
					changes_trie_config = Some(
						Decode::decode(&mut &v[..])
							.expect("changes trie configuration is encoded properly at genesis")
					);
				}
				(&k[..], Some(&v[..]))
			}),
			child_delta
		);

		self.db_updates = transaction;
		self.changes_trie_config_update = Some(changes_trie_config);
		self.commit_state = true;
		Ok(root)
	}

	fn update_changes_trie(
		&mut self,
		update: ChangesTrieTransaction<HashFor<Block>, NumberFor<Block>>,
	) -> ClientResult<()> {
		self.changes_trie_updates = update.0;
		self.changes_trie_build_cache_update = Some(update.1);
		Ok(())
	}

	fn insert_aux<I>(&mut self, ops: I) -> ClientResult<()>
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		self.aux_ops.append(&mut ops.into_iter().collect());
		Ok(())
	}

	fn update_storage(
		&mut self,
		update: StorageCollection,
		child_update: ChildStorageCollection,
	) -> ClientResult<()> {
		self.storage_updates = update;
		self.child_storage_updates = child_update;
		Ok(())
	}

	fn update_offchain_storage(
		&mut self,
		offchain_update: OffchainOverlayedChanges,
	) -> ClientResult<()> {
		self.offchain_storage_updates = offchain_update;
		Ok(())
	}

	fn mark_finalized(
		&mut self,
		block: BlockId<Block>,
		justification: Option<Justification>,
	) -> ClientResult<()> {
		self.finalized_blocks.push((block, justification));
		Ok(())
	}

	fn mark_head(&mut self, block: BlockId<Block>) -> ClientResult<()> {
		assert!(self.set_head.is_none(), "Only one set head per operation is allowed");
		self.set_head = Some(block);
		Ok(())
	}
}

struct StorageDb<Block: BlockT> {
	pub db: Arc<dyn Database<DbHash>>,
	pub state_db: StateDb<Block::Hash, Vec<u8>>,
	prefix_keys: bool,
}

impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
		if self.prefix_keys {
			let key = prefixed_key::<HashFor<Block>>(key, prefix);
			self.state_db.get(&key, self)
		} else {
			self.state_db.get(key.as_ref(), self)
		}
		.map_err(|e| format!("Database backend error: {:?}", e))
	}
}

impl<Block: BlockT> sc_state_db::NodeDb for StorageDb<Block> {
	type Error = io::Error;
	type Key = [u8];

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.db.get(columns::STATE, key))
	}
}

struct DbGenesisStorage<Block: BlockT>(pub Block::Hash);

impl<Block: BlockT> DbGenesisStorage<Block> {
	pub fn new() -> Self {
		let mut root = Block::Hash::default();
		let mut mdb = MemoryDB::<HashFor<Block>>::default();
		sp_state_machine::TrieDBMut::<HashFor<Block>>::new(&mut mdb, &mut root);
		DbGenesisStorage(root)
	}
}

impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for DbGenesisStorage<Block> {
	fn get(&self, _key: &Block::Hash, _prefix: Prefix) -> Result<Option<DBValue>, String> {
		Ok(None)
	}
}

/// Frozen `value` at time `at`.
///
/// Used as inner structure under lock in `FrozenForDuration`.
struct Frozen<T: Clone> {
	at: std::time::Instant,
	value: Option<T>,
}

/// Some value frozen for period of time.
///
/// If time `duration` not passed since the value was instantiated,
/// current frozen value is returned. Otherwise, you have to provide
/// a new value which will be again frozen for `duration`.
pub(crate) struct FrozenForDuration<T: Clone> {
	duration: std::time::Duration,
	value: parking_lot::Mutex<Frozen<T>>,
}

impl<T: Clone> FrozenForDuration<T> {
	fn new(duration: std::time::Duration) -> Self {
		Self {
			duration,
			value: Frozen { at: std::time::Instant::now(), value: None }.into(),
		}
	}

	fn take_or_else<F>(&self, f: F) -> T where F: FnOnce() -> T {
		let mut lock = self.value.lock();
		if lock.at.elapsed() > self.duration || lock.value.is_none() {
			let new_value = f();
			lock.at = std::time::Instant::now();
			lock.value = Some(new_value.clone());
			new_value
		} else {
			lock.value.as_ref().expect("checked with lock above").clone()
		}
	}
}

/// Tree management for substrate. Inedxes are `u32` and values ar encoded as
/// `Vec<u8>`.
pub type TreeManagement<H, S> = historied_db::management::tree::TreeManagement<
	H,
	u32,
	u64,
	S,
>;

/// Register tree management consumer.
pub type RegisteredConsumer<H, S> = historied_db::management::tree::RegisteredConsumer<
	H,
	u32,
	u64,
	S,
>;

/// Disk backend.
///
/// Disk backend keeps data in a key-value store. In archive mode, trie nodes are kept from all blocks.
/// Otherwise, trie nodes are kept only from some recent blocks.
pub struct Backend<Block: BlockT> {
	storage: Arc<StorageDb<Block>>,
	offchain_storage: offchain::LocalStorage,
	offchain_local_storage: offchain::BlockChainLocalStorage<
		<HashFor<Block> as Hasher>::Out,
		TreeManagementPersistence,
	>,
	changes_tries_storage: DbChangesTrieStorage<Block>,
	blockchain: BlockchainDb<Block>,
	canonicalization_delay: u64,
	shared_cache: SharedCache<Block>,
	import_lock: Arc<RwLock<()>>,
	is_archive: bool,
	io_stats: FrozenForDuration<(kvdb::IoStats, StateUsageInfo)>,
	state_usage: Arc<StateUsageStats>,
	historied_management: Arc<RwLock<TreeManagement<
		<HashFor<Block> as Hasher>::Out,
		TreeManagementPersistence,
	>>>,
	historied_pruning_window: Option<NumberFor<Block>>,
	historied_next_finalizable: Arc<RwLock<Option<NumberFor<Block>>>>,
	historied_management_consumer: RegisteredConsumer<
		<HashFor<Block> as Hasher>::Out,
		TreeManagementPersistence,
	>,
	historied_management_consumer_transaction: Arc<RwLock<Transaction<DbHash>>>,
}

impl<Block: BlockT> Backend<Block> {
	/// Create a new instance of database backend.
	///
	/// The pruning window is how old a block must be before the state is pruned.
	pub fn new(config: DatabaseSettings, canonicalization_delay: u64) -> ClientResult<Self> {
		let (db, ordered, ordered_2) = crate::utils::open_database_and_historied::<Block>(
			&config,
			DatabaseType::Full,
		)?;
		Self::from_database(db as Arc<_>, ordered, ordered_2, canonicalization_delay, &config)
	}

	/// Create new memory-backed client backend for tests.
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test(
		keep_blocks: u32,
		canonicalization_delay: u64,
	) -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db = sp_database::as_database(db);
		let db_setting = DatabaseSettings {
			state_cache_size: 16777216,
			state_cache_child_ratio: Some((50, 100)),
			pruning: PruningMode::keep_blocks(keep_blocks),
			source: DatabaseSettingsSrc::Custom(db),
		};

		Self::new(db_setting, canonicalization_delay).expect("failed to create test-db")
	}

	fn from_database(
		db: Arc<dyn Database<DbHash>>,
		ordered_db: historied_db::simple_db::SerializeDBDyn,
		ordered_db_2: historied_db::simple_db::SerializeDBDyn,
		canonicalization_delay: u64,
		config: &DatabaseSettings,
	) -> ClientResult<Self> {
		let is_archive_pruning = config.pruning.is_archive();
		let blockchain = BlockchainDb::new(db.clone())?;
		let meta = blockchain.meta.clone();
		let map_e = |e: sc_state_db::Error<io::Error>| sp_blockchain::Error::from(
			format!("State database error: {:?}", e)
		);
		let historied_pruning_window = match &config.pruning {
			PruningMode::Constrained(constraint) => constraint.max_blocks.map(|nb| nb.into()),
			_ => None,
		};
		let state_db: StateDb<_, _> = StateDb::new(
			config.pruning.clone(),
			!config.source.supports_ref_counting(),
			&StateMetaDb(&*db),
		).map_err(map_e)?;
		let storage_db = StorageDb {
			db: db.clone(),
			state_db,
			prefix_keys: !config.source.supports_ref_counting(),
		};
		let offchain_storage = offchain::LocalStorage::new(db.clone());
		let changes_tries_storage = DbChangesTrieStorage::new(
			db.clone(),
			blockchain.header_metadata_cache.clone(),
			columns::META,
			columns::CHANGES_TRIE,
			columns::KEY_LOOKUP,
			columns::HEADER,
			columns::CACHE,
			meta,
			if is_archive_pruning {
				None
			} else {
				Some(MIN_BLOCKS_TO_KEEP_CHANGES_TRIES_FOR)
			},
		)?;

		let historied_persistence = TransactionalSerializeDB {
			db: ordered_db,
			pending: Default::default(),
		};
		let historied_management = Arc::new(RwLock::new(TreeManagement::from_ser(historied_persistence)));
		let offchain_local_storage = offchain::BlockChainLocalStorage::new(
			db,
			historied_management.clone(),
			ordered_db_2,
		);
		let mut historied_management_consumer: RegisteredConsumer<
			<HashFor<Block> as Hasher>::Out,
			TreeManagementPersistence,
		> = Default::default();
		let historied_management_consumer_transaction = Arc::new(RwLock::new(
			Default::default()
		));
		historied_management_consumer.register_consumer(Box::new(
			offchain::TransactionalConsumer {
				storage: offchain_local_storage.clone(),
				pending: historied_management_consumer_transaction.clone(),
			}));
		Ok(Backend {
			storage: Arc::new(storage_db),
			offchain_storage,
			offchain_local_storage,
			changes_tries_storage,
			blockchain,
			canonicalization_delay,
			shared_cache: new_shared_cache(
				config.state_cache_size,
				config.state_cache_child_ratio.unwrap_or(DEFAULT_CHILD_RATIO),
			),
			import_lock: Default::default(),
			is_archive: is_archive_pruning,
			io_stats: FrozenForDuration::new(std::time::Duration::from_secs(1)),
			state_usage: Arc::new(StateUsageStats::new()),
			historied_management,
			historied_next_finalizable: Arc::new(RwLock::new(None)),
			historied_management_consumer,
			historied_pruning_window,
			historied_management_consumer_transaction,
		})
	}

	/// Handle setting head within a transaction. `route_to` should be the last
	/// block that existed in the database. `best_to` should be the best block
	/// to be set.
	///
	/// In the case where the new best block is a block to be imported, `route_to`
	/// should be the parent of `best_to`. In the case where we set an existing block
	/// to be best, `route_to` should equal to `best_to`.
	fn set_head_with_transaction(
		&self,
		transaction: &mut Transaction<DbHash>,
		route_to: Block::Hash,
		best_to: (NumberFor<Block>, Block::Hash),
	) -> ClientResult<(Vec<Block::Hash>, Vec<Block::Hash>)> {
		let mut enacted = Vec::default();
		let mut retracted = Vec::default();

		let meta = self.blockchain.meta.read();

		// cannot find tree route with empty DB.
		if meta.best_hash != Default::default() {
			let tree_route = sp_blockchain::tree_route(
				&self.blockchain,
				meta.best_hash,
				route_to,
			)?;

			// uncanonicalize: check safety violations and ensure the numbers no longer
			// point to these block hashes in the key mapping.
			for r in tree_route.retracted() {
				if r.hash == meta.finalized_hash {
					warn!(
						"Potential safety failure: reverting finalized block {:?}",
						(&r.number, &r.hash)
					);

					return Err(::sp_blockchain::Error::NotInFinalizedChain.into());
				}

				retracted.push(r.hash.clone());
				utils::remove_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					r.number
				)?;
			}

			// canonicalize: set the number lookup to map to this block's hash.
			for e in tree_route.enacted() {
				enacted.push(e.hash.clone());
				utils::insert_number_to_key_mapping(
					transaction,
					columns::KEY_LOOKUP,
					e.number,
					e.hash
				)?;
			}
		}

		let lookup_key = utils::number_and_hash_to_lookup_key(best_to.0, &best_to.1)?;
		transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, lookup_key);
		utils::insert_number_to_key_mapping(
			transaction,
			columns::KEY_LOOKUP,
			best_to.0,
			best_to.1,
		)?;

		Ok((enacted, retracted))
	}

	fn ensure_sequential_finalization(
		&self,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
	) -> ClientResult<()> {
		let last_finalized = last_finalized.unwrap_or_else(|| self.blockchain.meta.read().finalized_hash);
		if *header.parent_hash() != last_finalized {
			return Err(::sp_blockchain::Error::NonSequentialFinalization(
				format!("Last finalized {:?} not parent of {:?}", last_finalized, header.hash()),
			).into());
		}
		Ok(())
	}

	fn finalize_block_with_transaction(
		&self,
		transaction: &mut Transaction<DbHash>,
		hash: &Block::Hash,
		header: &Block::Header,
		last_finalized: Option<Block::Hash>,
		justification: Option<Justification>,
		changes_trie_cache_ops: &mut Option<DbChangesTrieStorageTransaction<Block>>,
		finalization_displaced: &mut Option<FinalizationDisplaced<Block::Hash, NumberFor<Block>>>,
	) -> ClientResult<(Block::Hash, <Block::Header as HeaderT>::Number, bool, bool)> {
		// TODO: ensure best chain contains this block.
		let number = *header.number();
		self.ensure_sequential_finalization(header, last_finalized)?;

		self.note_finalized(
			transaction,
			false,
			header,
			*hash,
			changes_trie_cache_ops,
			finalization_displaced,
		)?;

		if let Some(justification) = justification {
			transaction.set_from_vec(
				columns::JUSTIFICATION,
				&utils::number_and_hash_to_lookup_key(number, hash)?,
				justification.encode(),
			);
		}
		Ok((*hash, number, false, true))
	}

	// performs forced canonicalization with a delay after importing a non-finalized block.
	fn force_delayed_canonicalize(
		&self,
		transaction: &mut Transaction<DbHash>,
		hash: Block::Hash,
		number: NumberFor<Block>,
	)
		-> ClientResult<()>
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
				::sc_client_api::blockchain::HeaderBackend::hash(&self.blockchain, new_canonical.saturated_into())?
					.expect("existence of block with number `new_canonical` \
						implies existence of blocks with all numbers before it; qed")
			};

			trace!(target: "db", "Canonicalize block #{} ({:?})", new_canonical, hash);
			let commit = self.storage.state_db.canonicalize_block(&hash)
				.map_err(|e: sc_state_db::Error<io::Error>| sp_blockchain::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(transaction, commit);
		};

		Ok(())
	}

	fn try_commit_operation(
		&self,
		mut operation: BlockImportOperation<Block>,
	) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		let mut finalization_displaced_leaves = None;

		operation.apply_aux(&mut transaction);

		let hashes = operation.pending_block.as_ref().map(|pending_block| {
			let hash = pending_block.header.hash();
			let parent_hash = *pending_block.header.parent_hash();
			(hash, parent_hash)
		});

		let mut historied_db = if let Some((hash, parent_hash)) = hashes {
			// lazy init, not that this can lead to no finalization
			// if the node get close to often, with current windows
			// size, this is fine, otherwhise this value will need
			// to persist.
			if self.historied_next_finalizable.read().is_none() {
				let parent_block = BlockId::Hash(parent_hash.clone());
				if let Some(nb) = self.blockchain.block_number_from_id(&parent_block)? {
					*self.historied_next_finalizable.write() = Some(nb + HISTORIED_FINALIZATION_WINDOWS.into());
				}
			}

			// Ensure pending layer is clean
			let _ = std::mem::replace(&mut self.historied_management.write().ser().pending, Default::default());
			let update_plan = {
				// lock does notinclude update of value as we do not have concurrent block creation
				let mut management = self.historied_management.write();
				if let Some(state) = Some(management.get_db_state_for_fork(&parent_hash)
					.unwrap_or_else(|| {
						// allow this to start from existing state TODO add a stored boolean to only allow
						// that once in genesis or in tests
						warn!("state not found for parent hash, appending to latest");
						management.latest_state_fork()
					}))
				{
					let _query_plan = management.append_external_state(hash.clone(), &state)
						.ok_or(ClientError::Msg("correct state resolution".into()))?;
					let update_plan = management.get_db_state_mut(&hash)
						.ok_or(ClientError::Msg("correct state resolution".into()))?;
					update_plan
				} else {
					return Err("missing update plan".into());
				}
			};
			Some(HistoriedDBMut {
				current_state: update_plan,
				db: self.blockchain.db.clone(),
			})
		} else {
			None
		};

		{
			use historied_db::management::tree::TreeManagementStorage;
			let mut management;
			let journals = if TreeManagementPersistence::JOURNAL_DELETE {
				management = self.historied_management.write();
				Some(management.ser())
			} else {
				None
			};
		
			operation.apply_offchain(&mut transaction, historied_db.as_mut(), journals);
		}

		// write management state changes
		let pending = std::mem::replace(&mut self.historied_management.write().ser().pending, Default::default());
		for (col, (mut changes, dropped)) in pending {
			if dropped {
				use historied_db::simple_db::SerializeDB;
				for (key, _v) in self.historied_management.read().ser_ref().iter(col) {
					changes.insert(key, None);
				}
			}
			if let Some((col, p)) = resolve_collection(col) {
				for (key, change) in changes {
					subcollection_prefixed_key!(p, key);
					match change {
						Some(value) => transaction.set_from_vec(col, key, value),
						None => transaction.remove(col, key),
					}
				}
			} else {
				warn!("Unknown collection for tree management pending transaction {:?}", col);
			}
		}

		let mut meta_updates = Vec::with_capacity(operation.finalized_blocks.len());
		let mut last_finalized_hash = self.blockchain.meta.read().finalized_hash;

		let mut changes_trie_cache_ops = None;
		for (block, justification) in operation.finalized_blocks {
			let block_hash = self.blockchain.expect_block_hash_from_id(&block)?;
			let block_header = self.blockchain.expect_header(BlockId::Hash(block_hash))?;

			meta_updates.push(self.finalize_block_with_transaction(
				&mut transaction,
				&block_hash,
				&block_header,
				Some(last_finalized_hash),
				justification,
				&mut changes_trie_cache_ops,
				&mut finalization_displaced_leaves,
			)?);
			last_finalized_hash = block_hash;
		}

		let imported = if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();
			let parent_hash = *pending_block.header.parent_hash();
			let number = pending_block.header.number().clone();

			// blocks are keyed by number + hash.
			let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;

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
			)?;

			let header_metadata = CachedHeaderMetadata::from(&pending_block.header);
			self.blockchain.insert_header_metadata(
				header_metadata.hash,
				header_metadata,
			);

			transaction.set_from_vec(columns::HEADER, &lookup_key, pending_block.header.encode());
			if let Some(body) = &pending_block.body {
				transaction.set_from_vec(columns::BODY, &lookup_key, body.encode());
			}
			if let Some(justification) = pending_block.justification {
				transaction.set_from_vec(columns::JUSTIFICATION, &lookup_key, justification.encode());
			}

			if number.is_zero() {
				transaction.set_from_vec(columns::META, meta_keys::FINALIZED_BLOCK, lookup_key);
				transaction.set(columns::META, meta_keys::GENESIS_HASH, hash.as_ref());

				// for tests, because config is set from within the reset_storage
				if operation.changes_trie_config_update.is_none() {
					operation.changes_trie_config_update = Some(None);
				}
			}

			let finalized = if operation.commit_state {
				let mut changeset: sc_state_db::ChangeSet<Vec<u8>> = sc_state_db::ChangeSet::default();
				let mut ops: u64 = 0;
				let mut bytes: u64 = 0;
				let mut removal: u64 = 0;
				let mut bytes_removal: u64 = 0;
				for (mut key, (val, rc)) in operation.db_updates.drain() {
					if !self.storage.prefix_keys {
						// Strip prefix
						key.drain(0 .. key.len() - DB_HASH_LEN);
					};
					if rc > 0 {
						ops += 1;
						bytes += key.len() as u64 + val.len() as u64;
						if rc == 1 {
							changeset.inserted.push((key, val.to_vec()));
						} else {
							changeset.inserted.push((key.clone(), val.to_vec()));
							for _ in 0 .. rc - 1 {
								changeset.inserted.push((key.clone(), Default::default()));
							}
						}
					} else if rc < 0 {
						removal += 1;
						bytes_removal += key.len() as u64;
						if rc == -1 {
							changeset.deleted.push(key);
						} else {
							for _ in 0 .. -rc {
								changeset.deleted.push(key.clone());
							}
						}
					}
				}
				self.state_usage.tally_writes_nodes(ops, bytes);
				self.state_usage.tally_removed_nodes(removal, bytes_removal);

				let mut ops: u64 = 0;
				let mut bytes: u64 = 0;
				for (key, value) in operation.storage_updates.iter()
					.chain(operation.child_storage_updates.iter().flat_map(|(_, s)| s.iter())) {
						ops += 1;
						bytes += key.len() as u64;
						if let Some(v) = value.as_ref() {
							bytes += v.len() as u64;
						}
				}
				self.state_usage.tally_writes(ops, bytes);
				let number_u64 = number.saturated_into::<u64>();
				let commit = self.storage.state_db.insert_block(
					&hash,
					number_u64,
					&pending_block.header.parent_hash(),
					changeset,
				).map_err(|e: sc_state_db::Error<io::Error>|
					sp_blockchain::Error::from(format!("State database error: {:?}", e))
				)?;
				apply_state_commit(&mut transaction, commit);

				// Check if need to finalize. Genesis is always finalized instantly.
				let finalized = number_u64 == 0 || pending_block.leaf_state.is_final();
				finalized
			} else {
				false
			};

			let header = &pending_block.header;
			let is_best = pending_block.leaf_state.is_best();
			let changes_trie_updates = operation.changes_trie_updates;
			let changes_trie_config_update = operation.changes_trie_config_update;
			changes_trie_cache_ops = Some(self.changes_tries_storage.commit(
				&mut transaction,
				changes_trie_updates,
				cache::ComplexBlockId::new(
					*header.parent_hash(),
					if number.is_zero() { Zero::zero() } else { number - One::one() },
				),
				cache::ComplexBlockId::new(hash, number),
				header,
				finalized,
				changes_trie_config_update,
				changes_trie_cache_ops,
			)?);
			self.state_usage.merge_sm(operation.old_state.usage_info());
			// release state reference so that it can be finalized
			let cache = operation.old_state.into_cache_changes();

			if finalized {
				// TODO: ensure best chain contains this block.
				self.ensure_sequential_finalization(header, Some(last_finalized_hash))?;
				self.note_finalized(
					&mut transaction,
					true,
					header,
					hash,
					&mut changes_trie_cache_ops,
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

			let mut children = children::read_children(
				&*self.storage.db,
				columns::META,
				meta_keys::CHILDREN_PREFIX,
				parent_hash,
			)?;
			children.push(hash);
			children::write_children(
				&mut transaction,
				columns::META,
				meta_keys::CHILDREN_PREFIX,
				parent_hash,
				children,
			);

			meta_updates.push((hash, number, pending_block.leaf_state.is_best(), finalized));

			Some((number, hash, enacted, retracted, displaced_leaf, is_best, cache))
		} else {
			None
		};

		let cache_update = if let Some(set_head) = operation.set_head {
			if let Some(header) = sc_client_api::blockchain::HeaderBackend::header(&self.blockchain, set_head)? {
				let number = header.number();
				let hash = header.hash();

				let (enacted, retracted) = self.set_head_with_transaction(
					&mut transaction,
					hash.clone(),
					(number.clone(), hash.clone())
				)?;
				meta_updates.push((hash, *number, true, false));
				Some((enacted, retracted))
			} else {
				return Err(sp_blockchain::Error::UnknownBlock(format!("Cannot set head {:?}", set_head)))
			}
		} else {
			None
		};

		self.storage.db.commit(transaction)?;

		if let Some((
			number,
			hash,
			enacted,
			retracted,
			_displaced_leaf,
			is_best,
			mut cache,
		)) = imported {
			cache.sync_cache(
				&enacted,
				&retracted,
				operation.storage_updates,
				operation.child_storage_updates,
				Some(hash),
				Some(number),
				is_best,
			);
		}

		if let Some(changes_trie_build_cache_update) = operation.changes_trie_build_cache_update {
			self.changes_tries_storage.commit_build_cache(changes_trie_build_cache_update);
		}
		self.changes_tries_storage.post_commit(changes_trie_cache_ops);

		if let Some((enacted, retracted)) = cache_update {
			self.shared_cache.lock().sync(&enacted, &retracted);
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
		transaction: &mut Transaction<DbHash>,
		is_inserted: bool,
		f_header: &Block::Header,
		f_hash: Block::Hash,
		changes_trie_cache_ops: &mut Option<DbChangesTrieStorageTransaction<Block>>,
		displaced: &mut Option<FinalizationDisplaced<Block::Hash, NumberFor<Block>>>
	) -> ClientResult<()> {
		let f_num = f_header.number().clone();

		if self.storage.state_db.best_canonical().map(|c| f_num.saturated_into::<u64>() > c).unwrap_or(true) {
			let lookup_key = utils::number_and_hash_to_lookup_key(f_num, f_hash.clone())?;
			transaction.set_from_vec(columns::META, meta_keys::FINALIZED_BLOCK, lookup_key);

			let commit = self.storage.state_db.canonicalize_block(&f_hash)
				.map_err(|e: sc_state_db::Error<io::Error>| sp_blockchain::Error::from(format!("State database error: {:?}", e)))?;
			apply_state_commit(transaction, commit);

			if !f_num.is_zero() {
				let new_changes_trie_cache_ops = self.changes_tries_storage.finalize(
					transaction,
					*f_header.parent_hash(),
					f_hash,
					f_num,
					if is_inserted { Some(&f_header) } else { None },
					changes_trie_cache_ops.take(),
				)?;
				*changes_trie_cache_ops = Some(new_changes_trie_cache_ops);
			}
		}

		let new_displaced = self.blockchain.leaves.write().finalize_height(f_num);
		match displaced {
			x @ &mut None => *x = Some(new_displaced),
			&mut Some(ref mut displaced) => displaced.merge(new_displaced),
		}

		Ok(())
	}

	fn historied_pruning(&self, hash: &Block::Hash, number: NumberFor<Block>)
		-> ClientResult<()> {
		let do_finalize = &number > &self.historied_next_finalizable.read().as_ref().unwrap_or(&0.into());
		if !do_finalize {
			return Ok(())
		}

		let prune_index = self.historied_pruning_window.map(|nb| {
			number.saturating_sub(nb).saturated_into::<u64>()
		});

		// Ensure pending layer is clean
		let _ = std::mem::replace(&mut self.historied_management.write().ser().pending, Default::default());

		// TODO large mgmt lock
		let switch_index = self.historied_management.write().get_db_state_for_fork(hash);
		let path = {
			use historied_db::ManagementRef;
			self.historied_management.write().get_db_state(hash)
		};
		
		if let (Some(switch_index), Some(path)) = (switch_index, path) {
			self.historied_management.write().canonicalize(path, switch_index, prune_index);
			// do migrate data
			self.historied_management_consumer.migrate(&mut *self.historied_management.write());
		} else {
			return Err(ClientError::UnknownBlock("Missing in historied management".to_string()));
		}

		// flush historied management changes
		let pending = std::mem::replace(&mut self.historied_management.write().ser().pending, Default::default());
		let mut transaction = std::mem::replace(&mut *self.historied_management_consumer_transaction.write(), Default::default());
		// TODO this is duplicated code: put in a function
		for (col, (mut changes, dropped)) in pending {
			if dropped {
				use historied_db::simple_db::SerializeDB;
				for (key, _v) in self.historied_management.read().ser_ref().iter(col) {
					changes.insert(key, None);
				}
			}
			if let Some((col, p)) = resolve_collection(col) {
				for (key, change) in changes {
					subcollection_prefixed_key!(p, key);
					match change {
						Some(value) => transaction.set_from_vec(col, key, value),
						None => transaction.remove(col, key),
					}
				}
			} else {
				warn!("Unknown collection for tree management pending transaction {:?}", col);
			}
		}

		self.storage.db.commit(transaction)?;
		*self.historied_next_finalizable.write() = Some(number + HISTORIED_FINALIZATION_WINDOWS.into());
		Ok(())
	}
}

/// Avoid finalizing at every block.
const HISTORIED_FINALIZATION_WINDOWS: u8 = 101;

fn apply_state_commit(transaction: &mut Transaction<DbHash>, commit: sc_state_db::CommitSet<Vec<u8>>) {
	for (key, val) in commit.data.inserted.into_iter() {
		transaction.set_from_vec(columns::STATE, &key[..], val);
	}
	for key in commit.data.deleted.into_iter() {
		transaction.remove(columns::STATE, &key[..]);
	}
	for (key, val) in commit.meta.inserted.into_iter() {
		transaction.set_from_vec(columns::STATE_META, &key[..], val);
	}
	for key in commit.meta.deleted.into_iter() {
		transaction.remove(columns::STATE_META, &key[..]);
	}
}

impl<Block> sc_client_api::backend::AuxStore for Backend<Block> where Block: BlockT {
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		for (k, v) in insert {
			transaction.set(columns::AUX, k, v);
		}
		for k in delete {
			transaction.remove(columns::AUX, k);
		}
		self.storage.db.commit(transaction)?;
		Ok(())
	}

	fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Ok(self.storage.db.get(columns::AUX, key))
	}
}

impl<Block: BlockT> sc_client_api::backend::Backend<Block> for Backend<Block> {
	type BlockImportOperation = BlockImportOperation<Block>;
	type Blockchain = BlockchainDb<Block>;
	type State = SyncingCachingState<RefTrackingState<Block>, Block>;
	type OffchainPersistentStorage = offchain::LocalStorage;
	type OffchainLocalStorage = offchain::BlockChainLocalStorage<
		<HashFor<Block> as Hasher>::Out,
		TreeManagementPersistence,
	>;

	fn begin_operation(&self) -> ClientResult<Self::BlockImportOperation> {
		let mut old_state = self.state_at(BlockId::Hash(Default::default()))?;
		old_state.disable_syncing();

		Ok(BlockImportOperation {
			pending_block: None,
			old_state,
			db_updates: PrefixedMemoryDB::default(),
			storage_updates: Default::default(),
			child_storage_updates: Default::default(),
			offchain_storage_updates: Default::default(),
			changes_trie_config_update: None,
			changes_trie_updates: MemoryDB::default(),
			changes_trie_build_cache_update: None,
			aux_ops: Vec::new(),
			finalized_blocks: Vec::new(),
			set_head: None,
			commit_state: false,
		})
	}

	fn begin_state_operation(
		&self,
		operation: &mut Self::BlockImportOperation,
		block: BlockId<Block>,
	) -> ClientResult<()> {
		operation.old_state = self.state_at(block)?;
		operation.old_state.disable_syncing();

		operation.commit_state = true;
		Ok(())
	}

	fn commit_operation(
		&self,
		operation: Self::BlockImportOperation,
	) -> ClientResult<()> {
		let usage = operation.old_state.usage_info();
		self.state_usage.merge_sm(usage);
		let last_final = operation.finalized_blocks.last().cloned();
		match self.try_commit_operation(operation) {
			Ok(_) => {
				self.storage.state_db.apply_pending();

				// call historied pruning
				if let Some(latest_final) = last_final {
					let block = latest_final.0;
					if let (Some(number), Some(hash)) = (self.blockchain.block_number_from_id(&block)?,
						self.blockchain.block_hash_from_id(&block)?) {
						self.historied_pruning(&hash, number)?;
					}
				}
	
				Ok(())
			},
			e @ Err(_) => {
				self.storage.state_db.revert_pending();
				e
			}
		}
	}

	fn finalize_block(
		&self,
		block: BlockId<Block>,
		justification: Option<Justification>,
	) -> ClientResult<()> {
		let mut transaction = Transaction::new();
		let hash = self.blockchain.expect_block_hash_from_id(&block)?;
		let header = self.blockchain.expect_header(block)?;
		let mut displaced = None;

		let mut changes_trie_cache_ops = None;
		let (hash, number, is_best, is_finalized) = self.finalize_block_with_transaction(
			&mut transaction,
			&hash,
			&header,
			None,
			justification,
			&mut changes_trie_cache_ops,
			&mut displaced,
		)?;
		self.storage.db.commit(transaction)?;
		self.blockchain.update_meta(hash, number, is_best, is_finalized);
		self.changes_tries_storage.post_commit(changes_trie_cache_ops);
		if let Some(number) = self.blockchain.block_number_from_id(&block)? {
			self.historied_pruning(&hash, number)?;
		}
		Ok(())
	}

	fn changes_trie_storage(&self) -> Option<&dyn PrunableStateChangesTrieStorage<Block>> {
		Some(&self.changes_tries_storage)
	}

	fn offchain_persistent_storage(&self) -> Option<Self::OffchainPersistentStorage> {
		Some(self.offchain_storage.clone())
	}

	fn offchain_local_storage(&self) -> Option<Self::OffchainLocalStorage> {
		Some(self.offchain_local_storage.clone())
	}

	fn usage_info(&self) -> Option<UsageInfo> {
		let (io_stats, state_stats) = self.io_stats.take_or_else(||
			(
				// TODO: implement DB stats and cache size retrieval
				kvdb::IoStats::empty(),
				self.state_usage.take(),
			)
		);
		let database_cache = MemorySize::from_bytes(0);
		let state_cache = MemorySize::from_bytes(
			(*&self.shared_cache).lock().used_storage_cache_size(),
		);
		let state_db = self.storage.state_db.memory_info();

		Some(UsageInfo {
			memory: MemoryInfo {
				state_cache,
				database_cache,
				state_db,
			},
			io: IoInfo {
				transactions: io_stats.transactions,
				bytes_read: io_stats.bytes_read,
				bytes_written: io_stats.bytes_written,
				writes: io_stats.writes,
				reads: io_stats.reads,
				average_transaction_size: io_stats.avg_transaction_size() as u64,
				state_reads: state_stats.reads.ops,
				state_writes: state_stats.writes.ops,
				state_writes_cache: state_stats.overlay_writes.ops,
				state_reads_cache: state_stats.cache_reads.ops,
				state_writes_nodes: state_stats.nodes_writes.ops,
			},
		})
	}

	fn revert(
		&self,
		n: NumberFor<Block>,
		revert_finalized: bool,
	) -> ClientResult<(NumberFor<Block>, HashSet<Block::Hash>)> {
		let mut reverted_finalized = HashSet::new();

		let mut best_number = self.blockchain.info().best_number;
		let mut best_hash = self.blockchain.info().best_hash;

		let finalized = self.blockchain.info().finalized_number;

		let revertible = best_number - finalized;
		let n = if !revert_finalized && revertible < n {
			revertible
		} else {
			n
		};

		let mut revert_blocks = || -> ClientResult<NumberFor<Block>> {
			for c in 0 .. n.saturated_into::<u64>() {
				if best_number.is_zero() {
					return Ok(c.saturated_into::<NumberFor<Block>>())
				}
				let mut transaction = Transaction::new();
				let removed_number = best_number;
				let removed = self.blockchain.header(BlockId::Number(best_number))?.ok_or_else(
					|| sp_blockchain::Error::UnknownBlock(
						format!("Error reverting to {}. Block hash not found.", best_number)))?;
				let removed_hash = removed.hash();

				let prev_number = best_number.saturating_sub(One::one());
				let prev_hash = self.blockchain.hash(prev_number)?.ok_or_else(
					|| sp_blockchain::Error::UnknownBlock(
						format!("Error reverting to {}. Block hash not found.", best_number))
				)?;

				if !self.have_state_at(&prev_hash, prev_number) {
					return Ok(c.saturated_into::<NumberFor<Block>>())
				}

				match self.storage.state_db.revert_one() {
					Some(commit) => {
						apply_state_commit(&mut transaction, commit);

						best_number = prev_number;
						best_hash = prev_hash;

						let update_finalized = best_number < finalized;

						let key = utils::number_and_hash_to_lookup_key(best_number.clone(), &best_hash)?;
						let changes_trie_cache_ops = self.changes_tries_storage.revert(
							&mut transaction,
							&cache::ComplexBlockId::new(
								removed.hash(),
								removed_number,
							),
						)?;
						if update_finalized {
							transaction.set_from_vec(
								columns::META,
								meta_keys::FINALIZED_BLOCK,
								key.clone()
							);
							reverted_finalized.insert(removed_hash);
						}
						transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, key);
						transaction.remove(columns::KEY_LOOKUP, removed.hash().as_ref());
						children::remove_children(&mut transaction, columns::META, meta_keys::CHILDREN_PREFIX, best_hash);
						self.storage.db.commit(transaction)?;
						self.changes_tries_storage.post_commit(Some(changes_trie_cache_ops));
						self.blockchain.update_meta(best_hash, best_number, true, update_finalized);
					}
					None => return Ok(c.saturated_into::<NumberFor<Block>>())
				}
			}

			Ok(n)
		};

		let reverted = revert_blocks()?;

		let revert_leaves = || -> ClientResult<()> {
			let mut transaction = Transaction::new();
			let mut leaves = self.blockchain.leaves.write();

			leaves.revert(best_hash, best_number);
			leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);
			self.storage.db.commit(transaction)?;

			Ok(())
		};

		revert_leaves()?;

		Ok((reverted, reverted_finalized))
	}

	fn blockchain(&self) -> &BlockchainDb<Block> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<Block>) -> ClientResult<Self::State> {
		use sc_client_api::blockchain::HeaderBackend as BcHeaderBackend;

		// special case for genesis initialization
		match block {
			BlockId::Hash(h) if h == Default::default() => {
				let genesis_storage = DbGenesisStorage::<Block>::new();
				let root = genesis_storage.0.clone();
				let db_state = DbState::<Block>::new(
					Arc::new(genesis_storage),
					root,
				);
				let state = RefTrackingState::new(db_state, self.storage.clone(), None);
				let caching_state = CachingState::new(
					state,
					self.shared_cache.clone(),
					None,
				);
				return Ok(SyncingCachingState::new(
					caching_state,
					self.state_usage.clone(),
					self.blockchain.meta.clone(),
					self.import_lock.clone(),
				));
			},
			_ => {}
		}

		let hash = match block {
			BlockId::Hash(h) => h,
			BlockId::Number(n) => self.blockchain.hash(n)?.ok_or_else(||
				sp_blockchain::Error::UnknownBlock(format!("Unknown block number {}", n))
			)?,
		};

		match self.blockchain.header_metadata(hash) {
			Ok(ref hdr) => {
				if !self.have_state_at(&hash, hdr.number) {
					return Err(
						sp_blockchain::Error::UnknownBlock(
							format!("State already discarded for {:?}", block)
						)
					)
				}
				if let Ok(()) = self.storage.state_db.pin(&hash) {
					let root = hdr.state_root;
					let db_state = DbState::<Block>::new(
						self.storage.clone(),
						root,
					);
					let state = RefTrackingState::new(
						db_state,
						self.storage.clone(),
						Some(hash.clone()),
					);
					let caching_state = CachingState::new(
						state,
						self.shared_cache.clone(),
						Some(hash),
					);
					Ok(SyncingCachingState::new(
						caching_state,
						self.state_usage.clone(),
						self.blockchain.meta.clone(),
						self.import_lock.clone(),
					))
				} else {
					Err(
						sp_blockchain::Error::UnknownBlock(
							format!("State already discarded for {:?}", block)
						)
					)
				}
			},
			Err(e) => Err(e),
		}
	}

	fn have_state_at(&self, hash: &Block::Hash, number: NumberFor<Block>) -> bool {
		if self.is_archive {
			match self.blockchain.header_metadata(hash.clone()) {
				Ok(header) => {
					sp_state_machine::Storage::get(
						self.storage.as_ref(),
						&header.state_root,
						(&[], None),
					).unwrap_or(None).is_some()
				},
				_ => false,
			}
		} else {
			!self.storage.state_db.is_pruned(hash, number.saturated_into::<u64>())
		}
	}

	fn get_import_lock(&self) -> &RwLock<()> {
		&*self.import_lock
	}
}

impl<Block: BlockT> sc_client_api::backend::LocalBackend<Block> for Backend<Block> {}

#[cfg(test)]
pub(crate) mod tests {
	use hash_db::{HashDB, EMPTY_PREFIX};
	use super::*;
	use crate::columns;
	use sp_core::H256;
	use sc_client_api::backend::{Backend as BTrait, BlockImportOperation as Op};
	use sc_client_api::blockchain::Backend as BLBTrait;
	use sp_runtime::testing::{Header, Block as RawBlock, ExtrinsicWrapper};
	use sp_runtime::traits::{Hash, BlakeTwo256};
	use sp_runtime::generic::DigestItem;
	use sp_state_machine::{TrieMut, TrieDBMut};
	use sp_blockchain::{lowest_common_ancestor, tree_route};

	pub(crate) type Block = RawBlock<ExtrinsicWrapper<u64>>;

	pub fn prepare_changes(changes: Vec<(Vec<u8>, Vec<u8>)>) -> (H256, MemoryDB<BlakeTwo256>) {
		let mut changes_root = H256::default();
		let mut changes_trie_update = MemoryDB::<BlakeTwo256>::default();
		{
			let mut trie = TrieDBMut::<BlakeTwo256>::new(
				&mut changes_trie_update,
				&mut changes_root
			);
			for (key, value) in changes {
				trie.insert(&key, &value).unwrap();
			}
		}

		(changes_root, changes_trie_update)
	}

	pub fn insert_header(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		changes: Option<Vec<(Vec<u8>, Vec<u8>)>>,
		extrinsics_root: H256,
	) -> H256 {
		insert_block(backend, number, parent_hash, changes, None, extrinsics_root)
	}

	pub fn insert_block(
		backend: &Backend<Block>,
		number: u64,
		parent_hash: H256,
		changes: Option<Vec<(Vec<u8>, Vec<u8>)>>,
		offchain: Option<OffchainOverlayedChanges>,
		extrinsics_root: H256,
	) -> H256 {
		use sp_runtime::testing::Digest;

		let mut digest = Digest::default();
		let mut changes_trie_update = Default::default();
		if let Some(changes) = changes {
			let (root, update) = prepare_changes(changes);
			digest.push(DigestItem::ChangesTrieRoot(root));
			changes_trie_update = update;
		}
		let header = Header {
			number,
			parent_hash,
			state_root: BlakeTwo256::trie_root(Vec::new()),
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
		op.set_block_data(header, Some(Vec::new()), None, NewBlockState::Best).unwrap();
		op.update_changes_trie((changes_trie_update, ChangesTrieCacheAction::Clear)).unwrap();
		if let Some(offchain) = offchain {
			op.update_offchain_storage(offchain).unwrap();
		}
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

		let backend = Backend::<Block>::new(DatabaseSettings {
			state_cache_size: 16777216,
			state_cache_child_ratio: Some((50, 100)),
			pruning: PruningMode::keep_blocks(1),
			source: DatabaseSettingsSrc::Custom(backing),
		}, 0).unwrap();
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
				.map(|(x, y)| (&x[..], Some(&y[..])))
			).0.into();
			let hash = header.hash();

			op.reset_storage(Storage {
				top: storage.into_iter().collect(),
				children_default: Default::default(),
			}).unwrap();
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

			let (root, overlay) = op.old_state.storage_root(
				storage.iter()
					.map(|(k, v)| (&k[..], v.as_ref().map(|v| &v[..])))
			);
			op.update_db_storage(overlay).unwrap();
			header.state_root = root.into();

			op.update_storage(storage, Vec::new()).unwrap();
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
		sp_tracing::try_init_simple();
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

			header.state_root = op.old_state.storage_root(std::iter::empty()).0.into();
			let hash = header.hash();

			op.reset_storage(Storage {
				top: Default::default(),
				children_default: Default::default(),
			}).unwrap();

			key = op.db_updates.insert(EMPTY_PREFIX, b"hello");
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();
			assert_eq!(backend.storage.db.get(
				columns::STATE,
				&sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX)
			).unwrap(), &b"hello"[..]);
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

			op.db_updates.insert(EMPTY_PREFIX, b"hello");
			op.db_updates.remove(&key, EMPTY_PREFIX);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();
			assert_eq!(backend.storage.db.get(
				columns::STATE,
				&sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX)
			).unwrap(), &b"hello"[..]);
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

			op.db_updates.remove(&key, EMPTY_PREFIX);
			op.set_block_data(
				header,
				Some(vec![]),
				None,
				NewBlockState::Best,
			).unwrap();

			backend.commit_operation(op).unwrap();

			assert!(backend.storage.db.get(
				columns::STATE,
				&sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX)
			).is_some());
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
			assert!(backend.storage.db.get(
				columns::STATE,
				&sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX)
			).is_none());
		}

		backend.finalize_block(BlockId::Number(1), None).unwrap();
		backend.finalize_block(BlockId::Number(2), None).unwrap();
		backend.finalize_block(BlockId::Number(3), None).unwrap();
		assert!(backend.storage.db.get(
			columns::STATE,
			&sp_trie::prefixed_key::<BlakeTwo256>(&key, EMPTY_PREFIX)
		).is_none());
	}

	#[test]
	fn tree_route_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, None, Default::default());
		let a2 = insert_header(&backend, 2, a1, None, Default::default());
		let a3 = insert_header(&backend, 3, a2, None, Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, None, H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, None, Default::default());

		{
			let tree_route = tree_route(blockchain, a3, b2).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2, a1]);
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![b1, b2]);
		}

		{
			let tree_route = tree_route(blockchain, a1, a3).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a2, a3]);
		}

		{
			let tree_route = tree_route(blockchain, a3, a1).unwrap();

			assert_eq!(tree_route.common_block().hash, a1);
			assert_eq!(tree_route.retracted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![a3, a2]);
			assert!(tree_route.enacted().is_empty());
		}

		{
			let tree_route = tree_route(blockchain, a2, a2).unwrap();

			assert_eq!(tree_route.common_block().hash, a2);
			assert!(tree_route.retracted().is_empty());
			assert!(tree_route.enacted().is_empty());
		}
	}

	#[test]
	fn tree_route_child() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());

		{
			let tree_route = tree_route(blockchain, block0, block1).unwrap();

			assert_eq!(tree_route.common_block().hash, block0);
			assert!(tree_route.retracted().is_empty());
			assert_eq!(tree_route.enacted().iter().map(|r| r.hash).collect::<Vec<_>>(), vec![block1]);
		}
	}

	#[test]
	fn lowest_common_ancestor_works() {
		let backend = Backend::<Block>::new_test(1000, 100);
		let blockchain = backend.blockchain();
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		// fork from genesis: 3 prong.
		let a1 = insert_header(&backend, 1, block0, None, Default::default());
		let a2 = insert_header(&backend, 2, a1, None, Default::default());
		let a3 = insert_header(&backend, 3, a2, None, Default::default());

		// fork from genesis: 2 prong.
		let b1 = insert_header(&backend, 1, block0, None, H256::from([1; 32]));
		let b2 = insert_header(&backend, 2, b1, None, Default::default());

		{
			let lca = lowest_common_ancestor(blockchain, a3, b2).unwrap();

			assert_eq!(lca.hash, block0);
			assert_eq!(lca.number, 0);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a1, a3).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a3, a1).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a3).unwrap();

			assert_eq!(lca.hash, a2);
			assert_eq!(lca.number, 2);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a1).unwrap();

			assert_eq!(lca.hash, a1);
			assert_eq!(lca.number, 1);
		}

		{
			let lca = lowest_common_ancestor(blockchain, a2, a2).unwrap();

			assert_eq!(lca.hash, a2);
			assert_eq!(lca.number, 2);
		}
	}

	#[test]
	fn test_tree_route_regression() {
		// NOTE: this is a test for a regression introduced in #3665, the result
		// of tree_route would be erroneously computed, since it was taking into
		// account the `ancestor` in `CachedHeaderMetadata` for the comparison.
		// in this test we simulate the same behavior with the side-effect
		// triggering the issue being eviction of a previously fetched record
		// from the cache, therefore this test is dependent on the LRU cache
		// size for header metadata, which is currently set to 5000 elements.
		let backend = Backend::<Block>::new_test(10000, 10000);
		let blockchain = backend.blockchain();

		let genesis = insert_header(&backend, 0, Default::default(), None, Default::default());

		let block100 = (1..=100).fold(genesis, |parent, n| {
			insert_header(&backend, n, parent, None, Default::default())
		});

		let block7000 = (101..=7000).fold(block100, |parent, n| {
			insert_header(&backend, n, parent, None, Default::default())
		});

		// This will cause the ancestor of `block100` to be set to `genesis` as a side-effect.
		lowest_common_ancestor(blockchain, genesis, block100).unwrap();

		// While traversing the tree we will have to do 6900 calls to
		// `header_metadata`, which will make sure we will exhaust our cache
		// which only takes 5000 elements. In particular, the `CachedHeaderMetadata` struct for
		// block #100 will be evicted and will get a new value (with ancestor set to its parent).
		let tree_route = tree_route(blockchain, block100, block7000).unwrap();

		assert!(tree_route.retracted().is_empty());
	}

	#[test]
	fn test_leaves_with_complex_block_tree() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_leaves_for_backend(backend);
	}

	#[test]
	fn test_children_with_complex_block_tree() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_children_for_backend(backend);
	}

	#[test]
	fn test_blockchain_query_by_number_gets_canonical() {
		let backend: Arc<Backend<substrate_test_runtime_client::runtime::Block>> = Arc::new(Backend::new_test(20, 20));
		substrate_test_runtime_client::trait_tests::test_blockchain_query_by_number_gets_canonical(backend);
	}

	#[test]
	fn test_leaves_pruned_on_finality() {
		let backend: Backend<Block> = Backend::new_test(10, 10);
		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());

		let block1_a = insert_header(&backend, 1, block0, None, Default::default());
		let block1_b = insert_header(&backend, 1, block0, None, [1; 32].into());
		let block1_c = insert_header(&backend, 1, block0, None, [2; 32].into());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block1_a, block1_b, block1_c]);

		let block2_a = insert_header(&backend, 2, block1_a, None, Default::default());
		let block2_b = insert_header(&backend, 2, block1_b, None, Default::default());
		let block2_c = insert_header(&backend, 2, block1_b, None, [1; 32].into());

		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a, block2_b, block2_c, block1_c]);

		backend.finalize_block(BlockId::hash(block1_a), None).unwrap();
		backend.finalize_block(BlockId::hash(block2_a), None).unwrap();

		// leaves at same height stay. Leaves at lower heights pruned.
		assert_eq!(backend.blockchain().leaves().unwrap(), vec![block2_a, block2_b, block2_c]);
	}

	#[test]
	fn test_aux() {
		let backend: Backend<substrate_test_runtime_client::runtime::Block> = Backend::new_test(0, 0);
		assert!(backend.get_aux(b"test").unwrap().is_none());
		backend.insert_aux(&[(&b"test"[..], &b"hello"[..])], &[]).unwrap();
		assert_eq!(b"hello", &backend.get_aux(b"test").unwrap().unwrap()[..]);
		backend.insert_aux(&[], &[&b"test"[..]]).unwrap();
		assert!(backend.get_aux(b"test").unwrap().is_none());
	}

	#[test]
	fn test_finalize_block_with_justification() {
		use sc_client_api::blockchain::{Backend as BlockChainBackend};

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let _ = insert_header(&backend, 1, block0, None, Default::default());

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

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		let block3 = insert_header(&backend, 3, block2, None, Default::default());
		let block4 = insert_header(&backend, 4, block3, None, Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(block0)).unwrap();
			op.mark_finalized(BlockId::Hash(block1), None).unwrap();
			op.mark_finalized(BlockId::Hash(block2), None).unwrap();
			backend.commit_operation(op).unwrap();
		}
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(block2)).unwrap();
			op.mark_finalized(BlockId::Hash(block3), None).unwrap();
			op.mark_finalized(BlockId::Hash(block4), None).unwrap();
			backend.commit_operation(op).unwrap();
		}
	}

	#[test]
	fn test_finalize_non_sequential() {
		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let block1 = insert_header(&backend, 1, block0, None, Default::default());
		let block2 = insert_header(&backend, 2, block1, None, Default::default());
		{
			let mut op = backend.begin_operation().unwrap();
			backend.begin_state_operation(&mut op, BlockId::Hash(block0)).unwrap();
			op.mark_finalized(BlockId::Hash(block2), None).unwrap();
			backend.commit_operation(op).unwrap_err();
		}
	}

	#[test]
	fn header_cht_root_works() {
		use sc_client_api::ProvideChtRoots;

		let backend = Backend::<Block>::new_test(10, 10);

		// insert 1 + SIZE + SIZE + 1 blocks so that CHT#0 is created
		let mut prev_hash = insert_header(&backend, 0, Default::default(), None, Default::default());
		let cht_size: u64 = cht::size();
		for i in 1..1 + cht_size + cht_size + 1 {
			prev_hash = insert_header(&backend, i, prev_hash, None, Default::default());
		}

		let blockchain = backend.blockchain();

		let cht_root_1 = blockchain.header_cht_root(cht_size, cht::start_number(cht_size, 0))
			.unwrap().unwrap();
		let cht_root_2 = blockchain.header_cht_root(cht_size, cht::start_number(cht_size, 0) + cht_size / 2)
			.unwrap().unwrap();
		let cht_root_3 = blockchain.header_cht_root(cht_size, cht::end_number(cht_size, 0))
			.unwrap().unwrap();
		assert_eq!(cht_root_1, cht_root_2);
		assert_eq!(cht_root_2, cht_root_3);
	}

	#[test]
	fn offchain_backends_indexing() {
		use sp_core::offchain::{BlockChainOffchainStorage, OffchainStorage};

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		let offchain_local_storage = offchain_local_storage.at(block0).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), None);

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(b"prefix1", b"key1", b"value1", true);
		let block1 = insert_block(&backend, 1, block0, None, Some(ooc), Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block0).unwrap().get(b"prefix1", b"key1"), None);
		let offchain_local_storage = offchain_local_storage.at(block1).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), Some(b"value1".to_vec()));

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(b"prefix1", b"key1", vec![4u8; 20_000].as_slice(), true);
		let block2 = insert_block(&backend, 2, block1, None, Some(ooc), Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block1).unwrap().get(b"prefix1", b"key1"), Some(b"value1".to_vec()));
		let offchain_local_storage = offchain_local_storage.at(block2).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1").map(|v| v.len()), Some(20_000));

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.remove(b"prefix1", b"key1", true);
		let block3 = insert_block(&backend, 3, block2, None, Some(ooc), Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block0).unwrap().get(b"prefix1", b"key1"), None);
		assert_eq!(offchain_local_storage.at(block1).unwrap().get(b"prefix1", b"key1"), Some(b"value1".to_vec()));
		assert_eq!(offchain_local_storage.at(block2).unwrap().get(b"prefix1", b"key1").map(|v| v.len()), Some(20_000));
		let offchain_local_storage = offchain_local_storage.at(block3).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1").map(|v| v.len()), None);

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.remove(b"prefix1", b"key1", true);
		let block1_b = insert_block(&backend, 1, block0, None, Some(ooc), [1; 32].into());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block0).unwrap().get(b"prefix1", b"key1"), None);
		assert_eq!(offchain_local_storage.at(block1).unwrap().get(b"prefix1", b"key1"), Some(b"value1".to_vec()));
		let offchain_local_storage = offchain_local_storage.at(block1_b).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), None);
	}

	#[test]
	fn offchain_backends_change_new() {
		use sp_core::offchain::{BlockChainOffchainStorage, OffchainStorage};

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_header(&backend, 0, Default::default(), None, Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		let offchain_local_storage = offchain_local_storage.at(block0).unwrap();
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), None);

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(b"prefix1", b"key1", b"value1", true);
		let block1 = insert_block(&backend, 1, block0, None, Some(ooc), Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block0).unwrap().get(b"prefix1", b"key1"), None);
		assert!(!offchain_local_storage.at_new(block0).unwrap().can_update()); // TODO change
		let mut offchain_local_storage = offchain_local_storage.at_new(block1).unwrap();
		assert!(offchain_local_storage.can_update());
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), Some(b"value1".to_vec()));
		offchain_local_storage.set(b"prefix1", b"key1", b"test");
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), Some(b"test".to_vec()));
		offchain_local_storage.set(b"prefix1", b"key2", b"test");
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key2"), Some(b"test".to_vec()));
	}

	#[test]
	#[should_panic(expected = "Concurrency failure for sequential write of offchain storage")]
	fn offchain_backends_change_current_existing() {
		use sp_core::offchain::{BlockChainOffchainStorage, OffchainStorage};

		let backend = Backend::<Block>::new_test(10, 10);

		let mut ooc = OffchainOverlayedChanges::enabled();
		ooc.set(b"prefix1", b"key1", b"value1", true);
		let block0 = insert_block(&backend, 0, Default::default(), None, Some(ooc), Default::default());
		let offchain_local_storage = backend.offchain_local_storage().unwrap();
		assert_eq!(offchain_local_storage.at(block0).unwrap().get(b"prefix1", b"key1"), Some(b"value1".to_vec()));
		let mut offchain_local_storage = offchain_local_storage.at(block0).unwrap();
		assert!(offchain_local_storage.can_update());
		offchain_local_storage.set(b"prefix1", b"key1", b"test");
	}

	#[test]
	fn offchain_backends_change_current_new_value() {
		use sp_core::offchain::{BlockChainOffchainStorage, OffchainStorage};

		let backend = Backend::<Block>::new_test(10, 10);

		let block0 = insert_block(&backend, 0, Default::default(), None, None, Default::default());
		let offchain_local = backend.offchain_local_storage().unwrap();
		let mut offchain_local_storage = offchain_local.at(block0).unwrap();
		assert!(offchain_local_storage.can_update());
		offchain_local_storage.set(b"prefix1", b"key1", b"test");
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), Some(b"test".to_vec()));

		let block1 = insert_block(&backend, 1, block0, None, None, Default::default());
		let mut offchain_local_storage = offchain_local.at(block1).unwrap();
		offchain_local_storage.set(b"prefix1", b"key2", b"test2");
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key2"), Some(b"test2".to_vec()));

		let _block2 = insert_block(&backend, 2, block1, None, None, Default::default());
		// can insert in the past if there is no following change
		let mut offchain_local_storage = offchain_local.at(block1).unwrap();
		assert!(offchain_local_storage.can_update());
		offchain_local_storage.set(b"prefix1", b"key3", b"test3");
		assert!(offchain_local_storage.set_if_possible(b"prefix1", b"key1", b"test1"));
		assert!(!offchain_local_storage.set_if_possible(b"prefix1", b"key2", b"test1"));
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key3"), Some(b"test3".to_vec()));
		assert_eq!(offchain_local_storage.get(b"prefix1", b"key1"), Some(b"test1".to_vec()));
		let mut offchain_local_storage = offchain_local.at(block0).unwrap();
		assert!(offchain_local_storage.can_update());
		assert!(!offchain_local_storage.set_if_possible(b"prefix1", b"key1", b"test1"));
		assert!(!offchain_local_storage.set_if_possible(b"prefix1", b"key2", b"test1"));
		assert!(!offchain_local_storage.set_if_possible(b"prefix1", b"key3", b"test1"));
		assert!(offchain_local_storage.set_if_possible(b"prefix1", b"key4", b"test1"));
	}
}
