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

//! RocksDB-based offchain workers local storage.

use std::{
	collections::HashMap,
	sync::Arc,
};

use crate::{columns, Database, DbHash, Transaction};
use parking_lot::{Mutex, RwLock};
use historied_db::{Latest, Management, ManagementRef, UpdateResult,
	management::tree::{TreeManagementStorage, ForkPlan},
	historied::tree::Tree,
	backend::nodes::{NodesMeta, NodeStorage, NodeStorageMut, Node, ContextHead},
};
use codec::{Decode, Encode, Codec};
use log::error;

/// Offchain local storage
#[derive(Clone)]
pub struct LocalStorage {
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

type ChangesJournal<Db> = historied_db::management::JournalForMigrationBasis<
	(u32, u32),
	Vec<u8>,
	Db,
	crate::historied_tree_bindings::LocalOffchainDelete,
>;

pub(crate) type ChangesJournalSync = Arc<Mutex<ChangesJournal<historied_db::simple_db::SerializeDBDyn>>>;

/// Offchain local storage with blockchain historied storage.
#[derive(Clone)]
pub struct BlockChainLocalStorage<H: Ord, S: TreeManagementStorage> {
	historied_management: Arc<RwLock<crate::TreeManagement<H, S>>>,
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
	ordered_db: Arc<Mutex<historied_db::simple_db::SerializeDBDyn>>,
	changes_journals: ChangesJournalSync,
}

/// For migration this will update a pending change layer to support
/// transaction.
pub struct TransactionalConsumer<H: Ord, S: TreeManagementStorage> {
	/// Storage to use.
	pub storage: BlockChainLocalStorage<H, S>,
	/// Transaction to update on migrate.
	pub pending: Arc<RwLock<Transaction<DbHash>>>,
}

impl<H, S> historied_db::management::ManagementConsumer<H, crate::TreeManagement<H, S>> for TransactionalConsumer<H, S>
	where
		H: Ord + Clone + Codec + Send + Sync + 'static,
		S: TreeManagementStorage + 'static,
{
	fn migrate(&self, migrate: &mut historied_db::Migrate<H, crate::TreeManagement<H, S>>) {
		let mut keys = std::collections::BTreeSet::<Vec<u8>>::new();
		let (prune, changes) = migrate.migrate().touched_state();
		// this db is transactional.
		let db = migrate.management().ser();
		// using a new instance (transactional db is a different type).
		// This means some ununsed cache state can remain.
		let mut journals = ChangesJournal::from_db(db);
		if let Some(pruning) = prune {
			journals.remove_changes_before(db, &(pruning, Default::default()), &mut keys);
		}

		for state in changes {
			let state = state.clone();
			let state = (state.1, state.0);
			if let Some(removed) = journals.remove_changes_at(db, &state) {
				for key in removed {
					keys.insert(key);
				}
			}
		}

		if keys.is_empty() {
			return;
		}

		let block_nodes = BlockNodes::new(self.storage.db.clone());
		let branch_nodes = BranchNodes::new(self.storage.db.clone());

		let mut pending = self.pending.write();
		for k in keys {
			let column = crate::columns::OFFCHAIN;
			let init_nodes = ContextHead {
				key: k.clone(),
				backend: block_nodes.clone(),
				node_init_from: (),
			};
			let init = ContextHead {
				key: k.clone(),
				backend: branch_nodes.clone(),
				node_init_from: init_nodes.clone(),
			};

			let k = k.as_slice();
			let histo: HValue = if let Some(histo) = self.storage.db.get(column, k) {
				historied_db::DecodeWithContext::decode_with_context(&mut &histo[..], &(init.clone(), init_nodes.clone()))
					.expect("Bad encoded value in db, closing")
			} else {
				continue;
			};

			let mut new_value = histo;
			use historied_db::historied::Value;
			let neutral = None;
			match new_value.migrate(migrate.migrate(), Some(&neutral)) {
				historied_db::UpdateResult::Changed(()) => {
					use historied_db::Trigger;
					new_value.trigger_flush();
					pending.set_from_vec(column, k, new_value.encode());
				},
				historied_db::UpdateResult::Cleared(()) => {
					use historied_db::Trigger;
					new_value.trigger_flush();
					pending.remove(column, k);
				},
				historied_db::UpdateResult::Unchanged => (),
			}
		}

		block_nodes.apply_transaction(&mut pending);
		branch_nodes.apply_transaction(&mut pending);
	}
}

/// Offchain local storage for a given block.
#[derive(Clone)]
pub struct BlockChainLocalAt {
	db: Arc<dyn Database<DbHash>>,
	block_nodes: BlockNodes,
	branch_nodes: BranchNodes,
	at_read: ForkPlan<u32, u64>,
	at_write: Option<Latest<(u32, u64)>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
	ordered_db: Arc<Mutex<historied_db::simple_db::SerializeDBDyn>>,
	changes_journals: ChangesJournalSync,
	skip_journalize: bool,
}

/// Offchain local storage for a given block,
/// and for new state (without concurrency handling).
#[derive(Clone)]
pub struct BlockChainLocalAtNew(BlockChainLocalAt);

impl std::fmt::Debug for LocalStorage {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("LocalStorage")
			.finish()
	}
}

impl<H: Ord, S: TreeManagementStorage> std::fmt::Debug for BlockChainLocalStorage<H, S> {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("BlockChainLocalStorage")
			.finish()
	}
}

impl LocalStorage {
	/// Create new offchain storage for tests (backed by memorydb)
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db = sp_database::as_database(db);
		Self::new(db as _)
	}

	/// Create offchain local storage with given `KeyValueDB` backend.
	pub fn new(db: Arc<dyn Database<DbHash>>) -> Self {
		Self {
			db,
			locks: Default::default(),
		}
	}
}

impl<H: Ord, S: TreeManagementStorage> BlockChainLocalStorage<H, S> {
	/// Create offchain local storage with given `KeyValueDB` backend.
	pub fn new(
		db: Arc<dyn Database<DbHash>>,
		historied_management: Arc<RwLock<crate::TreeManagement<H, S>>>,
		journals_db: historied_db::simple_db::SerializeDBDyn,
	) -> Self {
		let journals = historied_db::management::JournalForMigrationBasis::from_db(&journals_db);
		Self {
			historied_management,
			db,
			locks: Default::default(),
			ordered_db: Arc::new(Mutex::new(journals_db)),
			changes_journals: Arc::new(Mutex::new(journals)),
		}
	}
}

impl<H: Ord> BlockChainLocalStorage<H, ()> {
	/// Create new offchain storage for tests (backed by memorydb)
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		let db = kvdb_memorydb::create(crate::utils::NUM_COLUMNS);
		let db: Arc<dyn Database<DbHash>> = sp_database::as_database(db);
		let historied_management = Arc::new(RwLock::new(crate::TreeManagement::default()));
		let ordered = sp_database::RadixTreeDatabase::new(db.clone());
		let ordered = Box::new(crate::DatabaseStorage(ordered));
		Self::new(db as _, historied_management, ordered)
	}
}

impl sp_core::offchain::OffchainStorage for LocalStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		let mut tx = Transaction::new();
		tx.set(columns::OFFCHAIN, &key, value);

		if let Err(err) = self.db.commit(tx) {
			error!("Error setting on local storage: {}", err)
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		let mut tx = Transaction::new();
		tx.remove(columns::OFFCHAIN, &key);

		if let Err(err) = self.db.commit(tx) {
			error!("Error removing on local storage: {}", err)
		}
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.db.get(columns::OFFCHAIN, &key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key: Vec<u8> = prefix.iter().chain(item_key).cloned().collect();
		let key_lock = {
			let mut locks = self.locks.lock();
			locks.entry(key.clone()).or_default().clone()
		};

		let is_set;
		{
			let _key_guard = key_lock.lock();
			let val = self.db.get(columns::OFFCHAIN, &key);
			is_set = val.as_ref().map(|x| &**x) == old_value;

			if is_set {
				self.set(prefix, item_key, new_value)
			}
		}

		// clean the lock map if we're the only entry
		let mut locks = self.locks.lock();
		{
			drop(key_lock);
			let key_lock = locks.get_mut(&key);
			if let Some(_) = key_lock.and_then(Arc::get_mut) {
				locks.remove(&key);
			}
		}
		is_set
	}
}

impl<H, S> sp_core::offchain::BlockChainOffchainStorage for BlockChainLocalStorage<H, S>
	where
		H: Send + Sync + Ord + Clone + Codec,
		S: TreeManagementStorage + Send + Sync + Clone,
{
	type BlockId = H;
	type OffchainStorage = BlockChainLocalAt;
	type OffchainStorageNew = BlockChainLocalAtNew;

	fn at(&self, id: Self::BlockId) -> Option<Self::OffchainStorage> {
		let db_state = self.historied_management.write().get_db_state(&id);
		if let Some(at_read) = db_state {
			let at_write = self.historied_management.write().get_db_state_mut(&id);
			Some(BlockChainLocalAt {
				db: self.db.clone(),
				branch_nodes: BranchNodes::new(self.db.clone()),
				block_nodes: BlockNodes::new(self.db.clone()),
				at_read,
				at_write,
				locks: self.locks.clone(),
				ordered_db: self.ordered_db.clone(),
				changes_journals: self.changes_journals.clone(),
				skip_journalize: !S::JOURNAL_DELETE,
			})
		} else {
			None
		}
	}
	fn at_new(&self, id: Self::BlockId) -> Option<Self::OffchainStorageNew> {
		self.at(id).map(|at| BlockChainLocalAtNew(at))
	}
	fn latest(&self) -> Option<Self::BlockId> {
		self.historied_management.write().latest_external_state()
	}
}

impl BlockChainLocalAt {
	/// Under current design, the local update is only doable when we
	/// are at a latest block, this function tells if we can use
	/// function that modify state.
	pub fn can_update(&self) -> bool {
		true
	}

	/// When doing batch update we can skip journalize,
	/// and produce the journalize item at once later.
	pub fn skip_journalize(&mut self) {
		self.skip_journalize = true;
	}
}

impl BlockChainLocalAtNew {
	/// Does the current state allows chain update attempt.
	pub fn can_update(&self) -> bool {
		self.0.at_write.is_some()
	}

	/// When doing batch update we can skip journalize,
	/// and produce the journalize item at once later.
	pub fn skip_journalize(&mut self) {
		self.0.skip_journalize = true;
	}
}


impl sp_core::offchain::OffchainStorage for BlockChainLocalAt {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		if !self.set_if_possible(prefix, key, value) {
			panic!("Concurrency failure for sequential write of offchain storage");
		}
	}

	fn set_if_possible(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) -> bool {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		match self.modify(
			prefix,
			key,
			test,
			Some(value),
			false,
		) {
			Ok(_) => true,
			Err(ModifyError::AlreadyWritten) => false,
			Err(ModifyError::NoWriteState) => panic!("Cannot write at latest"),
			Err(ModifyError::DbWrite) => panic!("Offchain local db commit failure"),
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.modify(
			prefix,
			key,
			test,
			None,
			false,
		).expect("Concurrency failure for sequential write of offchain storage");
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		// TODO consider using types for a totally encoded items.
		let key: Vec<u8> = prefix
			.iter()
			.chain(std::iter::once(&b'/'))
			.chain(key)
			.cloned()
			.collect();
		self.db.get(columns::OFFCHAIN, &key)
			.and_then(|v| {
				let init_nodes = ContextHead {
					key: key.clone(),
					backend: self.block_nodes.clone(),
					node_init_from: (),
				};
				let init = ContextHead {
					key,
					backend: self.branch_nodes.clone(),
					node_init_from: init_nodes.clone(),
				};
				let v: Option<HValue> = historied_db::DecodeWithContext::decode_with_context(&mut &v[..], &(init, init_nodes));
				v
			}.and_then(|h| {
				use historied_db::historied::ValueRef;
				h.get(&self.at_read).flatten()
			}))
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			false,
		).expect("Concurrency failure for sequential write of offchain storage")
	}
}

impl sp_core::offchain::OffchainStorage for BlockChainLocalAtNew {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		if !self.set_if_possible(prefix, key, value) {
			panic!("Concurrency failure for sequential write of offchain storage");
		}
	}

	fn set_if_possible(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) -> bool {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		match self.0.modify(
			prefix,
			key,
			test,
			Some(value),
			true,
		) {
			Ok(_) => true,
			Err(ModifyError::AlreadyWritten) => false,
			Err(ModifyError::NoWriteState) => panic!("Cannot write at latest"),
			Err(ModifyError::DbWrite) => panic!("Offchain local db commit failure"),
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		self.0.modify(
			prefix,
			key,
			test,
			None,
			true,
		).expect("Concurrency failure for sequential write of offchain storage");
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.0.get(prefix, key)
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		self.0.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			true,
		).expect("Concurrency failure for sequential write of offchain storage")
	}
}

#[derive(Debug)]
enum ModifyError {
	NoWriteState,
	AlreadyWritten,
	DbWrite,
}

impl BlockChainLocalAt {
	fn modify(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		condition: Option<impl Fn(Option<&[u8]>) -> bool>,
		new_value: Option<&[u8]>,
		is_new: bool,
	) -> Result<bool, ModifyError> {
		if self.at_write.is_none() && is_new {
			return Err(ModifyError::NoWriteState);
		}
		let key: Vec<u8> = prefix
			.iter()
			.chain(std::iter::once(&b'/'))
			.chain(item_key)
			.cloned()
			.collect();
		let key_lock = {
			let mut locks = self.locks.lock();
			locks.entry(key.clone()).or_default().clone()
		};

		let result = || -> Result<bool, ModifyError> {
			let at_write_inner;
			let at_write = if is_new {
				self.at_write.as_ref().expect("checked above")
			} else {
				at_write_inner = Latest::unchecked_latest(self.at_read.latest_index());
				&at_write_inner
			};
			let is_set;
			{
				let _key_guard = key_lock.lock();
				let histo = self.db.get(columns::OFFCHAIN, &key)
					.and_then(|v| {
						let init_nodes = ContextHead {
							key: key.clone(),
							backend: self.block_nodes.clone(),
							node_init_from: (),
						};
						let init = ContextHead {
							key: key.clone(),
							backend: self.branch_nodes.clone(),
							node_init_from: init_nodes.clone(),
						};
						let v: Option<HValue> = historied_db::DecodeWithContext::decode_with_context(
							&mut &v[..],
							&(init, init_nodes),
						);
						v
					});
				let val = histo.as_ref().and_then(|h| {
					use historied_db::historied::ValueRef;
					h.get(&self.at_read).flatten()
				});

				is_set = condition.map(|c| c(val.as_ref().map(|v| v.as_slice()))).unwrap_or(true);

				if is_set {
					use historied_db::historied::Value;
					let is_insert = new_value.is_some();
					let new_value = new_value.map(|v| v.to_vec());
					let (new_value, update_result) = if let Some(mut histo) = histo {
						let update_result = if is_new {
							histo.set(new_value, at_write)
						} else {
							use historied_db::historied::ConditionalValueMut;
							use historied_db::historied::StateIndex;
							if let Some(update_result) = histo.set_if_possible_no_overwrite(
								new_value,
								at_write.index_ref(),
							) {
								update_result
							} else {
								return Err(ModifyError::AlreadyWritten);
							}
						};
						if let &UpdateResult::Unchanged = &update_result {
							(Vec::new(), update_result)
						} else {
							use historied_db::Trigger;
							histo.trigger_flush();
							(histo.encode(), update_result)
						}
					} else {
						if is_insert {
							let init_nodes = ContextHead {
								key: key.clone(),
								backend: self.block_nodes.clone(),
								node_init_from: (),
							};
							let init = ContextHead {
								key: key.clone(),
								backend: self.branch_nodes.clone(),
								node_init_from: init_nodes.clone(),
							};

							(HValue::new(
									new_value,
									at_write,
									(init, init_nodes),
								).encode(), UpdateResult::Changed(()))
						} else {
							// nothing to delete
							(Default::default(), UpdateResult::Unchanged)
						}
					};
					match update_result {
						UpdateResult::Changed(()) => {
							let mut tx = Transaction::new();
							tx.set(columns::OFFCHAIN, &key, new_value.as_slice());

							if self.db.commit(tx).is_err() {
								return Err(ModifyError::DbWrite);
							};
						},
						UpdateResult::Cleared(()) => {
							let mut tx = Transaction::new();
							tx.remove(columns::OFFCHAIN, &key);

							if self.db.commit(tx).is_err() {
								return Err(ModifyError::DbWrite);
							};
						},
						UpdateResult::Unchanged => (),
					}
					match update_result {
						UpdateResult::Unchanged => (),
						UpdateResult::Changed(())
						| UpdateResult::Cleared(()) => {
							if !self.skip_journalize {
								use std::ops::DerefMut;
								let at_write = at_write.latest().clone();
								// Needed for encoded ordering against block index
								let at_write = (at_write.1, at_write.0);
								self.changes_journals.lock().add_changes(
									self.ordered_db.lock().deref_mut(),
									at_write,
									vec![key.clone()],
									false,
								)
							}
						},
					}

				}

			}
			Ok(is_set)
		}();

		// clean the lock map if we're the only entry
		let mut locks = self.locks.lock();
		{
			drop(key_lock);
			let key_lock = locks.get_mut(&key);
			if let Some(_) = key_lock.and_then(Arc::get_mut) {
				locks.remove(&key);
			}
		}
		result
	}
}

/// Multiple node splitting strategy based on content
/// size.
pub struct MetaBranches;

/// Multiple node splitting strategy based on content
/// size.
pub struct MetaBlocks;

impl NodesMeta for MetaBranches {
	const APPLY_SIZE_LIMIT: bool = true;
	const MAX_NODE_LEN: usize = 2048; // This should be benched.
	const MAX_NODE_ITEMS: usize = 8;
	const STORAGE_PREFIX: &'static [u8] = b"tree_mgmt/branch_nodes";
}

impl NodesMeta for MetaBlocks {
	const APPLY_SIZE_LIMIT: bool = true;
	// This needs to be less than for `MetaBranches`, the point is to
	// be able to store multiple branche in the immediate storage and
	// avoid having a single branch occupy the whole item.
	const MAX_NODE_LEN: usize = 512;
	const MAX_NODE_ITEMS: usize = 4;
	const STORAGE_PREFIX: &'static [u8] = b"tree_mgmt/block_nodes";
}

/// Node backend for blocks values
/// when the block history grows too big.
#[derive(Clone)]
pub struct BlockNodes(DatabasePending);

/// Node backend for branch values
/// when the branch history grows too big.
#[derive(Clone)]
pub struct BranchNodes(DatabasePending);

#[derive(Clone)]
struct DatabasePending {
	pending: Arc<RwLock<HashMap<Vec<u8>, Option<Vec<u8>>>>>,
	database: Arc<dyn Database<DbHash>>,
}

impl DatabasePending {
	fn clear_and_extract_changes(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>> {
		std::mem::replace(&mut self.pending.write(), HashMap::new())
	}

	fn apply_transaction(
		&self,
		col: sp_database::ColumnId,
		transaction: &mut Transaction<DbHash>,
	) {
		let pending = self.clear_and_extract_changes();
		for (key, change) in pending {
			if let Some(value) = change {
				transaction.set_from_vec(col, &key, value);
			} else {
				transaction.remove(col, &key);
			}
		}
	}

	fn read(&self, col: sp_database::ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		if let Some(pending) = self.pending.read().get(key).cloned() {
			pending
		} else {
			self.database.get(col, key)
		}
	}

	fn write(&self, key: Vec<u8>, value: Vec<u8>) {
		self.pending.write().insert(key, Some(value));
	}

	fn remove(&self, key: Vec<u8>) {
		self.pending.write().insert(key, None);
	}
}

impl BlockNodes {
	/// Initialize from clonable pointer to backend database.
	pub fn new(database: Arc<dyn Database<DbHash>>) -> Self {
		BlockNodes(DatabasePending {
			pending: Arc::new(RwLock::new(HashMap::new())),
			database,
		})
	}

	/// Flush pending changes into a database transaction.
	pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
		self.0.apply_transaction(crate::columns::AUX, transaction)
	}
}

impl BranchNodes {
	/// Initialize from clonable pointer to backend database.
	pub fn new(database: Arc<dyn Database<DbHash>>) -> Self {
		BranchNodes(DatabasePending {
			pending: Arc::new(RwLock::new(HashMap::new())),
			database,
		})
	}

	/// Flush pending changes into a database transaction.
	pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
		self.0.apply_transaction(crate::columns::AUX, transaction)
	}
}

impl NodeStorage<Option<Vec<u8>>, u64, LinearBackendInner, MetaBlocks> for BlockNodes {
	fn get_node(&self, reference_key: &[u8], relative_index: u64) -> Option<LinearNode> {
		let key = Self::vec_address(reference_key, relative_index);
		self.0.read(crate::columns::AUX, &key).and_then(|value| {
			// use encoded len as size (this is bigger than the call to estimate size
			// but not really an issue, otherwhise could adjust).
			let reference_len = value.len();

			let input = &mut value.as_slice();
			LinearBackendInner::decode(input).ok().map(|data| Node::new(
				data,
				reference_len,
			))
		})
	}
}

impl NodeStorageMut<Option<Vec<u8>>, u64, LinearBackendInner, MetaBlocks> for BlockNodes {
	fn set_node(&mut self, reference_key: &[u8], relative_index: u64, node: &LinearNode) {
		let key = Self::vec_address(reference_key, relative_index);
		let encoded = node.inner().encode();
		self.0.write(key, encoded);
	}
	fn remove_node(&mut self, reference_key: &[u8], relative_index: u64) {
		let key = Self::vec_address(reference_key, relative_index);
		self.0.remove(key);
	}
}

impl NodeStorage<BranchLinear, u32, TreeBackendInner, MetaBranches> for BranchNodes {
	fn get_node(&self, reference_key: &[u8], relative_index: u32) -> Option<TreeNode> {
		use historied_db::DecodeWithContext;
		let key = Self::vec_address(reference_key, relative_index);
		self.0.read(crate::columns::AUX, &key).and_then(|value| {
			// use encoded len as size (this is bigger than the call to estimate size
			// but not an issue, otherwhise could adjust).
			let reference_len = value.len();

			let block_nodes = BlockNodes(self.0.clone());
			let input = &mut value.as_slice();
			TreeBackendInner::decode_with_context(
				input,
				&ContextHead {
					key: reference_key.to_vec(),
					backend: block_nodes,
					node_init_from: (),
				},
			).map(|data| Node::new (
				data,
				reference_len,
			))
		})
	}
}

impl NodeStorageMut<BranchLinear, u32, TreeBackendInner, MetaBranches> for BranchNodes {
	fn set_node(&mut self, reference_key: &[u8], relative_index: u32, node: &TreeNode) {
		let key = Self::vec_address(reference_key, relative_index);
		let encoded = node.inner().encode();
		self.0.write(key, encoded);
	}
	fn remove_node(&mut self, reference_key: &[u8], relative_index: u32) {
		let key = Self::vec_address(reference_key, relative_index);
		self.0.remove(key);
	}
}

// Values are stored in memory in Vec like structure
type LinearBackendInner = historied_db::backend::in_memory::MemoryOnly<
	Option<Vec<u8>>,
	u64,
>;

// A multiple nodes wraps multiple vec like structure
type LinearBackend = historied_db::backend::nodes::Head<
	Option<Vec<u8>>,
	u64,
	LinearBackendInner,
	MetaBlocks,
	BlockNodes,
	(),
>;

// Nodes storing these
type LinearNode = historied_db::backend::nodes::Node<
	Option<Vec<u8>>,
	u64,
	LinearBackendInner,
	MetaBlocks,
>;

// Branch
type BranchLinear = historied_db::historied::linear::Linear<Option<Vec<u8>>, u64, LinearBackend>;

// Branch are stored in memory
type TreeBackendInner = historied_db::backend::in_memory::MemoryOnly<
	BranchLinear,
	u32,
>;

// Head of branches
type TreeBackend = historied_db::backend::nodes::Head<
	BranchLinear,
	u32,
	TreeBackendInner,
	MetaBranches,
	BranchNodes,
	ContextHead<BlockNodes, ()>
>;

// Node with branches
type TreeNode = historied_db::backend::nodes::Node<
	BranchLinear,
	u32,
	TreeBackendInner,
	MetaBranches,
>;

/// Historied value with multiple branches.
///
/// Indexed by u32 for both branches and value into branches.
/// Value are in memory but serialized as splitted node.
/// Each node contains multiple values or multiple branch head of nodes.
pub type HValue = Tree<u32, u64, Option<Vec<u8>>, TreeBackend, LinearBackend>;

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::offchain::OffchainStorage;

	#[test]
	fn should_compare_and_set_and_clear_the_locks_map() {
		let mut storage = LocalStorage::new_test();
		let prefix = b"prefix";
		let key = b"key";
		let value = b"value";

		storage.set(prefix, key, value);
		assert_eq!(storage.get(prefix, key), Some(value.to_vec()));

		assert_eq!(storage.compare_and_set(prefix, key, Some(value), b"asd"), true);
		assert_eq!(storage.get(prefix, key), Some(b"asd".to_vec()));
		assert!(storage.locks.lock().is_empty(), "Locks map should be empty!");
	}

	#[test]
	fn should_compare_and_set_on_empty_field() {
		let mut storage = LocalStorage::new_test();
		let prefix = b"prefix";
		let key = b"key";

		assert_eq!(storage.compare_and_set(prefix, key, None, b"asd"), true);
		assert_eq!(storage.get(prefix, key), Some(b"asd".to_vec()));
		assert!(storage.locks.lock().is_empty(), "Locks map should be empty!");
	}

}
