// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Offchain workers local storage and historied storage.

use std::{collections::HashMap, sync::Arc};

use crate::{columns, Database, DbHash, Transaction};
use parking_lot::{Mutex, MutexGuard, RwLock};
use historied_db::{Latest, UpdateResult,
	management::{Management, ManagementMut, ForkableManagement},
	management::tree::{TreeManagementStorage, ForkPlan},
	DecodeWithContext,
	historied::DataMut,
	mapped_db::{TransactionalMappedDB, MappedDBDyn},
	backend::nodes::ContextHead,
};
use sp_runtime::traits::{
	Block as BlockT, Header, Zero,
};
use codec::Encode;
use log::error;
use crate::tree_management::{TreeManagement, TreeManagementSync};
use sp_blockchain::Result as ClientResult;
use crate::historied_nodes::nodes_database::{BlockNodes, BranchNodes, NODES_COL};
use crate::historied_nodes::nodes_backend::Context;
use sp_core::offchain::OffchainOverlayedChange;

/// Offchain local storage
#[derive(Clone)]
pub struct LocalStorage {
	db: Arc<dyn Database<DbHash>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
}

impl std::fmt::Debug for LocalStorage {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("LocalStorage")
			.finish()
	}
}

impl LocalStorage {
	/// Create new offchain storage for tests (backed by memorydb)
	#[cfg(any(feature = "test-helpers", test))]
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

impl sp_core::offchain::OffchainStorage for LocalStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let mut tx = Transaction::new();
		tx.set(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key), value);

		if let Err(err) = self.db.commit(tx) {
			error!("Error setting on local storage: {}", err)
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let mut tx = Transaction::new();
		tx.remove(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key));

		if let Err(err) = self.db.commit(tx) {
			error!("Error removing on local storage: {}", err)
		}
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		self.db.get(columns::OFFCHAIN, &concatenate_prefix_and_key(prefix, key))
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key = concatenate_prefix_and_key(prefix, item_key);
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

/// Concatenate the prefix and key to create an offchain key in the db.
pub(crate) fn concatenate_prefix_and_key(prefix: &[u8], key: &[u8]) -> Vec<u8> {
	prefix
		.iter()
		.chain(key.into_iter())
		.cloned()
		.collect()
}

static_instance!(JournalChanges, b"\x08\x00\x00\x00offchain/journal_delete");

/// Offchain local storage with blockchain historied storage.
#[derive(Clone)]
pub struct BlockChainLocalStorage<Block: BlockT, S: TreeManagementStorage + 'static> {
	/// Historied management use by snapshot db.
	/// Currently snapshot db is single consumer, so init and clear
	/// operation also act on `historied_management`.
	/// This use a transactional layer in storage.
	historied_management: TreeManagementSync<Block, S>,
	/// Database with historied items. Warning, this is non transactional.
	/// Also for accessing nodes.
	db: Arc<dyn Database<DbHash>>,
	/// Locks applied to specific key of the db.
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
	// With blockchain local if concurrency is not
	// handled correctly by the offchain workers
	// the historied data stored will get in an
	// inconsistent state.
	// Eg a write creates a new head node, but another
	// does not, then if the other write last we will
	// got a loose backend node.
	// Note that for access only this is rather safe
	// since only a garbage collection can make
	// the query invalid, but garbage collection
	// does not run concurently with offchain workers.
	// Therefore we allow to lock the state
	// even when not modifying with `compare_and_set`.
	safe_offchain_locks: bool,
}

impl<B: BlockT, S: TreeManagementStorage> std::fmt::Debug for BlockChainLocalStorage<B, S> {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("BlockChainLocalStorage")
			.finish()
	}
}

impl<Block, S> BlockChainLocalStorage<Block, S>
	where
		Block: BlockT,
		S: TreeManagementStorage,
{
	fn nodes_db(&self) -> &Arc<dyn Database<DbHash>> {
		&self.db
	}
}

impl<Block, S> BlockChainLocalStorage<Block, S>
	where
		Block: BlockT,
		S: TreeManagementStorage<Storage = TransactionalMappedDB<MappedDBDyn>> + Clone,
{
	/// Create offchain local storage with given `KeyValueDB` backend.
	pub fn new(
		db: Arc<dyn Database<DbHash>>,
		historied_management: TreeManagementSync<Block, S>,
		safe_offchain_locks: bool,
	) -> Self {
		let mut offchain_db = Self {
			historied_management,
			db,
			locks: Default::default(),
			safe_offchain_locks,
		};
		let storage = offchain_db.clone();
		let pending = offchain_db.historied_management.inner.read().consumer_transaction.clone();
		offchain_db.historied_management.register_consumer(Box::new(TransactionalConsumer {
			storage,
			pending,
		}));
		offchain_db
	}

	/// Get handle to modification for a given state (for block import). 
	pub fn new_block_historied_db_mut(
		&self,
		parent: &Block::Hash,
		at: &Block::Hash,
	) -> ClientResult<Option<HistoriedDBMut<Arc<dyn Database<DbHash>>>>> {
		let (_query_plan, update_plan) = self.historied_management.register_new_block(&parent, &at)?;
		Ok(Some(HistoriedDBMut {
			current_state: update_plan,
			db: self.db.clone(),
			nodes_db: self.db.clone(),
		}))
	}

	/// Access blockchain local db with read and write capabilities for a given state.
	pub fn get_local_at(
		&self,
		at: Option<&Block::Hash>,
	) -> Option<BlockChainLocalAt<Block, S>> {
		let default_hash;
		let mut management = self.historied_management.inner.write();
		let (at, current_state) = if let Some(hash) = at {
			(hash, management.instance.get_db_state(&hash))
		} else {
			// genesis
			let state = management.instance.latest_state_fork();
			// starting a new state at default hash is not strictly necessary,
			// but we lack a historied db primitive to get default query state
			// on (0, 0).
			// TODO this looks quite unsound (except for read only usage).
			default_hash = Default::default();
			(&default_hash, management.instance.get_db_state(&default_hash)
				.or_else(|| management.instance.append_external_state(default_hash.clone(), &state)
					.and_then(|_| management.instance.get_db_state(&default_hash))
				))
		};
		if let Some(at_read) = current_state {
			let at_write = management.instance.get_db_state_mut(at);
			Some(BlockChainLocalAt {
				db: self.db.clone(),
				at_read,
				at_write,
				historied_management: self.historied_management.clone(),
				locks: self.locks.clone(),
				safe_offchain_locks: self.safe_offchain_locks,
			})
		} else {
			None
		}
	}

	/// Process block changes, and update a input transaction.
	pub fn apply_block_change(
		&self,
		operation: &mut crate::BlockImportOperation<Block>,
		transaction: &mut Transaction<DbHash>,
	) -> ClientResult<()> {
		let mut is_genesis = false;
		let hashes = operation.pending_block.as_ref().map(|pending_block| {
			if pending_block.header.number().is_zero() {
				is_genesis = true;
			}
			let hash = pending_block.header.hash();
			let parent_hash = *pending_block.header.parent_hash();
			(hash, parent_hash)
		});

		let mut historied = if let Some((hash, parent_hash)) = hashes {
			// Ensure pending layer is clean
			self.historied_management.clear_changes();
			self.new_block_historied_db_mut(&parent_hash, &hash)?
		} else {
			None
		};

		// Do not journal genesis.
		let mut management = (!is_genesis)
			.then(|| self.historied_management.inner.write());
		let journals = management.as_mut().map(|management| management.instance.ser());
		let mut journal_keys = journals.is_some().then(|| Vec::new());

		for ((prefix, key), value_operation) in operation.offchain_storage_updates.drain(..) {
			let key = crate::offchain::concatenate_prefix_and_key(&prefix, &key);
			match value_operation {
				OffchainOverlayedChange::SetValue(val) =>
					transaction.set_from_vec(columns::OFFCHAIN, &key, val),
				OffchainOverlayedChange::Remove =>
					transaction.remove(columns::OFFCHAIN, &key),
				OffchainOverlayedChange::SetLocalValue(val) => {
					historied.as_mut().map(|historied_db|
						historied_db.update_single(key, Some(val), transaction, journal_keys.as_mut())
					);
				},
				OffchainOverlayedChange::RemoveLocal => {
					historied.as_mut().map(|historied_db|
						historied_db.update_single(key, None, transaction, journal_keys.as_mut())
					);
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
			let mut journals = ChangesJournal::from_db(ordered_db);
			journals.add_changes(
				ordered_db,
				rev_index(historied.current_state.latest()),
				journal_keys,
				// New block, no need for fetch
				// (when executed twice we overwrite existing but journal should be the smae).
				true,
			)
		}

		let mut management = management.unwrap_or_else(||
			self.historied_management.inner.write()
		);
		// write management state changes (after changing values because change
		// journal is using historied management db).
		TreeManagementSync::<Block, _>::apply_historied_management_changes(
			&mut management.instance,
			transaction,
		);

		Ok(())
	}

	/// Access underlying historied management
	pub fn historied_management(&self) -> &TreeManagementSync<Block, S> {
		&self.historied_management
	}
}

impl<B, S> sp_core::offchain::BlockChainOffchainStorage for BlockChainLocalStorage<B, S>
	where
		B: BlockT,
		S: TreeManagementStorage<Storage = TransactionalMappedDB<MappedDBDyn>> + Clone,
{
	type BlockId = B::Hash;
	type OffchainStorage = BlockChainLocalAt<B, S>;

	fn at(&self, id: Self::BlockId) -> Option<Self::OffchainStorage> {
		self.get_local_at(Some(&id))
	}

	fn latest(&self) -> Option<Self::BlockId> {
		self.historied_management.inner.write().instance.latest_external_state()
	}
}

type ChangesJournal<Db> = historied_db::management::JournalForMigrationBasis<
	// Note that it is reversed state, we use block number first for ordering consideration.
	(u64, u32),
	Vec<u8>,
	Db,
	JournalChanges,
>;

fn rev_index(index: &(u32, u64)) -> (u64, u32) {
	(index.1, index.0)
}

mod nodes_backend {
	use historied_db::backend::nodes::NodesMeta;

	/// Multiple node splitting strategy based on content
	/// size.
	#[derive(Clone, Copy)]
	pub struct MetaBranches;

	/// Multiple node splitting strategy based on content
	/// size.
	#[derive(Clone, Copy)]
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
}

mod nodes_definition {
	use historied_db::{
		historied::Data,
		historied::tree::Tree,
		management::tree::ForkPlan,
	};
	use super::nodes_backend::{MetaBlocks, MetaBranches};
	use crate::historied_nodes::nodes_backend::{TreeBackend, LinearBackend};

	/// Historied value with multiple branches.
	///
	/// Indexed by u32 branches and u64 for blocks.
	/// Value are in memory but serialized as splitted node.
	/// Each node contains multiple values or multiple branch head of nodes.
	pub type HValue = Tree<
		u32,
		u64,
		Option<Vec<u8>>,
		TreeBackend<Option<Vec<u8>>, MetaBranches, MetaBlocks>,
		LinearBackend<Option<Vec<u8>>, MetaBlocks>,
	>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Option<Vec<u8>> {
		v.get(current_state).flatten()
	}
}

/// Historied value for offchain.
pub struct HValue(nodes_definition::HValue, BranchNodes, BlockNodes);

impl HValue {
	/// Get context for the nodes backend of this value.
	pub fn build_context(key: &[u8], nodes_db: &Arc<dyn Database<DbHash>>) -> (Context, BranchNodes, BlockNodes) {
		let block_nodes = BlockNodes::new(nodes_db.clone(), NODES_COL);
		let branch_nodes = BranchNodes::new(nodes_db.clone(), NODES_COL);

		let init_nodes = ContextHead {
			key: key.to_vec(),
			backend: block_nodes.clone(),
			encoded_indexes: Vec::new(),
			node_init_from: (),
		};
		let init = ContextHead {
			key: key.to_vec(),
			backend: branch_nodes.clone(),
			encoded_indexes: Vec::new(),
			node_init_from: init_nodes.clone(),
		};
		((init, init_nodes), branch_nodes, block_nodes)
	}

	/// Apply local nodes backend change to transaction.
	pub fn apply_nodes_backend_to_transaction(&mut self, transaction: &mut Transaction<DbHash>) {
		let HValue(inner, branches, blocks) = self; 

		use historied_db::Trigger;
		inner.trigger_flush();
		branches.apply_transaction(transaction);
		blocks.apply_transaction(transaction);
	}

	/// Instantiate new value.
	pub fn new(
		key: &[u8],
		value_at: Vec<u8>,
		state: &Latest<(u32, u64)>,
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Self {
		let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
		HValue(
			nodes_definition::HValue::new(Some(value_at), state, context),
			branch_nodes,
			block_nodes,
		)
	}

	/// Decode existing value.
	pub fn decode_with_context(
		key: &[u8],
		encoded: &[u8],
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Option<Self> {
		let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
		Some(HValue(
			nodes_definition::HValue::decode_with_context(&mut &encoded[..], &context)?,
			branch_nodes,
			block_nodes,
		))
	}

	/// Access existing value.
	fn value(&self, current_state: &ForkPlan<u32, u64>) -> Option<Vec<u8>> {
		let HValue(inner, _, _) = self;
		nodes_definition::value(inner, current_state)
	}

	fn set_first_change(
		&mut self,
		change: Option<Vec<u8>>,
		current_state: &Latest<(u32, u64)>,
	) -> Result<UpdateResult<()>, String> {
		let HValue(inner, _, _) = self;
		Ok(inner.set(change, current_state))
	}

	fn encode(&self) -> Vec<u8> {
		let HValue(inner, _, _) = self;
		inner.encode()
	}

	/// Migrate HValue
	fn migrate<B: BlockT, S: TreeManagementStorage>(
		&mut self,
		migrate: &mut historied_db::management::Migrate<B::Hash, TreeManagement<B::Hash, S>>,
	) -> UpdateResult<()> {
		let HValue(inner, _, _) = self;
		inner.migrate(migrate.migrate())
	}
}

/// Lock multiple guards and release on drop.
struct Guards<'a>(
	Vec<(Vec<u8>, MutexGuard<'static, ()>, Arc<Mutex<()>>)>,
	&'a Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>,
);

impl<'a> Guards<'a> {
	fn new(locks: &'a Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>) -> Self {
		Guards(Vec::new(), locks)
	}

	fn add(&mut self, key: Vec<u8>) {
		let key_lock = {
			let mut locks = self.1.lock();
			locks.entry(key.clone()).or_default().clone()
		};
		let key_lock_ref = key_lock.as_ref() as *const Mutex<()>;
		// Unsafe call relies on Guards 'a lifetime.
		let key_lock_ref = unsafe { key_lock_ref.as_ref().unwrap() };
		let guard = key_lock_ref.lock();
		// keep a copy of the arc so concurrent call will not remove it
		// from map.
		self.0.push((key, guard, key_lock));
	}

	fn pop(&mut self) {
		let mut locks = self.1.lock();
		Self::pop_inner(&mut self.0, &mut locks);
	}

	fn pop_inner(
		guards: &mut Vec<(Vec<u8>, MutexGuard<'static, ()>, Arc<Mutex<()>>)>,
		locks: &mut MutexGuard<HashMap<Vec<u8>, Arc<Mutex<()>>>>,
	) -> bool {
		if let Some((key, guard, key_lock)) = guards.pop() {
			drop(guard);
			drop(key_lock);
			let key_lock = locks.get_mut(&key);
			if let Some(_) = key_lock.and_then(Arc::get_mut) {
				locks.remove(&key);
			}
			true
		} else {
			false
		}
	}

	fn drop_all(&mut self) {
		let mut locks = self.1.lock();
		let guards = &mut self.0;
		{
			while Self::pop_inner(guards, &mut locks) { }
		}
	}
}

impl<'a> Drop for Guards<'a> {
	fn drop(&mut self) {
		self.drop_all()
	}
}

/// Offchain local storage at a given block.
#[derive(Clone)]
pub struct BlockChainLocalAt<Block: BlockT, S: TreeManagementStorage + 'static> {
	db: Arc<dyn Database<DbHash>>,
	at_read: ForkPlan<u32, u64>,
	at_write: Option<Latest<(u32, u64)>>,
	locks: Arc<Mutex<HashMap<Vec<u8>, Arc<Mutex<()>>>>>,
	// TODO this is only use to access inner ordered db: could use a specific
	// handle instead to remove the types parameter.
	historied_management: TreeManagementSync<Block, S>,
	safe_offchain_locks: bool,
}

impl<Block, S> BlockChainLocalAt<Block, S>
	where
		Block: BlockT,
		S: TreeManagementStorage<Storage = TransactionalMappedDB<MappedDBDyn>> + Clone,
{
	// Nodes db is the same as storage db, exposing
	// through a function for clarity.
	fn nodes_db(&self) -> &Arc<dyn Database<DbHash>> {
		&self.db
	}

	fn decode_inner(
		key: &[u8],
		encoded: &[u8],
		current_state: &ForkPlan<u32, u64>,
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Option<Vec<u8>> {
		let h_value = HValue::decode_with_context(key, &mut &encoded[..], nodes_db)?;
		h_value.value(current_state)
	}

	// TODO check if nodes backend are written??? or how.
	// TODO actually need to reuse blocksdb and branchdb instead of new one $afrom decode_with_context?
	// actually looks lit it should b eflush from this call
	fn modify(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		condition: Option<impl Fn(Option<&[u8]>) -> bool>,
		new_value: Option<&[u8]>,
		is_new: bool,
		lock_assert: bool,
	) -> Result<bool, ModifyError> {
		if self.at_write.is_none() && is_new {
			return Err(ModifyError::NoWriteState);
		}
		let key: Vec<u8> = concatenate_prefix_and_key(prefix, item_key);
		let key_lock = if lock_assert {
			let mut locks = self.locks.lock();
			Some(locks.entry(key.clone()).or_default().clone())
		} else {
			None
		};

		let result = || -> Result<bool, ModifyError> {
			let at_write_inner;
			let at_write = if is_new {
				self.at_write.as_ref().expect("checked above")
			} else {
				use historied_db::StateIndex;
				at_write_inner = Latest::unchecked_latest(self.at_read.index());
				&at_write_inner
			};
			let is_set;
			{
				let _key_guard = key_lock.as_ref().map(|key_lock| key_lock.lock());

				let histo = self.db.get(columns::OFFCHAIN, &key)
					.and_then(|encoded| {
						HValue::decode_with_context(&key, &mut &encoded[..], self.nodes_db())
					});
				let val = histo.as_ref().and_then(|h| {
					use historied_db::historied::Data;
					h.0.get(&self.at_read).flatten()
				});

				is_set = condition.map(|c| c(val.as_ref().map(|v| v.as_slice()))).unwrap_or(true);

				if is_set {
					let mut tx = Transaction::new();
					let new_value = new_value.map(|v| v.to_vec());
					let (new_value, update_result) = if let Some(mut histo) = histo {
						let update_result = if is_new {
							histo.0.set(new_value, at_write)
						} else {
							use historied_db::historied::force::ForceDataMut;
							use historied_db::StateIndex;
							let mut index = Default::default();
							histo.0.force_set(
								new_value,
								at_write.index_ref().unwrap_or_else(|| {
									index = at_write.index();
									&index
								}),
							)
						};
						if let &UpdateResult::Unchanged = &update_result {
							(Vec::new(), update_result)
						} else {
							histo.apply_nodes_backend_to_transaction(&mut tx);
							(histo.encode(), update_result)
						}
					} else {
						if let Some(new_value) = new_value {
							(
								HValue::new(
									&key,
									new_value,
									at_write,
									&self.db,
								).encode(),
								UpdateResult::Changed(()),
							)
						} else {
							// nothing to delete
							(Default::default(), UpdateResult::Unchanged)
						}
					};
					match update_result {
						UpdateResult::Changed(()) => {
							tx.set(columns::OFFCHAIN, &key, new_value.as_slice());
						},
						UpdateResult::Cleared(()) => {
							tx.remove(columns::OFFCHAIN, &key);
						},
						UpdateResult::Unchanged => (),
					}
					match update_result {
						UpdateResult::Unchanged => (),
						UpdateResult::Changed(())
						| UpdateResult::Cleared(()) => {
							let mut ordered_db = self.historied_management.inner.write();
							let db = ordered_db.instance.ser();
							let at_write = rev_index(at_write.latest());
							let mut journals = ChangesJournal::from_db(db);
							journals.add_changes(
								db,
								at_write,
								vec![key.clone()],
								false,
							);
							TreeManagementSync::<Block, _>::apply_historied_management_changes(
								&mut ordered_db.instance,
								&mut tx,
							);

							if self.db.commit(tx).is_err() {
								return Err(ModifyError::DbWrite);
							};
						},
					}
				}
			}
			Ok(is_set)
		}();

		if let Some(key_lock) = key_lock {
			// clean the lock map if we're the only entry
			let mut locks = self.locks.lock();
			{
				drop(key_lock);
				let key_lock = locks.get_mut(&key);
				if let Some(_) = key_lock.and_then(Arc::get_mut) {
					locks.remove(&key);
				}
			}
		}
		result
	}

	/// Under current design, the local update is only doable when we
	/// are at a latest block, this function tells if we can use
	/// function that modify state.
	pub fn can_update(&self) -> bool {
		true
	}
}

impl<Block, S> sp_core::offchain::OffchainStorage for BlockChainLocalAt<Block, S>
	where
		Block: BlockT,
		S: TreeManagementStorage<Storage = TransactionalMappedDB<MappedDBDyn>> + Clone,
{
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		match self.modify(
			prefix,
			key,
			test,
			Some(value),
			false,
			self.safe_offchain_locks,
		) {
			Ok(_) => (),
			Err(ModifyError::NoWriteState) => panic!("Cannot write at latest"),
			Err(ModifyError::DbWrite) => panic!("Offchain local db commit failure"),
		}
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let test: Option<fn(Option<&[u8]>) -> bool> = None;
		match self.modify(
			prefix,
			key,
			test,
			None,
			false,
			self.safe_offchain_locks,
		) {
			Ok(_) => (),
			Err(ModifyError::NoWriteState) => panic!("Cannot write at latest"),
			Err(ModifyError::DbWrite) => panic!("Offchain local db commit failure"),
		}
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = concatenate_prefix_and_key(prefix, key);
		if let Some(v) = self.db.get(columns::OFFCHAIN, key.as_slice()) {
			Self::decode_inner(key.as_slice(), v.as_slice(), &self.at_read, self.nodes_db())
		} else {
			None
		}
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		item_key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let test = |v: Option<&[u8]>| old_value == v;
		match self.modify(
			prefix,
			item_key,
			Some(test),
			Some(new_value),
			false,
			true,
		) {
			Ok(b) => b,
			Err(ModifyError::NoWriteState) => panic!("Cannot write at latest"),
			Err(ModifyError::DbWrite) => panic!("Offchain local db commit failure"),
		}
	}
}

/// Modifiable Historied DB for a given new block state.
///
/// This assumes that the block is a head block and modification
/// is conflict free (writing the delta a the end of a fork branch
/// without concurrent access).
pub struct HistoriedDBMut<DB> {
	/// Branch head indexes of a latest block.
	pub current_state: Latest<(u32, u64)>,
	/// Inner database storing historied values.
	pub db: DB,
	/// Db for storing nodes.
	pub nodes_db: Arc<dyn Database<DbHash>>,
}

impl<DB: Database<DbHash>> HistoriedDBMut<DB> {
	/// Create a transaction for this historied db.
	pub fn transaction(&self) -> Transaction<DbHash> {
		Transaction::new()
	}

	/// write a single value in change set.
	pub fn update_single(
		&mut self,
		key: Vec<u8>,
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
		journal_changes: Option<&mut Vec<Vec<u8>>>,
	) {
		self.update_single_inner(key, change, change_set, crate::columns::OFFCHAIN, journal_changes);
	}

	/// write a single value in change set.
	pub fn update_single_inner(
		&mut self,
		key: Vec<u8>,
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
		column: u32,
		journal_changes: Option<&mut Vec<Vec<u8>>>,
	) {
		let k = key.as_slice();
		let histo = if let Some(histo) = self.db.get(column, k) {
			Some(HValue::decode_with_context(k, &mut &histo[..], &self.nodes_db)
				.expect("Bad encoded value in db, closing"))
		} else {
			if change.is_none() {
				return;
			}
			None
		};
		match if let Some(mut histo) = histo {
			let update = histo.set_first_change(change, &self.current_state)
				.expect("Could not write change in snapshot db, DB corrupted");
			(histo, update)
		} else {
			if let Some(v) = change {
				let value = HValue::new(k, v, &self.current_state, &self.nodes_db);
				(value, UpdateResult::Changed(()))
			} else {
				return;
			}
		} {
			(mut value, UpdateResult::Changed(())) => {
				value.apply_nodes_backend_to_transaction(change_set);
				change_set.set_from_vec(column, k, value.encode());
				journal_changes.map(|keys| keys.push(key));
			},
			(mut value, UpdateResult::Cleared(())) => {
				value.apply_nodes_backend_to_transaction(change_set);
				change_set.remove(column, k);
				journal_changes.map(|keys| keys.push(key));
			},
			(_value, UpdateResult::Unchanged) => (),
		}
	}
}

/// Consumer with transactional support.
///
/// Read journaled keys and update inner transaction with requires
/// migration changes.
pub struct TransactionalConsumer<Block: BlockT, S: TreeManagementStorage + 'static> {
	/// Storage to use.
	pub storage: BlockChainLocalStorage<Block, S>,
	/// Transaction to update on migrate.
	pub pending: Arc<RwLock<Transaction<DbHash>>>,
}

impl<B, S> historied_db::management::ManagementConsumer<B::Hash, TreeManagement<B::Hash, S>> for TransactionalConsumer<B, S>
	where
		B: BlockT,
		S: TreeManagementStorage + 'static,
{
	fn migrate(&self, migrate: &mut historied_db::management::Migrate<B::Hash, TreeManagement<B::Hash, S>>) {
		let mut keys_to_migrate = std::collections::BTreeSet::<Vec<u8>>::new();
		assert!(S::JOURNAL_CHANGES);
		let (prune, state_changes) = migrate.migrate().touched_state();
		// this db is transactional, flush is done externally (consumer call from a historied
		// managenment).
		let db = migrate.management().ser();
		let mut journals = ChangesJournal::from_db(db);

		if let Some(pruning) = prune {
			journals.remove_changes_before(db, &(pruning, Default::default()), &mut keys_to_migrate);
		}

		for state in state_changes {
			let state = rev_index(&state);
			if let Some(removed) = journals.remove_changes_at(db, &state) {
				for key in removed {
					keys_to_migrate.insert(key);
				}
			}
		}

		if keys_to_migrate.is_empty() {
			return;
		}

		let mut pending = self.pending.write();
		let column = crate::columns::OFFCHAIN;
		// locking changed key until transaction applied.
		let mut guards = Guards::new(self.storage.locks.as_ref());
		let mut process_key = |
			k: &[u8], histo: Vec<u8>,
			nodes_db: &Arc<dyn Database<DbHash>>,
		| {
			guards.add(k.to_vec());

			let mut histo = HValue::decode_with_context(k, &mut &histo[..], nodes_db)
				.expect("Bad encoded value in db, closing");
			match histo.migrate::<B, S>(migrate) {
				historied_db::UpdateResult::Changed(()) => {
					histo.apply_nodes_backend_to_transaction(&mut pending);
					pending.set_from_vec(column, k, histo.encode());
				},
				historied_db::UpdateResult::Cleared(()) => {
					histo.apply_nodes_backend_to_transaction(&mut pending);
					pending.remove(column, k);
				},
				historied_db::UpdateResult::Unchanged => {
					// early guard release for this key.
					guards.pop();
				},
			}
		};

		assert!(S::JOURNAL_CHANGES);
		for k in keys_to_migrate {
			if let Some(histo) = self.storage.db.get(column, k.as_slice()) {
				process_key(k.as_slice(), histo, self.storage.nodes_db());
			} else {
				continue;
			};
		}
	}
}

#[derive(Debug)]
enum ModifyError {
	NoWriteState,
	DbWrite,
}

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
