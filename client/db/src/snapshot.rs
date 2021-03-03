// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Key value snapshot db with history.

use sp_database::{SnapshotDb as SnapshotDbT};
use crate::tree_management::{TreeManagementSync, TreeManagementPersistence};
use historied_db::{
	DecodeWithContext,
	management::{ForkableManagement, Management},
	historied::{DataMut, aggregate::Sum as _},
	Latest, UpdateResult,
	historied::tree::aggregate::Sum as TreeSum,
	management::tree::ForkPlan,
	backend::nodes::ContextHead,
	historied::aggregate::xdelta::{BytesDelta, BytesDiff},
};
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, Zero, NumberFor,
};
use sp_core::storage::{ChildInfo, ChildType, PrefixedStorageKey, well_known_keys};
use std::sync::Arc;
use parking_lot::RwLock;
use sp_database::Transaction;
use crate::DbHash;
use log::warn;
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sp_database::{Database, OrderedDatabase};
use sp_state_machine::kv_backend::KVBackend;
use codec::{Decode, Encode, Compact};
use sp_database::{SnapshotDbConf, SnapshotDBMode};
use sp_database::error::DatabaseError;
pub use sc_state_db::PruningMode;
use crate::historied_nodes::nodes_database::{BranchNodes, BlockNodes, NODES_COL};
use crate::historied_nodes::nodes_backend::Context;
use std::borrow::Cow;

/// Definition of mappings used by `TreeManagementPersistence`.
pub mod snapshot_db_conf {
	use sp_database::{SnapshotDbConf, SnapshotDBMode};
	use sp_blockchain::Result as ClientResult;
	use historied_db::mapped_db::MappedDBDyn;

	const CST: &'static[u8] = &[8u8, 0, 0, 0]; // AUX collection

	// Serialized configuration for snapshot.
	static_instance_variable!(SnapConfSer, CST, b"snapshot_db/config", false);

	// Mapping to store journal of change keys
	static_instance!(JournalChanges, b"\x08\x00\x00\x00snapshot_db/journal_changes");

	/// Get initial conf from chain_spec.
	pub fn from_chain_spec(properties: &sp_chain_spec::Properties) -> SnapshotDbConf {
		let mut conf = SnapshotDbConf::default();
		if Some(Some(true)) != properties.get("snapshotEnabled").map(|v| v.as_bool()) {
			return conf;
		}
		conf.enabled = true;
		if Some(Some(true)) == properties.get("snapshotPrimary").map(|v| v.as_bool()) {
			conf.primary_source = true;
		}
		if Some(Some(true)) == properties.get("snapshotNoNodeBackend").map(|v| v.as_bool()) {
			conf.no_node_backend = true;
		}
		if Some(Some(true)) == properties.get("snapshotJournalPruning").map(|v| v.as_bool()) {
			conf.journal_pruning = true;
		}
		if Some(Some(true)) == properties.get("snapshotDebugAssert").map(|v| v.as_bool()) {
			conf.debug_assert = true;
		}
		if Some(Some("xdelta3")) == properties.get("snapshotDebugAssert").map(|v| v.as_str()) {
			conf.diff_mode = SnapshotDBMode::Xdelta3Diff;
		}
		if let Some(Some(window_size)) = properties.get("snapshotLazyPruning").map(|v| v.as_u64()) {
			conf.lazy_pruning = Some(window_size as u32);
		}
		conf
	}

	/// Lazy initialization of snapshot db configuration from chain spec.
	pub fn update_db_conf(
		db: &mut MappedDBDyn,
		mut f: impl FnMut(&mut SnapshotDbConf) -> sp_blockchain::Result<()>,
	) -> sp_blockchain::Result<()> {
		let mut conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		let mut conf_mapping = conf.mapping(db);
		let mut conf = conf_mapping.get().clone();
		let res = f(&mut conf);
		if res.is_ok() {
			conf_mapping.set(conf);
		}
		res
	}

	/// Lazy initialization of snapshot db configuration from chain spec.
	pub fn lazy_init_from_chain_spec(
		db: &mut MappedDBDyn,
		genesis_conf: &SnapshotDbConf,
	) -> sp_blockchain::Result<()> {
		let mut conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		if !conf.get().lazy_set {
			let mut conf_mapping = conf.mapping(db);
			let mut genesis_conf = genesis_conf.clone();
			genesis_conf.lazy_set = true;
			conf_mapping.set(genesis_conf);
		}
		Ok(())
	}

	/// Get snapshot db configuration from chain spec.
	pub fn fetch_config(
		db: &MappedDBDyn,
	) -> ClientResult<SnapshotDbConf> {
		let conf = historied_db::mapped_db::Variable::<SnapshotDbConf, _, SnapConfSer>::from_ser(db);
		Ok(conf.get().clone())
	}
}

/// Snapshot db implementation.
#[derive(Clone)]
pub struct SnapshotDb<Block: BlockT> {
	/// Historied management use by snapshot db.
	/// Currently snapshot db is single consumer, so init and clear
	/// operation also act on `historied_management`.
	/// This use a transactional layer in storage.
	historied_management: TreeManagementSync<Block, TreeManagementPersistence>,
	/// Database with historied items. Warning, this is non transactional.
	ordered_db: Arc<dyn OrderedDatabase<DbHash>>,
	/// Configuration for this db.
	config: SnapshotDbConf,
	/// Historied value variant.
	hvalue_type: HValueType,
	/// Db for storing nodes.
	nodes_db: Arc<dyn Database<DbHash>>,
}

/// First level partition of 'STATE_SNAPSHOT' column.
#[repr(u8)]
enum SnapshotColumnPrefixes {
	/// Historied value from top trie.
	Top = 0,
	/// Historied value from children trie.
	Children = 1,
	/// Block nodes backend.
	BlockNodes = 3,
	/// Branch nodes backend.
	BranchNodes = 4,
}

fn child_prefixed_key(child_info: Option<&ChildInfo>, key: &[u8]) -> Vec<u8> {
	if let Some(child_info) = child_info {
		child_prefixed_key_inner_default(child_info.storage_key(), key)
	} else {
		child_prefixed_key_inner_top(key)
	}
}

fn child_prefixed_key_inner_top(key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = Vec::with_capacity(1 + key.len());
	prefixed_key.push(SnapshotColumnPrefixes::Top as u8);
	prefixed_key.extend_from_slice(key);
	prefixed_key
}

fn child_prefixed_key_inner_default(prefix: &[u8], key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = Vec::with_capacity(1 + prefix.size_hint() + key.len());
	prefixed_key.push(SnapshotColumnPrefixes::Children as u8);
	prefix.encode_to(&mut prefixed_key);
	prefixed_key.extend_from_slice(key);
	prefixed_key
}

impl<Block: BlockT> SnapshotDbT<Block> for SnapshotDb<Block> {
	fn clear_snapshot_db(&self) -> sp_database::error::Result<()> {
		let mut management = self.historied_management.inner.write();
		// get non transactional mappeddb.
		let db = &mut management.instance.ser().db;
		snapshot_db_conf::update_db_conf(db, |genesis_conf| {
			*genesis_conf = Default::default();
			Ok(())
		}).map_err(|e| DatabaseError(Box::new(e)))?;

		TreeManagementSync::<Block, TreeManagementPersistence>::clear(&self.ordered_db)
			.map_err(|e| DatabaseError(Box::new(e)))?;
		self.ordered_db.clear_prefix(crate::columns::AUX, b"snapshot_db/");
		self.ordered_db.clear_prefix(crate::columns::STATE_SNAPSHOT, b"");

		Ok(())
	}

	fn update_running_conf(
		&self,
		use_as_primary: Option<bool>,
		debug_assert: Option<bool>,
		pruning_window: Option<Option<u32>>,
		lazy_pruning_window: Option<u32>,
	) -> sp_database::error::Result<()> {
		let mut management = self.historied_management.inner.write();
		let db = &mut management.instance.ser().db;
		snapshot_db_conf::update_db_conf(db, |mut genesis_conf| {
			if !genesis_conf.enabled {
				return Err(ClientError::StateDatabase(
					"Disabled snapshot db need to be created first".into(),
				));
			}
			if let Some(primary) = use_as_primary {
				genesis_conf.primary_source = primary;
			}
			if let Some(debug) = debug_assert {
				genesis_conf.debug_assert = debug;
			}
			if let Some(window) = pruning_window {
				genesis_conf.pruning = Some(window);
			}
			if let Some(window) = lazy_pruning_window {
				genesis_conf.lazy_pruning = Some(window);
			}
			Ok(())
		}).map_err(|e| DatabaseError(Box::new(e)))
	}

	fn re_init(
		&self,
		mut config: SnapshotDbConf,
		best_block: Block::Hash,
		state_visit: impl sc_client_api::StateVisitor,
	) -> sp_database::error::Result<()> {
		self.clear_snapshot_db()?;

		config.lazy_set = true;

		{
			let mut management = self.historied_management.inner.write();
			let db = &mut management.instance.ser().db;
			snapshot_db_conf::update_db_conf(db, |genesis_conf| {
				*genesis_conf = config.clone();
				Ok(())
			}).map_err(|e| DatabaseError(Box::new(e)))?;
		}

		let (query_plan, update_plan) = self.historied_management.init_new_management(
			&best_block,
			&self.ordered_db,
		).map_err(|e| DatabaseError(Box::new(e)))?;
		let hvalue_type = HValueType::resolve(&config).ok_or_else(|| {
			let e = ClientError::StateDatabase(format!("Invalid snapshot config {:?}", config));
			DatabaseError(Box::new(e))
		})?;
		let mut historied_db = HistoriedDBMut {
			current_state: update_plan,
			current_state_read: query_plan,
			db: self.ordered_db.clone(),
			config,
			hvalue_type,
			nodes_db: self.nodes_db.clone(),
		};

		let mut tx = Default::default();
		let mut count_tx = 0;
		let tx = &mut tx;
		let count_tx = &mut count_tx;
		let mut child_storage_key = PrefixedStorageKey::new(Vec::new());
		let child_storage_key = &mut child_storage_key;
		let mut last_child: Option<Vec<u8>> = None;
		let last_child = &mut last_child;
		state_visit.state_visit(|child, key, value| {
			let key = if let Some(child) = child {
				if Some(child) != last_child.as_ref().map(Vec::as_slice) {
					*child_storage_key = PrefixedStorageKey::new(child.to_vec());
					*last_child = Some(child.to_vec());
				}
				match ChildType::from_prefixed_key(&child_storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) => {
						child_prefixed_key_inner_default(
							storage_key,
							key.as_slice(),
						)
					},
					_ => {
						let e = ClientError::StateDatabase("Unknown child trie type in state".into());
						return Err(DatabaseError(Box::new(e)));
					},
				}
			} else {
				child_prefixed_key_inner_top(key.as_slice())
			};
			// Do not journal initial change, since we will not prune them without another change
			// journaled.
			let journal_change = None;
			historied_db.unchecked_new_single_inner(key, value, tx, crate::columns::STATE_SNAPSHOT, journal_change);
			*count_tx = *count_tx + 1;
			if *count_tx == 1000 {
				//count += 1;
				//warn!("write a thousand {} {:?}", count, &k[..20]);
				let to_commit = std::mem::take(tx);
				self.ordered_db.commit(to_commit)?;
				*count_tx = 0;
			}
			Ok(())
		})?;
		let to_commit = std::mem::take(tx);
		self.ordered_db.commit(to_commit)?;

		Ok(())
	}

	fn export_snapshot(
		&self,
		out: &mut impl std::io::Write,
		last_finalized: NumberFor<Block>,
		from: Option<NumberFor<Block>>,
		to: Option<NumberFor<Block>>,
		flat: bool,
		db_mode: SnapshotDBMode,
		default_flat: impl sc_client_api::StateVisitor,
	) -> sp_database::error::Result<()> {
		if !self.config.enabled {
			if !flat {
				let e = ClientError::StateDatabase("Disabled snapshot db need to be created first".into());
				return Err(DatabaseError(Box::new(e)));
			} else {
				return self.flat_from_state(out, default_flat);
			}
		}

		unimplemented!("TODO next");
	}
}

impl<Block: BlockT> SnapshotDb<Block> {
	/// Instantiate new db.
	pub fn new(
		mut historied_management: TreeManagementSync<Block, TreeManagementPersistence>,
		ordered_db: Arc<dyn OrderedDatabase<DbHash>>,
		nodes_db: Arc<dyn Database<DbHash>>,
	) -> ClientResult<Self> {
		let config = {
			let management = historied_management.inner.read();
			let db = &management.instance.ser_ref().db;
			snapshot_db_conf::fetch_config(db)?
		};
		historied_management.pruning_window = config.pruning.clone()
			.flatten().map(|nb| nb.into());
		let hvalue_type = HValueType::resolve(&config)
			.ok_or_else(|| ClientError::StateDatabase(
				format!("Invalid snapshot config {:?}", config)
			))?;
		let mut snapshot_db = SnapshotDb {
			historied_management,
			ordered_db,
			config,
			hvalue_type,
			nodes_db,
		};

		let storage = snapshot_db.clone();
		let pending = snapshot_db.historied_management.inner.read().consumer_transaction.clone();
		snapshot_db.historied_management.register_consumer(Box::new(TransactionalConsumer {
			storage,
			pending,
		}));

		Ok(snapshot_db)
	}

	pub fn new_block_historied_db_mut(
		&self,
		parent: &Block::Hash,
		at: &Block::Hash,
	) -> ClientResult<Option<HistoriedDBMut<Arc<dyn OrderedDatabase<DbHash>>>>> {
		if !self.config.enabled {
			return Ok(None);
		}
		let (query_plan, update_plan) = self.historied_management.register_new_block(&parent, &at)?;
		Ok(Some(HistoriedDBMut {
			current_state: update_plan,
			current_state_read: query_plan,
			db: self.ordered_db.clone(),
			config: self.config.clone(),
			hvalue_type: self.hvalue_type,
			nodes_db: self.nodes_db.clone(),
		}))
	}

	pub fn get_historied_db(
		&self,
		at: Option<&Block::Hash>,
	) -> ClientResult<Option<HistoriedDB>> {
		if !self.config.enabled || !(self.config.primary_source || self.config.debug_assert) {
			return Ok(None);
		}

		let mut management = self.historied_management.inner.write();
		let current_state = if let Some(hash) = at {
			management.instance.get_db_state(&hash)
				.ok_or_else(|| ClientError::StateDatabase(
					format!("Snapshot db missing state for hash {:?}", hash)
				))?
		} else {
			// genesis
			let state = management.instance.latest_state_fork();
			// starting a new state at default hash is not strictly necessary,
			// but we lack a historied db primitive to get default query state
			// on (0, 0).
			let h = Default::default();
			management.instance.get_db_state(&h)
				.or_else(|| management.instance.append_external_state(h.clone(), &state)
					.and_then(|_| management.instance.get_db_state(&h))
				).ok_or_else(|| ClientError::StateDatabase("Historied management error".into()))?
		};

		Ok(Some(HistoriedDB {
			current_state,
			db: self.ordered_db.clone(),
			hvalue_type: self.hvalue_type,
			config: self.config.clone(),
			nodes_db: self.nodes_db.clone(),
		}))
	}

	pub fn get_kvbackend(
		&self,
		at: Option<&Block::Hash>,
	) -> ClientResult<Option<Arc<dyn KVBackend>>> {
		if let Some(db) = self.get_historied_db(at)? {
			let db = Arc::new(db);
			Ok(Some(db))
		} else {
			Ok(None)
		}
	}

	/// Return handle to journaling db if needed.
	pub fn do_journals(&self) -> bool {
		self.config.journal_pruning
	}

	/// Process block changes, and update a input transaction.
	pub fn apply_block_change(
		&self,
		operation: &crate::BlockImportOperation<Block>,
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

		let mut ordered_historied_db = if let Some((hash, parent_hash)) = hashes {
			// Ensure pending layer is clean
			self.historied_management.clear_changes();
			self.new_block_historied_db_mut(&parent_hash, &hash)?
		} else {
			None
		};

		// Do not journal genesis.
		let mut management = (self.do_journals() && !is_genesis)
			.then(|| self.historied_management.inner.write());
		let journals = management.as_mut().map(|management| management.instance.ser());
		let mut journal_keys = journals.is_some().then(|| Vec::new());
		// state change uses ordered db
		if let Some(ordered_historied_db) = ordered_historied_db.as_mut() {
			let historied_update = operation.storage_updates.clone();
			let mut nb = 0;
			for (k, change) in historied_update {
				ordered_historied_db.update_single(None, k.as_slice(), change, transaction, journal_keys.as_mut());
				nb += 1;
			}

			let historied_update = operation.child_storage_updates.clone();
			for (storage_key, historied_update) in historied_update {
				assert!(storage_key.starts_with(well_known_keys::DEFAULT_CHILD_STORAGE_KEY_PREFIX));

				let child_info = ChildInfo::new_default_from_vec(storage_key);
				for (k, change) in historied_update {
					ordered_historied_db.update_single(Some(&child_info), k.as_slice(), change, transaction, journal_keys.as_mut());
					nb += 1;
				}
			}
			warn!("committed {:?} change in historied db", nb);
		}

		if let (
			Some(journal_keys),
			Some(ordered_db),
			Some(historied),
		) = (journal_keys, journals, ordered_historied_db.as_ref()) {
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
	pub fn historied_management(&self) -> &TreeManagementSync<Block, TreeManagementPersistence> {
		&self.historied_management
	}

	fn flat_from_state<O: std::io::Write>(
		&self,
		out: &mut O,
		state_visit: impl sc_client_api::StateVisitor,
	) -> sp_database::error::Result<()> {
		out.write(&[SnapshotMode::Flat as u8, StateId::Top as u8])
			.map_err(|e| DatabaseError(Box::new(e)))?;

		let mut default_key_writer = KeyWriter {
			previous: [][..].into(),
		};
		let default_key_writer = &mut default_key_writer;
		let mut default_child_key_writer = KeyWriter {
			previous: Default::default(),
		};
		let default_child_key_writer = &mut default_child_key_writer;

		let mut last_child: Option<Vec<u8>> = None;
		let last_child = &mut last_child;
		let mut child_storage_key = PrefixedStorageKey::new(Vec::new());
		let child_storage_key = &mut child_storage_key;
		state_visit.state_visit(|child, key, value| {
			if child != last_child.as_ref().map(Vec::as_slice) {
				if let Some(child) = child.as_ref() {
					*child_storage_key = PrefixedStorageKey::new(child.to_vec());
					*last_child = Some(child.to_vec());
					match ChildType::from_prefixed_key(&child_storage_key) {
						Some((ChildType::ParentKeyId, storage_key)) => {
							out.write(&[StateId::DefaultChild as u8])
								.map_err(|e| DatabaseError(Box::new(e)))?;
							default_child_key_writer.write_next_owned(storage_key.to_vec(), out);
						},
						_ => {
							let e = ClientError::StateDatabase("Unknown child trie type in state".into());
							return Err(DatabaseError(Box::new(e)));
						},
					}
				} else {
					out.write(&[StateId::Top as u8])
						.map_err(|e| DatabaseError(Box::new(e)))?;
				}
				*default_key_writer = KeyWriter {
					previous: Default::default(),
				};
			}
			default_key_writer.write_next_owned(key, out);
			value.encode_to(out);
			Ok(())
		})?;

		out.write(&[SnapshotMode::Flat as u8, StateId::EndOfState as u8])
			.map_err(|e| DatabaseError(Box::new(e)))?;
		Ok(())
	}

	/// Handle new head, this only do minor assertions
	/// as historied value do not care about head.
	pub fn set_head_with_transaction(
		&self,
		_transaction: &mut Transaction<DbHash>,
		_previous_head: &Block::Hash,
		new_head: &(NumberFor<Block>, Block::Hash),
	) -> ClientResult<()> {
		if let Some(enc) = self.config.start_block.as_ref() {
			let start = Decode::decode(&mut enc.as_slice())
				.map_err(|e| DatabaseError(Box::new(e)))?;
			if new_head.0 < start {
				return Err(ClientError::StateDatabase("Snapshot db cannot handle this reorg.".into()));
			}
		}
		Ok(())
	}
}

/// First byte of snapshot define
/// its mode.
#[repr(u8)]
enum SnapshotMode {
	/// Flat variant, no compression, and obviously no diff.
	Flat = 0,
}

/// First byte of snapshot define
/// its mode.
#[repr(u8)]
enum StateId {
	/// End of state.
	/// This allow putting state payload in non final position.
	EndOfState = 0,
	/// Top state
	Top = 1,
	/// Default child trie, followed by unprefixed path from default trie prefix.
	/// Path is a KeyDelta from previous child trie.
	DefaultChild = 2,
}

enum KeyDelta {
	Augment(usize),
	PopAugment(usize, usize),
}

impl Encode for KeyDelta {
	fn size_hint(&self) -> usize {
		2
	}

	fn encode_to<T: codec::Output + ?Sized>(&self, out: &mut T) {
		match self {
			KeyDelta::Augment(nb) => {
				let augment_nb = nb * 2; // 0 as last bit
				Compact(augment_nb as u64).encode_to(out);
			},
			KeyDelta::PopAugment(nb, nb2) => {
				let pop_nb = (nb * 2) + 1; // 1 as last bit
				Compact(pop_nb as u64).encode_to(out);
				Compact(*nb2 as u64).encode_to(out);
			},
		}
	}
}

impl Decode for KeyDelta {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let first = Compact::<u64>::decode(input)?.0;
		if first % 2 == 0 {
			Ok(KeyDelta::Augment((first / 2) as usize))
		} else {
			let second = Compact::<u64>::decode(input)?.0;
			Ok(KeyDelta::PopAugment((first / 2) as usize, (second / 2) as usize))
		}
	}
}

/// Key are written in delta mode (since they are sorted it is a big size gain).
struct KeyWriter<'a> {
	previous: Cow<'a, [u8]>,
}

fn common_depth(v1: &[u8], v2: &[u8]) -> usize {
	let upper_bound = std::cmp::min(v1.len(), v2.len());
	for a in 0 .. upper_bound {
		if v1[a] != v2[a] {
			return a;
		}
	}
	upper_bound
}

impl<'a> KeyWriter<'a> {
	fn write_next_owned<O: codec::Output + ?Sized>(&mut self, next: Vec<u8>, out: &mut O) {
		let previous = &self.previous[..];
		let common = common_depth(previous, next.as_slice());
		let keydelta = if common < previous.len() {
			KeyDelta::PopAugment(previous.len() - common, next.len() - common);
		} else {
			KeyDelta::Augment(next.len() - common);
		};
		keydelta.encode_to(out);
		out.write(&next[common..]);
		self.previous = next.into();
	}

	fn write_next<O: codec::Output + ?Sized>(&mut self, next: &'a [u8], out: &mut O) {
		let previous = &self.previous;
		let common = common_depth(previous, next);
		let keydelta = if common < previous.len() {
			KeyDelta::PopAugment(previous.len() - common, next.len() - common);
		} else {
			KeyDelta::Augment(next.len() - common);
		};
		keydelta.encode_to(out);
		out.write(&next[common..]);
		self.previous = next.into();
	}
}

/// Key are read in delta mode (since they are sorted it is a big size gain).
struct KeyReader {
	previous: Vec<u8>,
}

impl KeyReader {
	fn read_next<I: codec::Input>(&mut self, input: &mut I)  -> Result<&[u8], codec::Error> {
		let nb = match KeyDelta::decode(input)? {
			KeyDelta::Augment(nb) => nb,
			KeyDelta::PopAugment(nb, nb2) => {
				let old_len = self.previous.len();
				if old_len < nb {
					return Err("Invalid keydiff encoding".into());
				}
				self.previous.truncate(old_len - nb);
				nb2
			},
		};
		let old_len = self.previous.len();
		self.previous.resize(old_len + nb, 0);
		input.read(&mut self.previous[old_len..])?;
		Ok(self.previous.as_slice())
	}
}

/*
mod SingleNodeEncodedNoDiff {
	type LinearBackend<'a> = historied_db::backend::encoded_array::EncodedArray<
		'a,
		Vec<u8>,
		historied_db::backend::encoded_array::NoVersion,
	>;
	type TreeBackend<'a> = historied_db::historied::encoded_array::EncodedArray<
		'a,
		historied_db::historied::linear::Linear<Vec<u8>, u64, LinearBackend<'a>>,
		historied_db::historied::encoded_array::NoVersion,
	>;
	// Warning we use Vec<u8> instead of Some(Vec<u8>) to be able to use encoded_array.
	// None is &[0] when Some are postfixed with a 1. TODO use a custom type instead.
	pub type HValue<'a> = Tree<u32, u64, Vec<u8>, TreeBackend<'a>, LinearBackend<'a>>;
}
*/

type ChangesJournal<Db> = historied_db::management::JournalForMigrationBasis<
	// Note that it is reversed state, we use block number first for ordering consideration.
	(u64, u32),
	Vec<u8>,
	Db,
	snapshot_db_conf::JournalChanges,
>;

fn rev_index(index: &(u32, u64)) -> (u64, u32) {
	(index.1, index.0)
}

mod nodes_backend {
	use super::SnapshotColumnPrefixes;
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
		const STORAGE_PREFIX: &'static [u8] = &[SnapshotColumnPrefixes::BranchNodes as u8];
	}

	impl NodesMeta for MetaBlocks {
		const APPLY_SIZE_LIMIT: bool = true;
		// This needs to be less than for `MetaBranches`, the point is to
		// be able to store multiple branche in the immediate storage and
		// avoid having a single branch occupy the whole item.
		const MAX_NODE_LEN: usize = 512;
		const MAX_NODE_ITEMS: usize = 4;
		const STORAGE_PREFIX: &'static [u8] = &[SnapshotColumnPrefixes::BlockNodes as u8];
	}
}

mod nodes_nodiff {
	use historied_db::{
		historied::Data,
		historied::tree::Tree,
		management::tree::ForkPlan,
	};
	use super::nodes_backend::{MetaBlocks, MetaBranches};
	use crate::historied_nodes::nodes_backend::{TreeBackend, LinearBackend};

	/// HValue variant alias for `HValueType::SingleNodeXDelta`.
	pub type HValue = Tree<
		u32,
		u64,
		Option<Vec<u8>>,
		TreeBackend<Option<Vec<u8>>, MetaBranches, MetaBlocks>,
		LinearBackend<Option<Vec<u8>>, MetaBlocks>,
	>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		Ok(v.get(current_state).flatten())
	}
}

mod nodes_xdelta {
	use historied_db::{
		historied::aggregate::Sum as _,
		historied::tree::{Tree, aggregate::Sum as TreeSum},
		management::tree::ForkPlan,
		historied::aggregate::xdelta::{BytesDelta, BytesDiff},
	};
	use super::nodes_backend::{MetaBlocks, MetaBranches};
	use crate::historied_nodes::nodes_backend::{TreeBackend, LinearBackend};

	type BytesDiffStorage = <BytesDiff as historied_db::historied::Value>::Storage;

	/// HValue variant alias for `HValueType::SingleNodeXDelta`.
	pub type HValue = Tree<
		u32,
		u64,
		BytesDiff,
		TreeBackend<BytesDiff, MetaBranches, MetaBlocks>,
		LinearBackend<BytesDiffStorage, MetaBlocks>,
	>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		let v = TreeSum::<_, _, BytesDelta, _, _>(&v);
		let v = v.get_sum(current_state);
		Ok(v.map(|v| v.into()).flatten())
	}
}

mod single_node_nodiff {
	use historied_db::{
		historied::Data,
		historied::tree::Tree,
		management::tree::ForkPlan,
	};

	type LinearBackend = historied_db::backend::in_memory::MemoryOnly8<
		Option<Vec<u8>>,
		u64,
	>;

	type TreeBackend = historied_db::backend::in_memory::MemoryOnly4<
		historied_db::historied::linear::Linear<Option<Vec<u8>>, u64, LinearBackend>,
		u32,
	>;

	/// HValue variant alias for `HValueType::SingleNodeXDelta`.
	pub type HValue = Tree<u32, u64, Option<Vec<u8>>, TreeBackend, LinearBackend>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		Ok(v.get(current_state).flatten())
	}
}

mod single_node_xdelta {
	use historied_db::{
		historied::aggregate::Sum as _,
		historied::tree::{Tree, aggregate::Sum as TreeSum},
		management::tree::ForkPlan,
		historied::aggregate::xdelta::{BytesDelta, BytesDiff},
	};

	type LinearBackend = historied_db::backend::in_memory::MemoryOnly8<
		<BytesDiff as historied_db::historied::Value>::Storage,
		u64,
	>;

	type TreeBackend = historied_db::backend::in_memory::MemoryOnly4<
		historied_db::historied::linear::Linear<BytesDiff, u64, LinearBackend>,
		u32,
	>;

	/// HValue variant alias for `HValueType::SingleNodeXDelta`.
	pub type HValue = Tree<u32, u64, BytesDiff, TreeBackend, LinearBackend>;

	/// Access current value.
	pub fn value(v: &HValue, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		let v = TreeSum::<_, _, BytesDelta, _, _>(&v);
		let v = v.get_sum(current_state);
		Ok(v.map(|v| v.into()).flatten())
	}
}

/// Historied value with multiple parallel branches.
/// Support multiple implementation from config.
pub enum HValue {
	NodesNoDiff(nodes_nodiff::HValue, BranchNodes, BlockNodes),
	NodesXDelta(nodes_xdelta::HValue, BranchNodes, BlockNodes),
	SingleNodeNoDiff(single_node_nodiff::HValue),
	SingleNodeXDelta(single_node_xdelta::HValue),
}

/// Compact resolved type from snapshot config.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HValueType {
	NodesNoDiff,
	NodesXDelta,
	SingleNodeNoDiff,
	SingleNodeXDelta,
}

impl HValueType {
	/// Get historied value type corresponding to a given config.
	pub fn resolve(config: &SnapshotDbConf) -> Option<Self> {
		Some(match (&config.diff_mode, &config.no_node_backend) {
			(SnapshotDBMode::Xdelta3Diff, true) => HValueType::SingleNodeXDelta,
			(SnapshotDBMode::Xdelta3Diff, false) => unimplemented!(),
			(SnapshotDBMode::NoDiff, true) => HValueType::SingleNodeNoDiff,
			(SnapshotDBMode::NoDiff, false) => HValueType::NodesNoDiff,
		})
	}
}

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
		match self {
			HValue::NodesNoDiff(inner, branches, blocks) => {
				use historied_db::Trigger;
				inner.trigger_flush();
				branches.apply_transaction(transaction);
				blocks.apply_transaction(transaction);
			},
			HValue::NodesXDelta(inner, branches, blocks) => {
				use historied_db::Trigger;
				inner.trigger_flush();
				branches.apply_transaction(transaction);
				blocks.apply_transaction(transaction);
			},
			HValue::SingleNodeNoDiff(..) => (),
			HValue::SingleNodeXDelta(..) => (),
		}
	}

	/// Instantiate new value.
	pub fn new(
		key: &[u8],
		value_at: Vec<u8>,
		state: &Latest<(u32, u64)>,
		kind: HValueType,
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Self {
		match kind {
			HValueType::NodesNoDiff => {
				let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
				HValue::NodesNoDiff(
					nodes_nodiff::HValue::new(Some(value_at), state, context),
					branch_nodes,
					block_nodes,
				)
			},
			HValueType::NodesXDelta => {
				let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
				HValue::NodesXDelta(
					nodes_xdelta::HValue::new(BytesDiff::Value(value_at), state, context),
					branch_nodes,
					block_nodes,
				)
			},
			HValueType::SingleNodeNoDiff => HValue::SingleNodeNoDiff(
				single_node_nodiff::HValue::new(Some(value_at), state, ((), ())),
			),
			HValueType::SingleNodeXDelta => HValue::SingleNodeXDelta(
				single_node_xdelta::HValue::new(BytesDiff::Value(value_at), state, ((), ())),
			),
		}
	}

	/// Decode existing value.
	pub fn decode_with_context(
		key: &[u8],
		encoded: &[u8],
		kind: HValueType,
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Option<Self> {
		match kind {
			HValueType::NodesNoDiff => {
				let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
				Some(HValue::NodesNoDiff(
					nodes_nodiff::HValue::decode_with_context(&mut &encoded[..], &context)?,
					branch_nodes,
					block_nodes,
				))
			},
			HValueType::NodesXDelta => {
				let (context, branch_nodes, block_nodes) = Self::build_context(key, nodes_db);
				Some(HValue::NodesXDelta(
					nodes_xdelta::HValue::decode_with_context(&mut &encoded[..], &context)?,
					branch_nodes,
					block_nodes,
				))
			},
			HValueType::SingleNodeNoDiff => Some(HValue::SingleNodeNoDiff(
				single_node_nodiff::HValue::decode_with_context(&mut &encoded[..], &((), ()))?,
			)),
			HValueType::SingleNodeXDelta => Some(HValue::SingleNodeXDelta(
				single_node_xdelta::HValue::decode_with_context(&mut &encoded[..], &((), ()))?,
			)),
		}
	}

	/// Access existing value.
	fn value(&self, current_state: &ForkPlan<u32, u64>) -> Result<Option<Vec<u8>>, String> {
		Ok(match self {
			HValue::NodesNoDiff(inner, _, _) => nodes_nodiff::value(inner, current_state)?,
			HValue::NodesXDelta(inner, _, _) => nodes_xdelta::value(inner, current_state)?,
			HValue::SingleNodeNoDiff(inner) => single_node_nodiff::value(inner, current_state)?,
			HValue::SingleNodeXDelta(inner) => single_node_xdelta::value(inner, current_state)?,
		})
	}

	fn set_first_change(
		&mut self,
		change: Option<Vec<u8>>,
		current_state: &Latest<(u32, u64)>,
		current_state_read: &ForkPlan<u32, u64>,
	) -> Result<UpdateResult<()>, String> {
		Ok(match self {
			HValue::NodesNoDiff(inner, _, _) => {
				inner.set(change, current_state)
			},
			HValue::SingleNodeNoDiff(inner) => {
				inner.set(change, current_state)
			},
			HValue::NodesXDelta(inner, ..) => {
				// TODO facto code with other xdelta
				if let Some(v) = change {
					if let Some(previous) = {
						// we should use previous state, but since we know this
						// is a first write for this state (write only once per keys)
						// current state will always return previous state
						// This assumption may not stand, but we replay something with same
						// effect so it should overwrite existing with same values (idem for nodes
						// as addressing is deterministic).
						let h = TreeSum::<_, _, BytesDelta, _, _>(inner);
						h.get_sum(current_state_read)
					} {
						let target_value = Some(v).into();
						let v_diff = historied_db::historied::aggregate::xdelta::substract(&previous, &target_value).into();
						inner.set(v_diff, current_state)
					} else {
						inner.set(BytesDiff::Value(v), current_state)
					}
				} else {
					inner.set(BytesDiff::None, current_state)
				}
			},
			HValue::SingleNodeXDelta(inner) => {
				if let Some(v) = change {
					if let Some(previous) = {
						// we should use previous state, but since we know this
						// is a first write for this state (write only once per keys)
						// current state will always return previous state
						// This assumption may not stand, but we replay something with same
						// effect so it should overwrite existing with same values (idem for nodes
						// as addressing is deterministic).
						let h = TreeSum::<_, _, BytesDelta, _, _>(inner);
						h.get_sum(current_state_read)
					} {
						let target_value = Some(v).into();
						let v_diff = historied_db::historied::aggregate::xdelta::substract(&previous, &target_value).into();
						inner.set(v_diff, current_state)
					} else {
						inner.set(BytesDiff::Value(v), current_state)
					}
				} else {
					inner.set(BytesDiff::None, current_state)
				}
			},
		})
	}

	fn encode(&self) -> Vec<u8> {
		match self {
			HValue::NodesNoDiff(inner, _, _) => inner.encode(),
			HValue::NodesXDelta(inner, _, _) => inner.encode(),
			HValue::SingleNodeNoDiff(inner) => inner.encode(),
			HValue::SingleNodeXDelta(inner) => inner.encode(),
		}
	}

	/// Migrate HValue
	fn migrate<B: BlockT>(
		&mut self,
		migrate: &mut historied_db::management::Migrate<B::Hash, TreeManagement<B::Hash>>,
	) -> UpdateResult<()> {
		match self {
			HValue::NodesXDelta(inner, _, _) => {
				let res = inner.migrate(migrate.migrate());
				if !matches!(&res, UpdateResult::Unchanged) {
					use historied_db::Trigger;
					inner.trigger_flush();
				}
				res
			},
			HValue::NodesNoDiff(inner, _, _) => {
				let res = inner.migrate(migrate.migrate());
				if !matches!(&res, UpdateResult::Unchanged) {
					use historied_db::Trigger;
					inner.trigger_flush();
				}
				res
			},
			HValue::SingleNodeNoDiff(inner) => inner.migrate(migrate.migrate()),
			HValue::SingleNodeXDelta(inner) => inner.migrate(migrate.migrate()),
		}
	}
}

/// Key value db at a given block for an historied DB.
pub struct HistoriedDB {
	current_state: ForkPlan<u32, u64>,
	db: Arc<dyn OrderedDatabase<DbHash>>,
	/// Configuration for this db.
	config: SnapshotDbConf,
	/// Historied value type for the given conf.
	hvalue_type: HValueType,
	/// Db for storing nodes.
	nodes_db: Arc<dyn Database<DbHash>>,
}

impl HistoriedDB {
	fn storage_inner(
		&self,
		child_info: Option<&ChildInfo>,
		key: &[u8],
		column: u32,
	) -> Result<Option<Vec<u8>>, String> {
		let key = child_prefixed_key(child_info, key);
		if let Some(v) = self.db.get(column, key.as_slice()) {
			HistoriedDB::decode_inner(key.as_slice(), v.as_slice(), &self.current_state, self.hvalue_type, &self.nodes_db)
		} else {
			Ok(None)
		}
	}

	fn decode_inner(
		key: &[u8],
		encoded: &[u8],
		current_state: &ForkPlan<u32, u64>,
		hvalue_type: HValueType,
		nodes_db: &Arc<dyn Database<DbHash>>,
	) -> Result<Option<Vec<u8>>, String> {
		let h_value = HValue::decode_with_context(key, &mut &encoded[..], hvalue_type, nodes_db)
			.ok_or_else(|| format!("KVDatabase decode error for k {:?}, v {:?}", key, encoded))?;
		Ok(h_value.value(current_state)?)
	}
}

impl KVBackend for HistoriedDB {
	fn use_as_primary(&self) -> bool {
		self.config.primary_source
	}

	fn assert_value(&self) -> bool {
		self.config.debug_assert
	}

	fn storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, String> {
		self.storage_inner(child, key, crate::columns::STATE_SNAPSHOT)
	}

	fn next_storage(
		&self,
		child: Option<&ChildInfo>,
		key: &[u8],
	) -> Result<Option<(Vec<u8>, Vec<u8>)>, String> {
		let trie_prefix = child_prefixed_key(child, &[]);
		let start = child_prefixed_key(child, key);

		let mut iter = self.db.iter_from(crate::columns::STATE_SNAPSHOT, start.as_slice());
		while let Some((key, value)) = iter.next() {
			if !key.starts_with(trie_prefix.as_slice()) {
				return Ok(None);
			}
			if key == start {
				continue;
			}
			if let Some(value) = HistoriedDB::decode_inner(
				key.as_slice(),
				value.as_slice(),
				&self.current_state,
				self.hvalue_type,
				&self.nodes_db,
			)? {
				return Ok(Some((key, value)));
			}
		}
		Ok(None)
	}
}

impl HistoriedDB {
	/// Iterator on key values.
	pub fn iter<'a>(&'a self, column: u32) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a {
		self.db.iter(column).filter_map(move |(k, v)| {
			let v = HValue::decode_with_context(&k[..], &mut &v[..], self.hvalue_type, &self.nodes_db)
				.or_else(|| {
					warn!("Invalid historied value k {:?}, v {:?}", k, v);
					None
				})
				.expect("Invalid encoded historied value, DB corrupted");
			let v = v.value(&self.current_state)
				.expect("Invalid encoded historied value, DB corrupted");
			v.map(|v| (k, v))
		})
	}

	/// Iterator on key values, starting at a given position.
	pub fn iter_from<'a>(&'a self, start: &[u8], column: u32) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a {
		self.db.iter_from(column, start).filter_map(move |(k, v)| {
			let v = HValue::decode_with_context(&k[..], &mut &v[..], self.hvalue_type, &self.nodes_db)
				.or_else(|| {
					warn!("decoding fail for k {:?}, v {:?}", k, v);
					None
				})
				.expect("Invalid encoded historied value, DB corrupted");
			let v = v.value(&self.current_state)
				.expect("Invalid encoded historied value, DB corrupted");
			v.map(|v| (k, v))
		})
	}
}

/// Key value db change for at a given block of an historied DB.
pub struct HistoriedDBMut<DB> {
	/// Branch head indexes to change values of a latest block.
	pub current_state: Latest<(u32, u64)>,
	/// Branch head indexes to change values of a latest block.
	pub current_state_read: ForkPlan<u32, u64>,
	/// Inner database to modify historied values.
	pub db: DB,
	/// Configuration for this db.
	pub config: SnapshotDbConf,
	/// Historied value type for the given conf.
	pub hvalue_type: HValueType,
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
		child_info: Option<&ChildInfo>,
		k: &[u8],
		change: Option<Vec<u8>>,
		change_set: &mut Transaction<DbHash>,
		journal_changes: Option<&mut Vec<Vec<u8>>>,
	) {
		let key = child_prefixed_key(child_info, k);
		self.update_single_inner(key, change, change_set, crate::columns::STATE_SNAPSHOT, journal_changes);
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
			Some(HValue::decode_with_context(k, &mut &histo[..], self.hvalue_type, &self.nodes_db)
				.expect("Bad encoded value in db, closing"))
		} else {
			if change.is_none() {
				return;
			}
			None
		};
		match if let Some(mut histo) = histo {
			let update = histo.set_first_change(change, &self.current_state, &self.current_state_read)
				.expect("Could not write change in snapshot db, DB corrupted");
			(histo, update)
		} else {
			if let Some(v) = change {
				let value = HValue::new(k, v, &self.current_state, self.hvalue_type, &self.nodes_db);
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

	fn unchecked_new_single_inner(
		&mut self,
		k: Vec<u8>,
		v: Vec<u8>,
		change_set: &mut Transaction<DbHash>,
		column: u32,
		journal_changes: Option<&mut Vec<Vec<u8>>>,
	) {
		let mut value = HValue::new(k.as_slice(), v, &self.current_state, self.hvalue_type, &self.nodes_db);
		value.apply_nodes_backend_to_transaction(change_set); // should be no ops, but cost nothing to call
		let value = value.encode();
		change_set.set_from_vec(column, &k, value);
		journal_changes.map(|keys| keys.push(k));
		// no need for no value set
	}
}

/// Consumer with transactional support.
///
/// Read journaled keys and update inner transaction with requires
/// migration changes.
pub struct TransactionalConsumer<B: BlockT> {
	/// Storage to use.
	pub storage: SnapshotDb<B>,
	/// Transaction to update on migrate.
	pub pending: Arc<RwLock<Transaction<DbHash>>>,
}

type TreeManagement<H> = crate::tree_management::TreeManagement<H, TreeManagementPersistence>;

impl<B> historied_db::management::ManagementConsumer<B::Hash, TreeManagement<B::Hash>> for TransactionalConsumer<B>
	where
		B: BlockT,
{
	fn migrate(&self, migrate: &mut historied_db::management::Migrate<B::Hash, TreeManagement<B::Hash>>) {
		let mut keys_to_migrate = std::collections::BTreeSet::<Vec<u8>>::new();
		if self.storage.do_journals() {
			let (prune, state_changes) = migrate.migrate().touched_state();
			// this db is transactional.
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
		};

		let mut pending = self.pending.write();
		let hvalue_type = self.storage.hvalue_type;
		let column = crate::columns::STATE_SNAPSHOT;
		let mut process_key = |
			k: &[u8], histo: Vec<u8>,
			nodes_db: &Arc<dyn Database<DbHash>>,
		| {
			let mut histo = HValue::decode_with_context(k, &mut &histo[..], hvalue_type, nodes_db)
				.expect("Bad encoded value in db, closing");
			match histo.migrate::<B>(migrate) {
				historied_db::UpdateResult::Changed(()) => {
					histo.apply_nodes_backend_to_transaction(&mut pending);
					pending.set_from_vec(column, k, histo.encode());
				},
				historied_db::UpdateResult::Cleared(()) => {
					histo.apply_nodes_backend_to_transaction(&mut pending);
					pending.remove(column, k);
				},
				historied_db::UpdateResult::Unchanged => (),
			}
		};

		if self.storage.do_journals() {
			for k in keys_to_migrate {
				if let Some(histo) = self.storage.ordered_db.get(column, k.as_slice()) {
					process_key(k.as_slice(), histo, &self.storage.nodes_db);
				} else {
					continue;
				};
			}
		} else {
			for (k, histo) in self.storage.ordered_db.iter(column) {
				process_key(k.as_slice(), histo, &self.storage.nodes_db);
			}
		}
	}
}
