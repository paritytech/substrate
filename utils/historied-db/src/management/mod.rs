// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! History state storage and management.
//!
//! This associate a tag (for instance a block hash),
//! with historical state index.
//! Tags are therefore usually associated with the generic parameter `H`.
//!
//! Given a tag, it allows building different states for different operation
//! on historical data.

/// Forkable state management implementations.
pub mod tree;

use sp_std::{vec::Vec, boxed::Box, marker::PhantomData};
use crate::{Ref, StateIndex};

/// Management maps a historical tag of type `H` with its different db states representation.
pub trait Management<H> {
	/// Internal index associated with a given tag.
	type Index;

	/// Attached db state needed for query operation
	/// on historical data.
	type S: StateIndex<Self::Index>;

	/// Attached db gc strategy.
	/// Can be applied on any historical data to
	/// clean up.
	type GC;

	/// Returns the associated inner index of a given historical tag.
	///
	/// Mutable access is for caching only.
	fn get_internal_index(&mut self, tag: &H) -> Option<Self::Index>;

	/// Returns the historical read state representation for a given historical tag.
	///
	/// Mutable access is for caching only.
	fn get_db_state(&mut self, tag: &H) -> Option<Self::S>;

	/// Reverse lookup fo a tag given an internal index.
	/// This can be a slow implementation, and should not be
	/// use for common operations.
	fn reverse_lookup(&mut self, index: &Self::Index) -> Option<H>;

	/// Returns a Gc to cleanup historical data.
	/// If the Gc is not relevant (eg after a migration), simply return None.
	fn get_gc(&self) -> Option<Ref<Self::GC>>;
}

pub trait ManagementMut<H>: Management<H> + Sized {
	/// Attached db state needed for update operation
	/// on historical data.
	type SE: StateIndex<Self::Index>;

	/// Attached db migrate definition.
	/// Can be applied on any historical data
	/// to migrate to a post migration management state.
	type Migrate;

	/// Return state mut for state but only if state exists and is
	/// a terminal writeable leaf (if not you need to create new branch 
	/// from previous state to write).
	fn get_db_state_mut(&mut self, tag: &H) -> Option<Self::SE>;

	/// Get a cursor over the last change of ref (when adding or removing).
	fn latest_state(&mut self) -> Self::SE;

	/// Return latest added external index, can return None
	/// if reverted.
	fn latest_external_state(&mut self) -> Option<H>;

	/// Force change value of latest external state.
	fn force_latest_external_state(&mut self, index: H);

	/// see migrate. When running thes making a backup of this management
	/// state is usually a good idea (this method does not manage
	/// backup or rollback).
	fn get_migrate(&mut self) -> Migrate<H, Self>;

	/// report a migration did run successfully, will update management state
	/// accordingly.
	/// All previously fetch states are unvalid.
	/// There is no type constraint of this, because migration is a specific
	/// case the general type should not be complexified.
	///
	/// TODO consider removing applied migrate, it seems easier to use a transactional
	/// backend over historied management.
	fn applied_migrate(&mut self);
}

/// This trait is for mapping a given state to the DB opaque inner state.
pub trait ForkableManagement<H>: ManagementMut<H> {
	/// Do we keep trace of changes.
	const JOURNAL_CHANGES: bool;

	/// Fork state, the state to use for forking.
	///
	/// Usually should be `Self::Index` or a type wrapping it.
	/// (fork doable at any given index if index is defined,
	/// no need for additional information).
	type SF: StateIndex<Self::Index>;

	/// Simple access to fork state type.
	/// This operation should usually be a noops.
	fn from_index(index: Self::Index) -> Self::SF;

	fn get_db_state_for_fork(&mut self, tag: &H) -> Option<Self::SF>;

	/// Useful to fork in a independant branch (eg no parent reference found).
	fn init_state_fork(&mut self) -> Self::SF;

	fn latest_state_fork(&mut self) -> Self::SF {
		let se = self.latest_state();
		Self::from_index(se.index())
	}

	/// Add a tagged state following a given fork state.
	///
	/// This only succeed for a valid `at`, and can either append to an
	/// existing branch or create a new branch.
	fn append_external_state(&mut self, tag: H, at: &Self::SF) -> Option<Self::SE>;

	/// `append_external_state` variant with tag as parameter.
	///
	/// Note that this trait could be simplified to this function only.
	/// But fork state can generally be extracted from `Self::SE` or `Self::S`
	/// and skip one query.
	fn try_append_external_state(&mut self, state: H, at: &H) -> Option<Self::SE> {
		self.get_db_state_for_fork(&at)
			.and_then(|at| self.append_external_state(state, &at))
	}
}

/// Latest from fork only, this is for use case of aggregable
/// data cache: to store the aggregate cache.
/// (it only record a single state per fork!! but still need to resolve
/// if new fork is needed so hold almost as much info as a forkable management).
/// NOTE aggregable data cache is a cache that reply to locality
/// (a byte trie with locks that invalidate cache when set storage is call).
/// get_aggregate(aggregate_key)-> option<StructAggregate>
/// set_aggregate(aggregate_key, struct aggregate, [(child_info, lockprefixes)]).
pub trait ForkableHeadManagement<H>: Management<H> {
	fn register_external_state_head(&mut self, state: H, at: &Self::S) -> Self::S;
	fn try_register_external_state_head(&mut self, state: H, at: &H) -> Option<Self::S> {
		self.get_db_state(at).map(|at| self.register_external_state_head(state, &at))
	}
}

/// Type holding a state db to lock the management, until applying migration.
pub struct Migrate<'a, H, M: ManagementMut<H>>(&'a mut M, M::Migrate, PhantomData<H>);

impl<'a, H, M: ManagementMut<H>> Migrate<'a, H, M> {
	pub fn new(management: &'a mut M, migrate: M::Migrate) -> Self {
		Migrate(management, migrate, PhantomData)
	}

	pub fn applied_migrate(self) {
		self.0.applied_migrate();
	}
	/// When using management from migrate,
	/// please unsure that you are not modifying
	/// management state in an incompatible way
	/// with the migration.
	pub fn management(&mut self) -> &mut M {
		self.0
	}
	pub fn migrate(&mut self) -> &mut M::Migrate {
		&mut self.1
 	}
}

/// Allows to consume event from the state management.
///
/// Current usage is mostly ensuring that migration occurs
/// on every compenent using the state (by registering these
/// components on the state management and implementing `migrate`).
pub trait ManagementConsumer<H, M: ManagementMut<H>>: Send + Sync + 'static {
	/// A migration runing on the state management,
	/// notice that the migrate parameter can be modified
	/// in case it contains data relative to this particular
	/// consumer. It is responsibility of the implementation
	/// to avoid changing this parameter in a way that would
	/// impact others consumer calls.
	fn migrate(&self, migrate: &mut Migrate<H, M>);
}

/// Cast the consumer to a dyn rust object.
pub fn consumer_to_register<H, M: ManagementMut<H>, C: ManagementConsumer<H, M> + Clone>(c: &C) -> Box<dyn ManagementConsumer<H, M>> {
	Box::new(c.clone())
}

/// Management consumer base implementation.
pub struct JournalForMigrationBasis<S: Ord, K, Db, DbConf> {
	touched_keys: crate::mapped_db::Map<S, Vec<K>, Db, DbConf>,
}

impl<S, K, Db, DbConf> JournalForMigrationBasis<S, K, Db, DbConf>
	where
		S: codec::Codec + Clone + Ord,
		K: codec::Codec + Clone + Ord,
		Db: crate::mapped_db::MappedDB,
		DbConf: crate::mapped_db::MapInfo,
{
	/// Note that if we got no information of the state, using `is_new` as
	/// false is always safe.
	pub fn add_changes(&mut self, db: &mut Db, state: S, mut changes: Vec<K>, is_new: bool) {
		let mut mapping = self.touched_keys.mapping(db);
		let changes = if is_new {
			changes.dedup();
			changes
		} else {
			if let Some(existing) = mapping.get(&state) {
				let mut existing = existing.clone();
				merge_keys(&mut existing, changes);
				existing
			} else {
				changes.dedup();
				changes
			}
		};
		mapping.insert(state, changes);
	}

	/// Get and remove the changes at a given state.
	pub fn remove_changes_at(&mut self, db: &mut Db, state: &S) -> Option<Vec<K>> {
		let mut mapping = self.touched_keys.mapping(db);
		mapping.remove(state)
	}

	/// Get and remove the changes at a before a given state.
	///
	/// The result is aggregated into `result` mutable set.
	pub fn remove_changes_before(
		&mut self,
		db: &mut Db,
		state: &S,
		result: &mut sp_std::collections::btree_set::BTreeSet<K>,
	) {
		let mut mapping = self.touched_keys.mapping(db);
		// TODO can do better with entry iterator (or key iterator at least)
		let mut to_remove = Vec::new();
		for kv in mapping.iter() {
			if &kv.0 < state {
				to_remove.push(kv.0);
			} else {
				break;
			}
		}
		for state in to_remove.into_iter() {
			if let Some(v) = mapping.remove(&state) {
				for k in v {
					result.insert(k);
				}
			}
		}
	}

	/// Restore journals from a given backend database.
	pub fn from_db(db: &Db) -> Self {
		JournalForMigrationBasis {
			touched_keys: crate::mapped_db::Map::default_from_db(&db),
		}
	}
}

fn merge_keys<K: Ord>(origin: &mut Vec<K>, mut keys: Vec<K>) {
	origin.sort_unstable();
	keys.sort_unstable();
	let mut cursor: usize = 0;
	let end = origin.len();
	for key in keys.into_iter() {
		if Some(&key) == origin.last() {
			// skip (avoid duplicate in keys)
		} else if cursor == end {
			origin.push(key);
		} else {
			while cursor != end && origin[cursor] < key {
				cursor += 1;
			}
			if cursor < end && origin[cursor] != key {
				origin.push(key);
			}
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::test::InMemorySimpleDB5;

	#[test]
	fn test_merge_keys() {
		let mut set1 = vec![b"ab".to_vec(), b"bc".to_vec(), b"da".to_vec(), b"ab".to_vec()];
		let set2 = vec![b"rb".to_vec(), b"bc".to_vec(), b"rb".to_vec(), b"ab".to_vec()];
		// note that set1 should not have duplicate, so they are kept, while for set 2 they are removed.
		let res = vec![b"ab".to_vec(), b"ab".to_vec(), b"bc".to_vec(), b"da".to_vec(), b"rb".to_vec()];
		merge_keys(&mut set1, set2);
		assert_eq!(set1, res);
	}

	#[test]
	fn test_journal_for_migration() {
		#[derive(Default, Clone)]
		struct Collection;
		impl crate::mapped_db::MapInfo for Collection {
			const STATIC_COL: &'static [u8] = &[0u8, 0, 0, 0];
		}
		let mut db = InMemorySimpleDB5::new();
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			journal.add_changes(&mut db, 1u32, vec![1u16], true);
			journal.add_changes(&mut db, 2u32, vec![2u16], true);
			journal.add_changes(&mut db, 3u32, vec![3u16], true);
			journal.add_changes(&mut db, 3u32, vec![1u16], false);
			journal.add_changes(&mut db, 8u32, vec![8u16], false);
		}
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), Some(vec![8u16]));
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), None);
			let mut set = std::collections::BTreeSet::new();
			journal.remove_changes_before(&mut db, &3u32, &mut set);
			assert_eq!(journal.remove_changes_at(&mut db, &2u32), None);
			assert_eq!(journal.remove_changes_at(&mut db, &1u32), None);
			let set: Vec<u16> = set.into_iter().collect();
			assert_eq!(set, vec![1u16, 2]);
			assert_eq!(journal.remove_changes_at(&mut db, &3u32), Some(vec![3u16, 1]));
		}
		{
			let mut journal = JournalForMigrationBasis::<u32, u16, _, Collection>::from_db(&db);
			assert_eq!(journal.remove_changes_at(&mut db, &8u32), None);
		}
	}
}
