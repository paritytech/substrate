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

//! Test implementation that favor minimal non scalable in memory
//! implementation.
//!
//! The unique state representation must be sequential (index of an array)
//! and their corresponding mapped internal state is the same index.

use crate::*;
use std::collections::HashMap;
use std::hash::Hash;
use codec::{Encode, Decode};

struct DbElt<K, V> {
	values: HashMap<K, V>,
	previous: StateIndex,
	is_latest: bool,
}

/// The main test Db.
pub struct Db<K, V> {
	db: Vec<Option<DbElt<K, V>>>,
	latest_state: Latest<StateIndex>,
}

/// state index.
type StateIndex = u32;

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Encode, Decode)]
/// State Input (aka hash).
pub struct StateInput(pub u32);

impl StateInput {
	fn to_index(&self) -> StateIndex {
		self.0
	}
}

impl<K, V> Db<K, V> {
	pub fn is_latest(&self, ix: &StateIndex) -> bool {
		self.db.get(*ix as usize).and_then(|o_elt| o_elt.as_ref().map(|elt| elt.is_latest)).unwrap_or(false)
	}

	fn contains(&self, ix: &StateInput) -> bool {
		self.db.get(ix.to_index() as usize).map(|o_elt| o_elt.is_some()).unwrap_or(false)
	}

	fn get_state(&self, state: &StateInput) -> Option<StateIndex> {
		if self.contains(state) {
			Some(state.to_index())
		} else {
			None
		}
	}
}

/// Query path, ordered by latest state first.
/// Note that this could be simplified to just the index.
type Query = Vec<StateIndex>;

impl<K: Hash + Eq, V: Clone> StateDBRef<K, V> for Db<K, V> {
	type S = Query;

	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.get_ref(key, at).cloned()
	}

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.get(key, at).is_some()
	}
}

impl<K: Hash + Eq, V> InMemoryStateDBRef<K, V> for Db<K, V> {
	type S = Query;

	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V> {
		for s in at.iter() {
			if let Some(v) = self.db.get(*s as usize)
				.and_then(|o_elt| o_elt.as_ref().and_then(|elt| elt.values.get(key))) {
				return Some(v)
			}
		}
		None
	}
}

impl<K: Hash + Eq, V: Clone> StateDB<K, V> for Db<K, V> {
	type SE = Latest<StateIndex>;
	type GC = ();
	type Migrate = ();

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		debug_assert!(self.is_latest(at.latest()));
		self.db.get_mut(at.0 as usize).and_then(|o_elt| o_elt.as_mut().map(|elt| &mut elt.values))
			.expect("state should be valid TODO need a return type to emplace")
			.insert(key, value);
	}

	fn remove(&mut self, key: &K, at: &Self::SE) {
		debug_assert!(self.is_latest(at.latest()));
		self.db.get_mut(at.0 as usize).and_then(|o_elt| o_elt.as_mut().map(|elt| &mut elt.values))
			.expect("no removal and no random SE")
			.remove(key);
	}

	fn gc(&mut self, _gc: &Self::GC) { }

	fn migrate(&mut self, _mig: &mut Self::Migrate) { }
}

impl<K: Eq + Hash, V> ManagementRef<StateInput> for Db<K, V> {
	type S = Query;
	type GC = ();
	type Migrate = ();

	fn get_db_state(&mut self, state: &StateInput) -> Option<Self::S> {
		if let Some(mut ix) = self.get_state(state) {
			let mut query = vec![ix];
			loop {
				let next = self.db[ix as usize].as_ref().map(|elt| elt.previous).unwrap_or(ix);
				if next == ix {
					break;
				} else {
					query.push(next);
					ix = next;
				}
			}
			Some(query)
		} else {
			None
		}
	}

	fn get_gc(&self) -> Option<Ref<Self::GC>> {
		None
	}
}

impl<K: Eq + Hash, V> Management<StateInput> for Db<K, V> {
	type SE = Latest<StateIndex>;

	fn init() -> (Self, Self::S) {
		// 0 is defined
		(Db {
			db: vec![
				Some(DbElt {
					values: Default::default(),
					previous: 0,
					is_latest: true,
				})
			],
			latest_state: Latest::unchecked_latest(0),
		}, vec![0])
	}

	fn get_db_state_mut(&mut self, state: &StateInput) -> Option<Self::SE> {
//		if let Some(s) = self.get_state(state) {
		if self.is_latest(&state.to_index()) {
			return Some(Latest::unchecked_latest(state.to_index()))
		}
//		}
		None
	}

	fn latest_state(&mut self) -> Self::SE {
		self.latest_state.clone()
	}

	fn latest_external_state(&mut self) -> Option<StateInput> {
		// unimplemented
		None
	}

	fn force_latest_external_state(&mut self, _state: StateInput) { }

	fn init_state(&mut self) -> Self::SE {
		Latest::unchecked_latest(0)
	}

	fn reverse_lookup(&mut self, state: &Self::S) -> Option<StateInput> {
		if let Some(state) = state.first() {
			// TODO wrong cast.
			let state = StateInput(*state as u32);
			if self.contains(&state) {
				Some(state)
			} else {
				None
			}
		} else {
			None
		}
	}

	fn get_migrate(self) -> (Migrate<StateInput, Self>, Self::Migrate) {
		(Migrate::capture(self), ())
	}

	fn applied_migrate(&mut self) { }
}

impl<K: Eq + Hash, V> ForkableManagement<StateInput> for Db<K, V> {
	const JOURNAL_DELETE: bool = false;

	type SF = StateIndex;

	fn inner_fork_state(&self, s: Self::SE) -> Self::SF {
		s.0
	}

	fn ref_state_fork(&self, s: &Self::S) -> Self::SF {
		s.first().cloned().unwrap_or_default()
	}

	fn get_db_state_for_fork(&mut self, state: &StateInput) -> Option<Self::SF> {
		self.get_state(state)
	}

	fn append_external_state(&mut self, state: StateInput, at: &Self::SF) -> Option<Self::SE> {
		debug_assert!(state.to_index() as usize == self.db.len(), "Test simple implementation only allow sequential new identifier");
		if self.db.get_mut(*at as usize).and_then(|v| v.as_mut().map(|v| {
			v.is_latest = false;
			()
		})).is_none() {
			return None;
		}
		self.db.push(Some(DbElt {
			values: Default::default(),
			previous: *at,
			is_latest: true,
		}));
		let new = self.db.len() as u32 - 1;
		self.latest_state = Latest::unchecked_latest(new);
		Some(Latest::unchecked_latest(new))
	}

	/// Warning this recurse over children and can be slow for some
	/// implementations.
	fn drop_state(&mut self, state: &Self::SF, return_dropped: bool) -> Option<Vec<StateInput>> {
		let mut result = if return_dropped {
			Some(Vec::new())
		} else {
			None
		};
		self.latest_state = Latest::unchecked_latest(
			self.db.get(*state as usize).and_then(|o_elt| o_elt.as_ref().map(|elt| elt.previous)).unwrap_or(0)
		);
		self.rec_drop_state(&mut result, *state);
		result
	}
}

impl<K: Eq + Hash, V> Db<K, V> {
	fn rec_drop_state(&mut self, result: &mut Option<Vec<StateInput>>, state: StateIndex) {
		// initial state is not removable.
		let skip = if state != Default::default() {
			if let Some(o) = self.db.get_mut(state as usize) {
				if o.is_none() {
					return;
				}
				*o = None;
				// TODO wrong cast
				result.as_mut().map(|r| r.push(StateInput(state as u32)));
			} else {
				return;
			}
			0
		} else {
			1
		};
		let rec_calls: Vec<StateIndex> = self.db.iter().enumerate().skip(skip)
			.filter_map(|(ix, elt)| elt.as_ref().and_then(|elt| if elt.previous == state {
			Some(ix as u32)
		} else {
			None
		})).collect();
		for state in rec_calls {
			self.rec_drop_state(result, state);
		}
	}
}
