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

//! Linear historied data.

#[cfg(not(feature = "std"))]
use sp_std::{vec::Vec, vec};
use sp_std::marker::PhantomData;
use crate::{StateDBRef, UpdateResult, InMemoryStateDBRef, StateDB};
use hash_db::{PlainDB, PlainDBRef};
use crate::Latest;
use codec::{Encode, Decode};
use sp_std::ops::Range;
use crate::{Context, DecodeWithContext};

pub mod linear;
pub mod tree;

/// Trait for historied value
pub trait ValueRef<V> {
	/// State to query for this value.
	type S;

	/// Get value at this state.
	fn get(&self, at: &Self::S) -> Option<V>;

	/// Check if a value exists at this state.
	fn contains(&self, at: &Self::S) -> bool;

	/// Check if this is empty.
	fn is_empty(&self) -> bool;
}

// TODO EMCH refact with 'a for inner value
// and a get value type (see test on rust playground).
// So we only got ValueRef type.
pub trait InMemoryValueRef<V>: ValueRef<V> {
	/// Get reference to the value at this state.
	fn get_ref(&self, at: &Self::S) -> Option<&V>;
}

pub trait InMemoryValueSlice<V>: ValueRef<V> {
	/// Get reference to the value at this state.
	fn get_slice(&self, at: &Self::S) -> Option<&[u8]>;
}

pub trait InMemoryValueRange<S> {
	/// Get reference to the value from which this slice can be build.
	fn get_range(slice: &[u8], at: &S) -> Option<Range<usize>>;
}

/// Trait for historied value.
pub trait Value<V>: ValueRef<V> + Context {
	/// State to use for changing value.
	/// We use a different state than
	/// for querying as it can use different
	/// constraints.
	type SE: StateIndex<Self::Index>;

	/// Index a single history item.
	type Index;

	/// GC strategy that can be applied.
	/// GC can be run in parallel, it does not
	/// make query incompatible.
	type GC;
	/// Like gc but operation require a lock on the db
	/// and all pending state are invalidated.
	type Migrate;

	/// Contextiate a new value.
	fn new(value: V, at: &Self::SE, init: Self::Context) -> Self;

	/// Insert or update a value.
	fn set(&mut self, value: V, at: &Self::SE) -> UpdateResult<()>;

	/// Discard history at.
	fn discard(&mut self, at: &Self::SE) -> UpdateResult<Option<V>>;

	/// Garbage collect value.
	fn gc(&mut self, gc: &Self::GC) -> UpdateResult<()>;

	/// Check if migrate should be applied if this state index
	/// got modified.
	fn is_in_migrate(index: &Self::Index, gc: &Self::Migrate) -> bool;

	/// Migrate a value, all value needs to migrate at once, as
	/// the content will not be valid with post-migration states
	/// otherwise.
	fn migrate(&mut self, mig: &Self::Migrate) -> UpdateResult<()>;
}

/// Returns pointer to in memory value.
pub trait InMemoryValue<V>: Value<V> {
	/// Get latest value, can apply updates.
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V>;

	/// Similar to value set but returning a pointer on replaced or deleted value.
	/// If the value is change but history is kept (new state), no pointer is returned.
	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>>;
}

/// Same as `Value` but allows using unsafe index and failing if incorrect.
/// This involves some additional computation to check correctness.
/// It is also usefull when some asumption are not strong enough, for
/// instance if `Value` is subject to concurrent access.
/// TODO an entry api would be more proper (returning optional entry).
pub trait ConditionalValueMut<V>: Value<V> {
	type IndexConditional;
	/// Does state allow modifying this value.
	/// If value is added as parameter, we do not allow overwrite.
	fn can_set(&self, no_overwrite: Option<&V>, at: &Self::IndexConditional) -> bool;
	/// Do update if state allows it, otherwhise return None.
	fn set_if_possible(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>>;

	/// Do update if state allows it and we are not erasing an existing value, otherwhise return None.
	fn set_if_possible_no_overwrite(&mut self, value: V, at: &Self::IndexConditional) -> Option<UpdateResult<()>>;
}

/// An entry at a given history index.
#[derive(Debug, Clone, Encode, Decode, PartialEq, Eq)]
pub struct HistoriedValue<V, S> {
	/// The stored value.
	pub value: V,
	/// The state this value belongs to.
	pub state: S,
}

impl<V, S> Context for HistoriedValue<V, S>
	where
		V: Context,
{
	type Context = V::Context;
}

impl<V, S> DecodeWithContext for HistoriedValue<V, S>
	where
		V: DecodeWithContext,
		S: Decode,
{
	fn decode_with_context(mut input: &[u8], init: &Self::Context) -> Option<Self> {
		V::decode_with_context(input, init)
			.and_then(|value| S::decode(&mut input).ok()
				.map(|state| HistoriedValue {
					value,
					state,
				})
			)
	}
}

impl<V, S> HistoriedValue<V, S> {
	/// Apply modification over historied value reference and state.
	pub fn apply<V2, F: Fn((&mut V, &mut S))>(&mut self, f: F) {
		let HistoriedValue { value, state } = self;
		f((value, state))
	}

	/// Map inner historied value.
	pub fn map<V2, F: Fn(V) -> V2>(self, f: F) -> HistoriedValue<V2, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: f(value), state }
	}
}

impl<'a, V: 'a, S: Clone> HistoriedValue<V, S> {
	/// Get historied reference to the value.
	pub fn as_ref(&self) -> HistoriedValue<&V, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: &value, state: state.clone() }
	}

	/// Map over a reference of value.
	pub fn map_ref<V2: 'a, F: Fn(&'a V) -> V2>(&'a self, f: F) -> HistoriedValue<V2, S> {
		let HistoriedValue { value, state } = self;
		HistoriedValue { value: f(value), state: state.clone() }
	}
}

impl<V, S> From<(V, S)> for HistoriedValue<V, S> {
	fn from(input: (V, S)) -> HistoriedValue<V, S> {
		HistoriedValue { value: input.0, state: input.1 }
	}
}

/// Implementation for plain db.
pub struct BTreeMap<K, V, H: Context>(pub(crate) sp_std::collections::btree_map::BTreeMap<K, H>, H::Context, PhantomData<V>);

impl<K: Ord, V, H: Context> BTreeMap<K, V, H> {
	pub fn new(init: H::Context) -> Self {
		BTreeMap(sp_std::collections::btree_map::BTreeMap::new(), init, PhantomData)
	}
}

impl<K: Ord, V: Clone, H: ValueRef<V> + Context> StateDBRef<K, V> for BTreeMap<K, V, H> {
	type S = H::S;

	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.0.get(key)
			.and_then(|h| h.get(at))
	}

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.0.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

// note that the constraint on state db ref for the associated type is bad (forces V as clonable).
impl<K: Ord, V, H: InMemoryValueRef<V> + Context> InMemoryStateDBRef<K, V> for BTreeMap<K, V, H> {
	type S = H::S;

	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V> {
		self.0.get(key)
			.and_then(|h| h.get_ref(at))
	}
}

impl<K: Ord + Clone, V: Clone + Eq, H: Value<V>> StateDB<K, V> for BTreeMap<K, V, H> {
	type SE = H::SE;
	type GC = H::GC;
	type Migrate = H::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(hist) = self.0.get_mut(&key) {
			hist.set(value, at);
		} else {
			self.0.insert(key, H::new(value, at, self.1.clone()));
		}
	}

	fn remove(&mut self, key: &K, at: &Self::SE) {
		match self.0.get_mut(&key).map(|h| h.discard(at)) {
			Some(UpdateResult::Cleared(_)) => (),
			_ => return,
		}
		self.0.remove(&key);
	}

	fn gc(&mut self, gc: &Self::GC) {
		// retain for btreemap missing here.
		let mut to_remove = Vec::new();
		for (key, h) in self.0.iter_mut() {
			match h.gc(gc) {
				UpdateResult::Cleared(_) => (),
				_ => break,
			}
			to_remove.push(key.clone());
		}
		for k in to_remove {
			self.0.remove(&k);
		}
	}

	fn migrate(&mut self, mig: &mut Self::Migrate) {
		// retain for btreemap missing here.
		let mut to_remove = Vec::new();
		for (key, h) in self.0.iter_mut() {
			match h.migrate(mig) {
				UpdateResult::Cleared(_) => (),
				_ => break,
			}
			to_remove.push(key.clone());
		}
		for k in to_remove {
			self.0.remove(&k);
		}
	}
}

/// Implementation for plain db.
pub struct PlainDBState<K, DB, H, S> {
	db: DB,
	touched_keys: sp_std::collections::btree_map::BTreeMap<S, Vec<K>>, // TODO change that by a journal trait!!
	_ph: PhantomData<H>,
}

impl<K, V: Clone, H: ValueRef<V>, DB: PlainDBRef<K, H>, S> StateDBRef<K, V> for PlainDBState<K, DB, H, S> {
	type S = H::S;

	fn get(&self, key: &K, at: &Self::S) -> Option<V> {
		self.db.get(key)
			.and_then(|h| h.get(at))
	}

	fn contains(&self, key: &K, at: &Self::S) -> bool {
		self.db.get(key)
			.map(|h| h.contains(at))
			.unwrap_or(false)
	}
}

impl<
	K: Ord + Clone,
	V: Clone + Eq,
	H: Value<V, Context = ()>,
	DB: PlainDBRef<K, H> + PlainDB<K, H>,
> StateDB<K, V> for PlainDBState<K, DB, H, H::Index>
	where
			H::Index: Clone + Ord,
{
	type SE = H::SE;
	type GC = H::GC;
	type Migrate = H::Migrate;

	fn emplace(&mut self, key: K, value: V, at: &Self::SE) {
		if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
			match hist.set(value, at) {
				UpdateResult::Changed(_) => self.db.emplace(key.clone(), hist),
				UpdateResult::Cleared(_) => self.db.remove(&key),
				UpdateResult::Unchanged => return,
			}
		} else {
			self.db.emplace(key.clone(), H::new(value, at, ()));
		}
		self.touched_keys.entry(at.index()).or_default().push(key);
	}

	fn remove(&mut self, key: &K, at: &Self::SE) {
		if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
			match hist.discard(at) {
				UpdateResult::Changed(_) => self.db.emplace(key.clone(), hist),
				UpdateResult::Cleared(_) => self.db.remove(&key),
				UpdateResult::Unchanged => return,
			}
		}
		self.touched_keys.entry(at.index()).or_default().push(key.clone());
	}

	fn gc(&mut self, gc: &Self::GC) {
		let mut keys: sp_std::collections::btree_set::BTreeSet<_> = Default::default();
		for touched in self.touched_keys.values() {
			for key in touched.iter() {
				keys.insert(key.clone());
			}
		}
		for key in keys {
			if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
				match hist.gc(gc) {
					UpdateResult::Changed(_) => self.db.emplace(key, hist),
					UpdateResult::Cleared(_) => self.db.remove(&key),
					UpdateResult::Unchanged => break,
				}
			}
		}
	}

	fn migrate(&mut self, mig: &mut Self::Migrate) {
		// TODO this is from old gc but seems ok (as long as touched is complete).
		// retain for btreemap missing here.
		let mut states = Vec::new();
		// TODO do we really want this error prone prefiltering??
		for touched in self.touched_keys.keys() {
			if H::is_in_migrate(touched, mig) {
				states.push(touched.clone());
			}
		}
		let mut keys: sp_std::collections::btree_set::BTreeSet<_> = Default::default();
		for state in states {
			if let Some(touched) = self.touched_keys.remove(&state) {
				for k in touched {
					keys.insert(k);
				}
			}
		}
		self.touched_keys.clear();
		for key in keys {
			if let Some(mut hist) = <DB as PlainDB<_, _>>::get(&self.db, &key) {
				match hist.migrate(mig) {
					UpdateResult::Changed(_) => self.db.emplace(key, hist),
					UpdateResult::Cleared(_) => self.db.remove(&key),
					UpdateResult::Unchanged => break,
				}
			}
		}
	}
}

/// Associate a state index for a given state reference
pub trait StateIndex<I> {
	/// Get individal state index.
	fn index(&self) -> I;
	/// Get reference to individal state index.
	fn index_ref(&self) -> &I;
}

impl<S: Clone> StateIndex<S> for Latest<S> {
	fn index(&self) -> S {
		self.latest().clone()
	}
	fn index_ref(&self) -> &S {
		self.latest()
	}
}
