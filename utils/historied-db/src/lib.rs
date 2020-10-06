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

//! Database for key value with history.

// TODO change all ref to S to a borrow similar to map (most
// of the type S is copied so using reference looks pointless).

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use println;

#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! println {
	() => ($crate::print!("\n"));
	($($arg:tt)*) => ({ })
}

use sp_std::marker::PhantomData;

/// Implementation of historied-db traits
/// using historied values
pub mod historied;

/// Backend structures for historied data storage.
pub mod backend;

/// Tools to work with simple key value
/// collection based dbs (non historied).
pub mod simple_db;

/// Management for state of historied data.
pub mod management;

/// Context associated with item.
/// Main use case here is a backend to fetch
/// additional information.
pub trait Context: Sized {
	type Context: Clone;
}


/// Trigger action on changed data.
pub trait Trigger {
	/// Define if we can trigger.
	const TRIGGER: bool;

	/// Run triggered related action on this element and changed children.
	/// Flush is typically committing to context if needed.
	fn trigger_flush(&mut self);
}


macro_rules! empty_init {
	($type: ty) => {
		impl Context for $type {
			type Context = ();
		}

		impl Trigger for $type {
			const TRIGGER: bool = false;
			fn trigger_flush(&mut self) { }
		}
	}
}
empty_init!(u8);
empty_init!(u16);
empty_init!(u32);
empty_init!(u64);
empty_init!(u128);
impl<V: Context> Context for Option<V> {
	type Context = V::Context;
}

impl<V: Trigger> Trigger for Option<V> {
	const TRIGGER: bool = V::TRIGGER;

	fn trigger_flush(&mut self) {
		if V::TRIGGER {
			self.as_mut().map(|v| v.trigger_flush());
		}
	}
}

impl<V: Context> Context for Vec<V> {
	type Context = V::Context;
}

impl<V: Trigger> Trigger for Vec<V> {
	const TRIGGER: bool = V::TRIGGER;

	fn trigger_flush(&mut self) {
		if V::TRIGGER {
			self.iter_mut().for_each(|v| v.trigger_flush())
		}
	}
}

pub trait InitFrom: Context {
	fn init_from(init: Self::Context) -> Self;
}

pub trait DecodeWithContext: Context {
	fn decode_with_context<I: codec::Input>(input: &mut I, init: &Self::Context) -> Option<Self>;
}

impl<V: Context> InitFrom for Option<V> {
	fn init_from(_init: Self::Context) -> Self {
		None
	}
}

impl<V: Context> InitFrom for Vec<V> {
	fn init_from(_init: Self::Context) -> Self {
		Vec::new()
	}
}

impl<V: codec::Decode + Context> DecodeWithContext for Option<V> {
	fn decode_with_context<I: codec::Input>(input: &mut I, _init: &Self::Context) -> Option<Self> {
		use codec::Decode;
		Self::decode(input).ok()
	}
}

impl<V: codec::Decode + Context> DecodeWithContext for Vec<V> {
	fn decode_with_context<I: codec::Input>(input: &mut I, _init: &Self::Context) -> Option<Self> {
		use codec::Decode;
		Self::decode(input).ok()
	}
}

/// Minimal simple implementation.
#[cfg(any(test, feature = "test-helpers"))]
pub mod test;

use sp_std::vec::Vec;

#[cfg_attr(test, derive(PartialEq, Debug))]
///  result to be able to proceed
/// with further update if the value needs it.
pub enum UpdateResult<T> {
	Unchanged,
	Changed(T),
	Cleared(T),
}

impl<T> UpdateResult<T> {
	pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> UpdateResult<U> {
		match self {
			UpdateResult::Unchanged => UpdateResult::Unchanged,
			UpdateResult::Changed(v) => UpdateResult::Changed(f(v)),
			UpdateResult::Cleared(v) => UpdateResult::Cleared(f(v)),
		}
	}
}

/// Trait for immutable reference of a plain key value db.
pub trait StateDBRef<K, V> {
	/// State for this db.
	type S;

	/// Look up a given hash into the bytes that hash to it, returning None if the
	/// hash is not known.
	fn get(&self, key: &K, at: &Self::S) -> Option<V>;

	/// Check for the existance of a hash-key.
	fn contains(&self, key: &K, at: &Self::S) -> bool;
}

/// Variant of `StateDBRef` to return value without copy.
pub trait InMemoryStateDBRef<K, V> {
	/// State for this db.
	type S;

	/// Look up a given hash into the bytes that hash to it, returning None if the
	/// hash is not known.
	fn get_ref(&self, key: &K, at: &Self::S) -> Option<&V>;
}

pub trait StateDB<K, V>: StateDBRef<K, V> {
		// TODO associated type from Value??
	/// State to use here.
	/// We use a different state than
	/// for the ref as it can use different
	/// constraints.
	type SE;
	/// GC strategy that can be applied.
	/// GC can be run in parallel, it does not
	/// make query incompatible.
	type GC;
	/// Like gc but operation require a lock on the db
	/// and all pending state are invalidated.
	type Migrate;
	/// Insert a datum item into the DB. Insertions are counted and the equivalent
	/// number of `remove()`s must be performed before the data is considered dead.
	/// The caller should ensure that a key only corresponds to one value.
	fn emplace(&mut self, key: K, value: V, at: &Self::SE);

	/// Remove a datum previously inserted. Insertions can be "owed" such that the
	/// same number of `insert()`s may happen without the data being eventually
	/// being inserted into the DB. It can be "owed" more than once.
	/// The caller should ensure that a key only corresponds to one value.
	fn remove(&mut self, key: &K, at: &Self::SE);
	// TODO see issue on value for mut on gc
	fn gc(&mut self, gc: &Self::GC);
	// TODO see issue on value for mut on gc
	fn migrate(&mut self, mig: &mut Self::Migrate);
}

/// Type holding a state db to lock the management.
pub struct Migrate<H, M>(M, PhantomData<H>);

impl<H, M: Management<H>> Migrate<H, M> {
	pub fn capture(m: M) -> Self {
		Migrate(m, PhantomData)
	}
	pub fn applied_migrate(mut self) -> M {
		self.0.applied_migrate();
		self.0
	}
}

pub enum Ref<'a, V> {
	Borrowed(&'a V),
	Owned(V),
}

impl<'a, V> AsRef<V> for Ref<'a, V> {
	fn as_ref(&self) -> &V {
		match self {
			Ref::Borrowed(v) => v,
			Ref::Owned(v) => &v,
		}
	}
}

impl<'a, V: Clone> Ref<'a, V> {
	pub fn into_owned(self) -> V {
		match self {
			Ref::Borrowed(v) => v.clone(),
			Ref::Owned(v) => v,
		}
	}
}

/// Management maps a historical tag of type `H` with its different db states representation.
pub trait ManagementRef<H> {
	/// attached db state needed for query.
	type S;
	/// attached db gc strategy.
	type GC;
	type Migrate;
	/// Returns the historical state representation for a given historical tag.
	fn get_db_state(&mut self, tag: &H) -> Option<Self::S>;
	/// returns optional to avoid holding lock of do nothing GC.
	/// TODO this would need RefMut or make the serialize cache layer inner mutable.
	fn get_gc(&self) -> Option<Ref<Self::GC>>;
}

pub trait Management<H>: ManagementRef<H> + Sized {
	/// attached db state needed for update.
	type SE; // TODO rename to latest or pending???
	fn init() -> (Self, Self::S);

	/// Return state mut for state but only if state exists and is
	/// a terminal writeable leaf (if not you need to create new branch 
	/// from previous state to write).
	fn get_db_state_mut(&mut self, tag: &H) -> Option<Self::SE>;

	/// Get a cursor over the initial state, can be use in some specific
	/// case (replace `default` for SE).
	fn init_state(&mut self) -> Self::SE;

	/// Get a cursor over the last change of ref (when adding or removing).
	fn latest_state(&mut self) -> Self::SE;

	/// Return latest added external index, can return None
	/// if reverted.
	fn latest_external_state(&mut self) -> Option<H>;

	/// Force change value of latest external state.
	fn force_latest_external_state(&mut self, index: H);

	fn reverse_lookup(&mut self, state: &Self::S) -> Option<H>;

	/// see migrate. When running thes making a backup of this management
	/// state is usually a good idea (this method does not manage
	/// backup or rollback).
	fn get_migrate(self) -> (Migrate<H, Self>, Self::Migrate);

	/// report a migration did run successfully, will update management state
	/// accordingly.
	/// All previously fetch states are unvalid.
	/// There is no type constraint of this, because migration is a specific
	/// case the general type should not be complexified.
	fn applied_migrate(&mut self);
}

/// This trait is for mapping a given state to the DB opaque inner state.
// TODO is only ManagementRef
pub trait ForkableManagement<H>: Management<H> {
	/// Do we keep trace of changes.
	const JOURNAL_DELETE: bool;
	/// Fork at any given internal state.
	type SF;

	/// SF is a state with 
	fn inner_fork_state(&self, s: Self::SE) -> Self::SF;

	/// SF from a S (usually the head of S)
	fn ref_state_fork(&self, s: &Self::S) -> Self::SF;

	fn get_db_state_for_fork(&mut self, tag: &H) -> Option<Self::SF>;

	/// Useful to fork in a independant branch (eg no parent reference found).
	fn init_state_fork(&mut self) -> Self::SF {
		let se = self.init_state();
		self.inner_fork_state(se)
	}

	fn latest_state_fork(&mut self) -> Self::SF {
		let se = self.latest_state();
		self.inner_fork_state(se)
	}

	/// This only succeed valid `at`.
	fn append_external_state(&mut self, state: H, at: &Self::SF) -> Option<Self::SE>;

	/// Note that this trait could be simplified to this function only.
	/// But SF can generally be extracted from an SE or an S so it is one less query.
	fn try_append_external_state(&mut self, state: H, at: &H) -> Option<Self::SE> {
		self.get_db_state_for_fork(&at)
			.and_then(|at| self.append_external_state(state, &at))
	}

	/// Warning this should cover all children recursively and can be slow for some
	/// implementations.
	/// Return all dropped tag.
	fn drop_state(&mut self, state: &Self::SF, return_dropped: bool) -> Option<Vec<H>>;

	fn try_drop_state(&mut self, tag: &H, return_dropped: bool) -> Option<Vec<H>> {
		self.get_db_state_for_fork(tag)
			.and_then(|at| self.drop_state(&at, return_dropped))
	}
}

pub trait LinearManagement<H>: ManagementRef<H> {
	fn append_external_state(&mut self, state: H) -> Option<Self::S>;

	// cannot be empty: if at initial state we return initial
	// state and initialise with a new initial state.
	fn drop_last_state(&mut self) -> Self::S;
}

/// Latest from fork only, this is for use case of aggregable
/// data cache: to store the aggregate cache.
/// (it only record a single state per fork!! but still need to resolve
/// if new fork is needed so hold almost as much info as a forkable management).
/// NOTE aggregable data cache is a cache that reply to locality
/// (a byte trie with locks that invalidate cache when set storage is call).
/// get_aggregate(aggregate_key)-> option<StructAggregate>
/// set_aggregate(aggregate_key, struct aggregate, [(child_info, lockprefixes)]).
pub trait ForkableHeadManagement<H>: ManagementRef<H> {
	fn register_external_state_head(&mut self, state: H, at: &Self::S) -> Self::S;
	fn try_register_external_state_head(&mut self, state: H, at: &H) -> Option<Self::S> {
		self.get_db_state(at).map(|at| self.register_external_state_head(state, &at))
	}
}

pub trait CompositeManagement<H>: ForkableManagement<H> {
	// join existing linear fork with this state
	// for a canonicalisation it therefore apply before
	// this state
	fn apply_linear(&mut self, at: &Self::S);
	fn try_apply_linear(&mut self, at: &H) {
		self.get_db_state(at).map(|at| self.apply_linear(&at));
	}
}


/*
enum DualState<S1, S2> {
	State1(S1),
	State2(S2),
}

enum DualManagement<'a, M1, M2> {
	Management1(&M1),
	Management2(&M2),
}


/// composite repsesentation, implements a switch between two
/// representation.
pub trait CompositeManagement<H> {
	/// State representation corresponding to external state H.
	type S1;
	type S2;
	type Management1<H>;
	type Management2<H>;

	fn get_db_state(&self, H) -> DualState<Self::S1, Self::S2>;
	fn get_management(&mut self, DualState) -> DualManagement<Self::M1, Self::M2>;
}
*/


// Additional trait that should not be in this crate (deals with collections).

pub trait MultipleDB {
	type Handle;
	fn set_collection(&mut self, h: Self::Handle);
	fn current_collection(&self) -> Self::Handle;
}

pub struct Collection {
	// static handle
	pub top: &'static [u8],
	// dynamic handle
	pub child: Vec<u8>,
}

pub trait ManagedDB {
	type Collection;
	type Handle;
	fn get_collection(&self, collection: &Self::Collection) -> Option<Self::Handle>;
	fn new_collection(&mut self, collection: &Self::Collection) -> Self::Handle;
	fn delete_collection(&mut self, collection: &Self::Collection);
}


/// This is a rather simple way of managing state, as state should not be
/// invalidated at all (can be change at latest state, also drop but not at 
/// random state).
///
/// Note that it is only informational and does not guaranty the state
/// is the latest.
/// TODO repr Transparent and cast ptr for tree?
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Latest<S>(S);

impl<S> Latest<S> {
	/// This is only to be use by a `Management` or
	/// a context where the state can be proven as
	/// being the latest.
	pub(crate) fn unchecked_latest(s: S) -> Self {
		Latest(s)
	}
	/// Reference to inner state.
	pub fn latest(&self) -> &S {
		&self.0
	}
}
