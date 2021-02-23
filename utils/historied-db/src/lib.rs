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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! println {
	() => ($crate::print!("\n"));
	($($arg:tt)*) => ({ })
}

/// Implementation of historied-db traits
/// using historied values
pub mod historied;

/// Backend structures for historied data storage.
pub mod backend;

/// Tools to work with simple key value
/// collection mapped over dbs location (non historied).
pub mod mapped_db;

/// Management for state of historied data.
pub mod management;

/// Context associated with item.
/// Main use case here is a backend to fetch
/// additional information.
pub trait Context: Sized {
	type Context: ContextBuilder;
}

/// A context can be obtain by clone or
/// from a parent index byte representation.
pub trait ContextBuilder: Clone {
	/// If set to false, some conversion of index to bytes can be skipped.
	const USE_INDEXES: bool;

	/// Here parent index is a concatenation of all parent encoded indexes.
	fn with_indexes(&self, parent_indexes: &[u8], index: &[u8]) -> Self;

	/// Access to stored parent indexes of this builder.
	fn indexes(&self) -> &[u8];
}

/// For pair implementation, first and second are hierarchically ordered.
/// This is mainly used by `Tree`.
impl<A: ContextBuilder, B: ContextBuilder> ContextBuilder for (A, B) {
	const USE_INDEXES: bool = A::USE_INDEXES;

	fn with_indexes(&self, parent_indexes: &[u8], index: &[u8]) -> Self {
		let first = self.0.with_indexes(parent_indexes, index);
		let second = self.1.with_indexes(first.indexes(), &[]);
		(first, second)
	}
	fn indexes(&self) -> &[u8] {
		self.1.indexes()
	}
}

impl ContextBuilder for () {
	const USE_INDEXES: bool = false;

	fn with_indexes(&self, _parent_indexes: &[u8], _index: &[u8]) -> Self {
		()
	}
	fn indexes(&self) -> &[u8] {
		&[]
	}
}

/// Trigger action on changed data.
///
/// This allow recursive call.
/// Currently the only example of this
/// use is the `Head` backend requires
/// to flush its changes.
/// Calling this in context of a tree
/// containing head will flush those
/// heads changes.
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

		impl DecodeWithContext for $type {
			fn decode_with_context<I: codec::Input>(input: &mut I, _init: &Self::Context) -> Option<Self> {
				use codec::Decode;
				Self::decode(input).ok()
			}
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

/// Utility that work as a `Cow`,
/// but do not allow modification.
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

/// State using this struct are seen as latest state.
///
/// A latest state is the current last state of a sequence.
///
/// Note that it is only informational and does not guaranty the state
/// is the latest.
///
/// This is a rather simple way of managing state, but relatively
/// good when working in non concurrent environment.
///
/// TODO repr Transparent and cast ptr for tree?
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Latest<S>(S);

impl<S> Latest<S> {
	/// This is only to be use by a `ManagementMut` or
	/// a context where the state can be proven as
	/// being the latest.
	pub fn unchecked_latest(s: S) -> Self {
		Latest(s)
	}
	/// Reference to inner state.
	pub fn latest(&self) -> &S {
		&self.0
	}
}

/// Associate a state index with a given state.
/// The index is the base unit for a state.
/// It is the historical position.
/// When use with a management, it is the value
/// associated with a tag.
pub trait StateIndex<I> {
	/// Get individal state index.
	fn index(&self) -> I;
	/// Get reference to individal state index.
	/// If some memory needs allocation, return `None`,
	/// and user should fallback to using `index`.
	/// TODO consider removal (index should be copy).
	fn index_ref(&self) -> Option<&I>;
}

impl<S: Clone> StateIndex<S> for Latest<S> {
	fn index(&self) -> S {
		self.latest().clone()
	}
	fn index_ref(&self) -> Option<&S> {
		Some(self.latest())
	}
}

macro_rules! primitive_state_index {
	($name: ty) => {
		impl StateIndex<$name> for $name {
			fn index(&self) -> $name {
				self.clone()
			}
			fn index_ref(&self) -> Option<&$name> {
				Some(self)
			}
		}
	}
}
	
primitive_state_index!(u8);
primitive_state_index!(u32);
primitive_state_index!(u64);
primitive_state_index!(u128);
primitive_state_index!(Vec<u8>);
