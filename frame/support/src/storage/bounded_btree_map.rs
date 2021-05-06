// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Traits, types and structs to support a bounded BTreeMap.

use sp_std::{
	borrow::Borrow, collections::btree_map::BTreeMap, convert::TryFrom, fmt, marker::PhantomData,
	ops::Deref,
};
use crate::traits::{Get, MaxEncodedLen};
use codec::{Encode, Decode};

/// A bounded map based on a B-Tree.
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. See [`BTreeMap`] for more details.
///
/// Unlike a standard `BTreeMap`, there is a static, enforced upper limit to the number of items
/// in the map. All internal operations ensure this bound is respected.
#[derive(Encode, Decode)]
pub struct BoundedBTreeMap<K, V, S>(BTreeMap<K, V>, PhantomData<S>);

impl<K, V, S> BoundedBTreeMap<K, V, S>
where
	S: Get<u32>,
{
	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		S::get() as usize
	}
}

impl<K, V, S> BoundedBTreeMap<K, V, S>
where
	K: Ord,
	S: Get<u32>,
{
	/// Create a new `BoundedBTreeMap`.
	///
	/// Does not allocate.
	pub fn new() -> Self {
		BoundedBTreeMap(BTreeMap::new(), PhantomData)
	}

	/// Create `Self` from a primitive `BTreeMap` without any checks.
	unsafe fn unchecked_from(map: BTreeMap<K, V>) -> Self {
		Self(map, Default::default())
	}

	/// Create `Self` from a primitive `BTreeMap` without any checks.
	///
	/// Logs warnings if the bound is not being respected. The scope is mentioned in the log message
	/// to indicate where overflow is happening.
	///
	/// # Example
	///
	/// ```
	/// # use sp_std::collections::btree_map::BTreeMap;
	/// # use frame_support::{parameter_types, storage::bounded_btree_map::BoundedBTreeMap};
	/// parameter_types! {
	/// 	pub const Size: u32 = 5;
	/// }
	/// let mut map = BTreeMap::new();
	/// map.insert("foo", 1);
	/// map.insert("bar", 2);
	/// let bounded_map = unsafe {BoundedBTreeMap::<_, _, Size>::force_from(map, "demo")};
	/// ```
	pub unsafe fn force_from<Scope>(map: BTreeMap<K, V>, scope: Scope) -> Self
	where
		Scope: Into<Option<&'static str>>,
	{
		if map.len() > Self::bound() {
			log::warn!(
				target: crate::LOG_TARGET,
				"length of a bounded btreemap in scope {} is not respected.",
				scope.into().unwrap_or("UNKNOWN"),
			);
		}

		Self::unchecked_from(map)
	}

	/// Consume self, and return the inner `BTreeMap`.
	///
	/// This is useful when a mutating API of the inner type is desired, and closure-based mutation
	/// such as provided by [`try_mutate`][Self::try_mutate] is inconvenient.
	pub fn into_inner(self) -> BTreeMap<K, V> {
		debug_assert!(self.0.len() <= Self::bound());
		self.0
	}

	/// Consumes self and mutates self via the given `mutate` function.
	///
	/// If the outcome of mutation is within bounds, `Some(Self)` is returned. Else, `None` is
	/// returned.
	///
	/// This is essentially a *consuming* shorthand [`Self::into_inner`] -> `...` ->
	/// [`Self::try_from`].
	pub fn try_mutate(mut self, mut mutate: impl FnMut(&mut BTreeMap<K, V>)) -> Option<Self> {
		mutate(&mut self.0);
		(self.0.len() <= Self::bound()).then(move || self)
	}

	// Clears the map, removing all elements.
	pub fn clear(&mut self) {
		self.0.clear()
	}

	/// Return a mutable reference to the value corresponding to the key.
	///
	/// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
	/// form _must_ match the ordering on the key type.
	pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
	where
		K: Borrow<Q>,
		Q: Ord + ?Sized,
	{
		self.0.get_mut(key)
	}

	/// Exactly the same semantics as [`BTreeMap::insert`], but returns an `Err` (and is a noop) if the
	/// new length of the map exceeds `S`.
	pub fn try_insert(&mut self, key: K, value: V) -> Result<(), ()> {
		if self.len() < Self::bound() {
			self.0.insert(key, value);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Remove a key from the map, returning the value at the key if the key was previously in the map.
	///
	/// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
	/// form _must_ match the ordering on the key type.
	pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
	where
		K: Borrow<Q>,
		Q: Ord + ?Sized,
	{
		self.0.remove(key)
	}

	/// Remove a key from the map, returning the value at the key if the key was previously in the map.
	///
	/// The key may be any borrowed form of the map's key type, but the ordering on the borrowed
	/// form _must_ match the ordering on the key type.
	pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
	where
		K: Borrow<Q>,
		Q: Ord + ?Sized,
	{
		self.0.remove_entry(key)
	}
}

impl<K, V, S> Default for BoundedBTreeMap<K, V, S>
where
	K: Ord,
	S: Get<u32>,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<K, V, S> Clone for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: Clone,
{
	fn clone(&self) -> Self {
		BoundedBTreeMap(self.0.clone(), PhantomData)
	}
}

impl<K, V, S> fmt::Debug for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: fmt::Debug,
	S: Get<u32>,
{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_tuple("BoundedBTreeMap").field(&self.0).field(&Self::bound()).finish()
	}
}

impl<K, V, S> PartialEq for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}

impl<K, V, S> Eq for BoundedBTreeMap<K, V, S> where BTreeMap<K, V>: Eq {}

impl<K, V, S> PartialEq<BTreeMap<K, V>> for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: PartialEq,
{
	fn eq(&self, other: &BTreeMap<K, V>) -> bool {
		self.0 == *other
	}
}

impl<K, V, S> PartialOrd for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<K, V, S> Ord for BoundedBTreeMap<K, V, S>
where
	BTreeMap<K, V>: Ord,
{
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.0.cmp(&other.0)
	}
}

impl<K, V, S> IntoIterator for BoundedBTreeMap<K, V, S> {
	type Item = (K, V);
	type IntoIter = sp_std::collections::btree_map::IntoIter<K, V>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<K, V, S> MaxEncodedLen for BoundedBTreeMap<K, V, S>
where
	K: MaxEncodedLen,
	V: MaxEncodedLen,
	S: Get<u32>,
{
	fn max_encoded_len() -> usize {
		Self::bound()
			.saturating_mul(K::max_encoded_len().saturating_add(V::max_encoded_len()))
			.saturating_add(
				// https://github.com/paritytech/parity-scale-codec/
				//   blob/f0341dabb01aa9ff0548558abb6dcc5c31c669a1/src/codec.rs#L876
				codec::Compact::<u32>::max_encoded_len(),
			)
	}
}

impl<K, V, S> Deref for BoundedBTreeMap<K, V, S>
where
	K: Ord,
{
	type Target = BTreeMap<K, V>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<K, V, S> AsRef<BTreeMap<K, V>> for BoundedBTreeMap<K, V, S>
where
	K: Ord,
{
	fn as_ref(&self) -> &BTreeMap<K, V> {
		&self.0
	}
}

impl<K, V, S> From<BoundedBTreeMap<K, V, S>> for BTreeMap<K, V>
where
	K: Ord,
{
	fn from(map: BoundedBTreeMap<K, V, S>) -> Self {
		map.0
	}
}

impl<K, V, S> TryFrom<BTreeMap<K, V>> for BoundedBTreeMap<K, V, S>
where
	K: Ord,
	S: Get<u32>,
{
	type Error = ();

	fn try_from(value: BTreeMap<K, V>) -> Result<Self, Self::Error> {
		(value.len() <= Self::bound()).then(move || BoundedBTreeMap(value, PhantomData)).ok_or(())
	}
}
