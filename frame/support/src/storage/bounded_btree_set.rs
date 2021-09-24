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

//! Traits, types and structs to support a bounded `BTreeSet`.

use crate::{storage::StorageDecodeLength, traits::Get};
use codec::{Decode, Encode, MaxEncodedLen};
use sp_std::{
	borrow::Borrow, collections::btree_set::BTreeSet, convert::TryFrom, marker::PhantomData,
	ops::Deref,
};

/// A bounded set based on a B-Tree.
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. See [`BTreeSet`] for more details.
///
/// Unlike a standard `BTreeSet`, there is an enforced upper limit to the number of items in the
/// set. All internal operations ensure this bound is respected.
#[derive(Encode)]
pub struct BoundedBTreeSet<T, S>(BTreeSet<T>, PhantomData<S>);

impl<T, S> Decode for BoundedBTreeSet<T, S>
where
	T: Decode + Ord,
	S: Get<u32>,
{
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let inner = BTreeSet::<T>::decode(input)?;
		if inner.len() > S::get() as usize {
			return Err("BoundedBTreeSet exceeds its limit".into())
		}
		Ok(Self(inner, PhantomData))
	}

	fn skip<I: codec::Input>(input: &mut I) -> Result<(), codec::Error> {
		BTreeSet::<T>::skip(input)
	}
}

impl<T, S> BoundedBTreeSet<T, S>
where
	S: Get<u32>,
{
	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		S::get() as usize
	}
}

impl<T, S> BoundedBTreeSet<T, S>
where
	T: Ord,
	S: Get<u32>,
{
	/// Create a new `BoundedBTreeSet`.
	///
	/// Does not allocate.
	pub fn new() -> Self {
		BoundedBTreeSet(BTreeSet::new(), PhantomData)
	}

	/// Consume self, and return the inner `BTreeSet`.
	///
	/// This is useful when a mutating API of the inner type is desired, and closure-based mutation
	/// such as provided by [`try_mutate`][Self::try_mutate] is inconvenient.
	pub fn into_inner(self) -> BTreeSet<T> {
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
	pub fn try_mutate(mut self, mut mutate: impl FnMut(&mut BTreeSet<T>)) -> Option<Self> {
		mutate(&mut self.0);
		(self.0.len() <= Self::bound()).then(move || self)
	}

	// Clears the set, removing all elements.
	pub fn clear(&mut self) {
		self.0.clear()
	}

	/// Exactly the same semantics as [`BTreeSet::insert`], but returns an `Err` (and is a noop) if
	/// the new length of the set exceeds `S`.
	///
	/// In the `Err` case, returns the inserted item so it can be further used without cloning.
	pub fn try_insert(&mut self, item: T) -> Result<bool, T> {
		if self.len() < Self::bound() || self.0.contains(&item) {
			Ok(self.0.insert(item))
		} else {
			Err(item)
		}
	}

	/// Remove an item from the set, returning whether it was previously in the set.
	///
	/// The item may be any borrowed form of the set's item type, but the ordering on the borrowed
	/// form _must_ match the ordering on the item type.
	pub fn remove<Q>(&mut self, item: &Q) -> bool
	where
		T: Borrow<Q>,
		Q: Ord + ?Sized,
	{
		self.0.remove(item)
	}

	/// Removes and returns the value in the set, if any, that is equal to the given one.
	///
	/// The value may be any borrowed form of the set's value type, but the ordering on the borrowed
	/// form _must_ match the ordering on the value type.
	pub fn take<Q>(&mut self, value: &Q) -> Option<T>
	where
		T: Borrow<Q> + Ord,
		Q: Ord + ?Sized,
	{
		self.0.take(value)
	}
}

impl<T, S> Default for BoundedBTreeSet<T, S>
where
	T: Ord,
	S: Get<u32>,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<T, S> Clone for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: Clone,
{
	fn clone(&self) -> Self {
		BoundedBTreeSet(self.0.clone(), PhantomData)
	}
}

#[cfg(feature = "std")]
impl<T, S> std::fmt::Debug for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: std::fmt::Debug,
	S: Get<u32>,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_tuple("BoundedBTreeSet").field(&self.0).field(&Self::bound()).finish()
	}
}

impl<T, S> PartialEq for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}

impl<T, S> Eq for BoundedBTreeSet<T, S> where BTreeSet<T>: Eq {}

impl<T, S> PartialEq<BTreeSet<T>> for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: PartialEq,
{
	fn eq(&self, other: &BTreeSet<T>) -> bool {
		self.0 == *other
	}
}

impl<T, S> PartialOrd for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: PartialOrd,
{
	fn partial_cmp(&self, other: &Self) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<T, S> Ord for BoundedBTreeSet<T, S>
where
	BTreeSet<T>: Ord,
{
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.0.cmp(&other.0)
	}
}

impl<T, S> IntoIterator for BoundedBTreeSet<T, S> {
	type Item = T;
	type IntoIter = sp_std::collections::btree_set::IntoIter<T>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<T, S> MaxEncodedLen for BoundedBTreeSet<T, S>
where
	T: MaxEncodedLen,
	S: Get<u32>,
{
	fn max_encoded_len() -> usize {
		Self::bound()
			.saturating_mul(T::max_encoded_len())
			.saturating_add(codec::Compact(S::get()).encoded_size())
	}
}

impl<T, S> Deref for BoundedBTreeSet<T, S>
where
	T: Ord,
{
	type Target = BTreeSet<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T, S> AsRef<BTreeSet<T>> for BoundedBTreeSet<T, S>
where
	T: Ord,
{
	fn as_ref(&self) -> &BTreeSet<T> {
		&self.0
	}
}

impl<T, S> From<BoundedBTreeSet<T, S>> for BTreeSet<T>
where
	T: Ord,
{
	fn from(set: BoundedBTreeSet<T, S>) -> Self {
		set.0
	}
}

impl<T, S> TryFrom<BTreeSet<T>> for BoundedBTreeSet<T, S>
where
	T: Ord,
	S: Get<u32>,
{
	type Error = ();

	fn try_from(value: BTreeSet<T>) -> Result<Self, Self::Error> {
		(value.len() <= Self::bound())
			.then(move || BoundedBTreeSet(value, PhantomData))
			.ok_or(())
	}
}

impl<T, S> codec::DecodeLength for BoundedBTreeSet<T, S> {
	fn len(self_encoded: &[u8]) -> Result<usize, codec::Error> {
		// `BoundedBTreeSet<T, S>` is stored just a `BTreeSet<T>`, which is stored as a
		// `Compact<u32>` with its length followed by an iteration of its items. We can just use
		// the underlying implementation.
		<BTreeSet<T> as codec::DecodeLength>::len(self_encoded)
	}
}

impl<T, S> StorageDecodeLength for BoundedBTreeSet<T, S> {}

impl<T, S> codec::EncodeLike<BTreeSet<T>> for BoundedBTreeSet<T, S> where BTreeSet<T>: Encode {}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::Twox128;
	use sp_io::TestExternalities;
	use sp_std::convert::TryInto;

	crate::parameter_types! {
		pub const Seven: u32 = 7;
		pub const Four: u32 = 4;
	}

	crate::generate_storage_alias! { Prefix, Foo => Value<BoundedBTreeSet<u32, Seven>> }
	crate::generate_storage_alias! { Prefix, FooMap => Map<(u32, Twox128), BoundedBTreeSet<u32, Seven>> }
	crate::generate_storage_alias! {
		Prefix,
		FooDoubleMap => DoubleMap<(u32, Twox128), (u32, Twox128), BoundedBTreeSet<u32, Seven>>
	}

	fn map_from_keys<T>(keys: &[T]) -> BTreeSet<T>
	where
		T: Ord + Copy,
	{
		keys.iter().copied().collect()
	}

	fn boundedmap_from_keys<T, S>(keys: &[T]) -> BoundedBTreeSet<T, S>
	where
		T: Ord + Copy,
		S: Get<u32>,
	{
		map_from_keys(keys).try_into().unwrap()
	}

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3]);
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3]);
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3]);
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}

	#[test]
	fn try_insert_works() {
		let mut bounded = boundedmap_from_keys::<u32, Four>(&[1, 2, 3]);
		bounded.try_insert(0).unwrap();
		assert_eq!(*bounded, map_from_keys(&[1, 0, 2, 3]));

		assert!(bounded.try_insert(9).is_err());
		assert_eq!(*bounded, map_from_keys(&[1, 0, 2, 3]));
	}

	#[test]
	fn deref_coercion_works() {
		let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3]);
		// these methods come from deref-ed vec.
		assert_eq!(bounded.len(), 3);
		assert!(bounded.iter().next().is_some());
		assert!(!bounded.is_empty());
	}

	#[test]
	fn try_mutate_works() {
		let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3, 4, 5, 6]);
		let bounded = bounded
			.try_mutate(|v| {
				v.insert(7);
			})
			.unwrap();
		assert_eq!(bounded.len(), 7);
		assert!(bounded
			.try_mutate(|v| {
				v.insert(8);
			})
			.is_none());
	}

	#[test]
	fn btree_map_eq_works() {
		let bounded = boundedmap_from_keys::<u32, Seven>(&[1, 2, 3, 4, 5, 6]);
		assert_eq!(bounded, map_from_keys(&[1, 2, 3, 4, 5, 6]));
	}

	#[test]
	fn too_big_fail_to_decode() {
		let v: Vec<u32> = vec![1, 2, 3, 4, 5];
		assert_eq!(
			BoundedBTreeSet::<u32, Four>::decode(&mut &v.encode()[..]),
			Err("BoundedBTreeSet exceeds its limit".into()),
		);
	}

	#[test]
	fn unequal_eq_impl_insert_works() {
		// given a struct with a strange notion of equality
		#[derive(Debug)]
		struct Unequal(u32, bool);

		impl PartialEq for Unequal {
			fn eq(&self, other: &Self) -> bool {
				self.0 == other.0
			}
		}
		impl Eq for Unequal {}

		impl Ord for Unequal {
			fn cmp(&self, other: &Self) -> std::cmp::Ordering {
				self.0.cmp(&other.0)
			}
		}

		impl PartialOrd for Unequal {
			fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
				Some(self.cmp(other))
			}
		}

		let mut set = BoundedBTreeSet::<Unequal, Four>::new();

		// when the set is full

		for i in 0..4 {
			set.try_insert(Unequal(i, false)).unwrap();
		}

		// can't insert a new distinct member
		set.try_insert(Unequal(5, false)).unwrap_err();

		// but _can_ insert a distinct member which compares equal, though per the documentation,
		// neither the set length nor the actual member are changed
		set.try_insert(Unequal(0, true)).unwrap();
		assert_eq!(set.len(), 4);
		let zero_item = set.get(&Unequal(0, true)).unwrap();
		assert_eq!(zero_item.0, 0);
		assert_eq!(zero_item.1, false);
	}
}
