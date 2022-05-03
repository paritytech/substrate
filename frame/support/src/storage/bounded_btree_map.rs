// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	storage::StorageDecodeLength,
	traits::{Get, TryCollect},
};
use codec::{Decode, Encode, MaxEncodedLen};
use sp_std::{borrow::Borrow, collections::btree_map::BTreeMap, marker::PhantomData, ops::Deref};

use sp_arithmetic::traits::AtMost32BitUnsigned;

/// A bounded map based on a B-Tree.
///
/// B-Trees represent a fundamental compromise between cache-efficiency and actually minimizing
/// the amount of work performed in a search. See [`BTreeMap`] for more details.
///
/// Unlike a standard `BTreeMap`, there is an enforced upper limit to the number of items in the
/// map. All internal operations ensure this bound is respected.
#[derive(Encode, scale_info::TypeInfo)]
#[scale_info(skip_type_params(S))]
pub struct BoundedBTreeMap<K, V, B, S: Get<B>>(BTreeMap<K, V>, PhantomData<(B, S)>);

impl<K, V, B, S> Decode for BoundedBTreeMap<K, V, B, S>
where
	K: Decode + Ord,
	V: Decode,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let inner = BTreeMap::<K, V>::decode(input)?;
		if S::get().into().try_into().map_or(false, |v: usize| inner.len() > v) {
			return Err("BoundedBTreeMap exceeds its limit".into())
		}
		Ok(Self(inner, PhantomData))
	}

	fn skip<I: codec::Input>(input: &mut I) -> Result<(), codec::Error> {
		BTreeMap::<K, V>::skip(input)
	}
}

impl<K, V, B, S> BoundedBTreeMap<K, V, B, S>
where
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		let bound: usize = S::get().into() as usize;
		bound
	}
}

impl<K, V, B, S> BoundedBTreeMap<K, V, B, S>
where
	K: Ord,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	/// Create `Self` from `t` without any checks.
	fn unchecked_from(t: BTreeMap<K, V>) -> Self {
		Self(t, Default::default()) 
	}

	/// Create a new `BoundedBTreeMap`.
	///
	/// Does not allocate.
	pub fn new() -> Self {
		BoundedBTreeMap(BTreeMap::new(), PhantomData)
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

	/// Exactly the same semantics as [`BTreeMap::insert`], but returns an `Err` (and is a noop) if
	/// the new length of the map exceeds `S`.
	///
	/// In the `Err` case, returns the inserted pair so it can be further used without cloning.
	pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> {
		if self.len() < Self::bound() || self.0.contains_key(&key) {
			Ok(self.0.insert(key, value))
		} else {
			Err((key, value))
		}
	}

	/// Remove a key from the map, returning the value at the key if the key was previously in the
	/// map.
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

	/// Remove a key from the map, returning the value at the key if the key was previously in the
	/// map.
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

impl<K, V, B, S> Default for BoundedBTreeMap<K, V, B, S>
where
	K: Ord,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn default() -> Self {
		Self::new()
	}
}

impl<K, V, B, S> Clone for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: Clone,
	B: AtMost32BitUnsigned,
	S: Get<B>
{
	fn clone(&self) -> Self {
		BoundedBTreeMap(self.0.clone(), PhantomData)
	}
}

#[cfg(feature = "std")]
impl<K, V, B, S> std::fmt::Debug for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: std::fmt::Debug,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.debug_tuple("BoundedBTreeMap").field(&self.0).field(&Self::bound()).finish()
	}
}

impl<K, V, B, S1, S2> PartialEq<BoundedBTreeMap<K, V, B, S1>> for BoundedBTreeMap<K, V, B, S2>
where
	BTreeMap<K, V>: PartialEq,
	B: AtMost32BitUnsigned,
	S1: Get<B>,
	S2: Get<B>,
{
	fn eq(&self, other: &BoundedBTreeMap<K, V, B, S1>) -> bool {
		S1::get() == S2::get() && self.0 == other.0
	}
}

impl<K, V, B, S> Eq for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: Eq,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
}

impl<K, V, B, S> PartialEq<BTreeMap<K, V>> for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: PartialEq,
	S: Get<B>
{
	fn eq(&self, other: &BTreeMap<K, V>) -> bool {
		self.0 == *other
	}
}

impl<K, V, B, S> PartialOrd for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: PartialOrd,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn partial_cmp(&self, other: &Self) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<K, V, B, S> Ord for BoundedBTreeMap<K, V, B, S>
where
	BTreeMap<K, V>: Ord,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.0.cmp(&other.0)
	}
}

impl<K, V, B, S: Get<B>> IntoIterator for BoundedBTreeMap<K, V, B, S> {
	type Item = (K, V);
	type IntoIter = sp_std::collections::btree_map::IntoIter<K, V>;

	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<K, V, B, S> MaxEncodedLen for BoundedBTreeMap<K, V, B, S>
where
	K: MaxEncodedLen,
	V: MaxEncodedLen,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	fn max_encoded_len() -> usize {
		Self::bound()
			.saturating_mul(K::max_encoded_len().saturating_add(V::max_encoded_len()))
			.saturating_add(codec::Compact(S::get().into()).encoded_size())
	}
}

impl<K, V, B, S> Deref for BoundedBTreeMap<K, V, B, S>
where
	K: Ord,
	S: Get<B>,
{
	type Target = BTreeMap<K, V>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<K, V, B, S> AsRef<BTreeMap<K, V>> for BoundedBTreeMap<K, V, B, S>
where
	K: Ord,
	S: Get<B>,
{
	fn as_ref(&self) -> &BTreeMap<K, V> {
		&self.0
	}
}

impl<K, V, B, S> From<BoundedBTreeMap<K, V, B, S>> for BTreeMap<K, V>
where
	K: Ord,
	S: Get<B>
{
	fn from(map: BoundedBTreeMap<K, V, B, S>) -> Self {
		map.0
	}
}

impl<K, V, B, S> TryFrom<BTreeMap<K, V>> for BoundedBTreeMap<K, V, B, S>
where
	K: Ord,
	B: AtMost32BitUnsigned,
	S: Get<B>,
{
	type Error = ();

	fn try_from(value: BTreeMap<K, V>) -> Result<Self, Self::Error> {
		(value.len() <= Self::bound())
			.then(move || BoundedBTreeMap(value, PhantomData))
			.ok_or(())
	}
}

impl<K, V, B, S: Get<B>> codec::DecodeLength for BoundedBTreeMap<K, V, B, S> {
	fn len(self_encoded: &[u8]) -> Result<usize, codec::Error> {
		// `BoundedBTreeMap<K, V, S>` is stored just a `BTreeMap<K, V>`, which is stored as a
		// `Compact<u32>` with its length followed by an iteration of its items. We can just use
		// the underlying implementation.
		<BTreeMap<K, V> as codec::DecodeLength>::len(self_encoded)
	}
}

impl<K, V, B, S: Get<B>> StorageDecodeLength for BoundedBTreeMap<K, V, B, S> {}

impl<K, V, B, S: Get<B>> codec::EncodeLike<BTreeMap<K, V>> for BoundedBTreeMap<K, V, B, S> where
	BTreeMap<K, V>: Encode
{
}

impl<I, K, V, B, Bound> TryCollect<BoundedBTreeMap<K, V, B, Bound>> for I
where
	K: Ord,
	I: ExactSizeIterator + Iterator<Item = (K, V)>,
	B: AtMost32BitUnsigned,
	Bound: Get<B>,
{
	type Error = &'static str;

	fn try_collect(self) -> Result<BoundedBTreeMap<K, V, B, Bound>, Self::Error> {
		if Bound::get().into().try_into().map_or(false, |v: usize| self.len() > v) {
			Err("iterator length too big")
		} else {
			Ok(BoundedBTreeMap::<K, V, B, Bound>::unchecked_from(self.collect::<BTreeMap<K, V>>()))
		}
	}
}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::Twox128;
	use frame_support::traits::{ ConstU8, ConstU16, ConstU32 };
	use sp_io::TestExternalities;

	crate::generate_storage_alias! { Prefix, Foo => Value<BoundedBTreeMap<u32, (), u32, ConstU32<7>>> }
	crate::generate_storage_alias! { Prefix, FooMap => Map<(Twox128, u32), BoundedBTreeMap<u32, (), u32, ConstU32<7>>> }
	crate::generate_storage_alias! {
		Prefix,
		FooDoubleMap => DoubleMap<(Twox128, u32), (Twox128, u32), BoundedBTreeMap<u32, (), u32, ConstU32<7>>>
	}

	fn map_from_keys<K>(keys: &[K]) -> BTreeMap<K, ()>
	where
		K: Ord + Copy,
	{
		keys.iter().copied().zip(std::iter::repeat(())).collect()
	}

	fn boundedmap_from_keys<K, B, S>(keys: &[K]) -> BoundedBTreeMap<K, (), B, S>
	where
		K: Ord + Copy,
		B: AtMost32BitUnsigned,
		S: Get<B>,
	{
		map_from_keys(keys).try_into().unwrap()
	}

	#[test]
	fn type_bounds_work() {
		let bt1 = boundedmap_from_keys::<u32, u8, ConstU8<6>>(&[0, 1, 2, 3, 4, 5]);
		let bt2 = boundedmap_from_keys::<u32, u16, ConstU16<6>>(&[0, 1, 2, 3, 4, 5]);
		let bt3 = boundedmap_from_keys::<u32, u32, ConstU32<6>>(&[0, 1, 2, 3, 4, 5]);

		assert_eq!(bt1.len(), 6);
		assert_eq!(bt2.len(), 6);
		assert_eq!(bt3.len(), 6);

		assert_eq!(*bt1, map_from_keys(&[0, 1, 2, 3, 4, 5]));
		assert_eq!(*bt2, map_from_keys(&[0, 1, 2, 3, 4, 5]));
		assert_eq!(*bt3, map_from_keys(&[0, 1, 2, 3, 4, 5]));
	}

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3]);
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3]);
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3]);
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}

	#[test]
	fn try_insert_works() {
		let mut bounded = boundedmap_from_keys::<u32, u32, ConstU32<4>>(&[1, 2, 3]);
		bounded.try_insert(0, ()).unwrap();
		assert_eq!(*bounded, map_from_keys(&[1, 0, 2, 3]));

		assert!(bounded.try_insert(9, ()).is_err());
		assert_eq!(*bounded, map_from_keys(&[1, 0, 2, 3]));
	}

	#[test]
	fn deref_coercion_works() {
		let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3]);
		// these methods come from deref-ed vec.
		assert_eq!(bounded.len(), 3);
		assert!(bounded.iter().next().is_some());
		assert!(!bounded.is_empty());
	}

	#[test]
	fn try_mutate_works() {
		let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3, 4, 5, 6]);
		let bounded = bounded
			.try_mutate(|v| {
				v.insert(7, ());
			})
			.unwrap();
		assert_eq!(bounded.len(), 7);
		assert!(bounded
			.try_mutate(|v| {
				v.insert(8, ());
			})
			.is_none());
	}

	#[test]
	fn btree_map_eq_works() {
		let bounded = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2, 3, 4, 5, 6]);
		assert_eq!(bounded, map_from_keys(&[1, 2, 3, 4, 5, 6]));
	}

	#[test]
	fn too_big_fail_to_decode() {
		let v: Vec<(u32, u32)> = vec![(1, 1), (2, 2), (3, 3), (4, 4), (5, 5)];
		assert_eq!(
			BoundedBTreeMap::<u32, u32, u32, ConstU32<4>>::decode(&mut &v.encode()[..]),
			Err("BoundedBTreeMap exceeds its limit".into()),
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

		let mut map = BoundedBTreeMap::<Unequal, u32, u32, ConstU32<4>>::new();

		// when the set is full

		for i in 0..4 {
			map.try_insert(Unequal(i, false), i).unwrap();
		}

		// can't insert a new distinct member
		map.try_insert(Unequal(5, false), 5).unwrap_err();

		// but _can_ insert a distinct member which compares equal, though per the documentation,
		// neither the set length nor the actual member are changed, but the value is
		map.try_insert(Unequal(0, true), 6).unwrap();
		assert_eq!(map.len(), 4);
		let (zero_key, zero_value) = map.get_key_value(&Unequal(0, true)).unwrap();
		assert_eq!(zero_key.0, 0);
		assert_eq!(zero_key.1, false);
		assert_eq!(*zero_value, 6);
	}

	#[test]
	fn can_be_collected() {
		let b1 = boundedmap_from_keys::<u32, u32, ConstU32<5>>(&[1, 2, 3, 4]);
		let b2: BoundedBTreeMap<u32, (), u32, ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can also be collected into a collection of length 4.
		let b2: BoundedBTreeMap<u32, (), u32, ConstU32<4>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can be mutated further into iterators that are `ExactSizedIterator`.
		let b2: BoundedBTreeMap<u32, (), u32, ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).rev().skip(2).try_collect().unwrap();
		// note that the binary tree will re-sort this, so rev() is not really seen
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3]);

		let b2: BoundedBTreeMap<u32, (), u32, ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).take(2).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3]);

		// but these worn't work
		let b2: Result<BoundedBTreeMap<u32, (), u32, ConstU32<3>>, _> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect();
		assert!(b2.is_err());

		let b2: Result<BoundedBTreeMap<u32, (), u32, ConstU32<1>>, _> =
			b1.iter().map(|(k, v)| (k + 1, *v)).skip(2).try_collect();
		assert!(b2.is_err());
	}

	#[test]
	fn eq_works() {
		// of same type
		let b1 = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2]);
		let b2 = boundedmap_from_keys::<u32, u32, ConstU32<7>>(&[1, 2]);
		assert_eq!(b1, b2);

		// of different type, but same value and bound.
		crate::parameter_types! {
			B1: u32 = 7;
			B2: u32 = 7;
		}
		let b1 = boundedmap_from_keys::<u32, u32, B1>(&[1, 2]);
		let b2 = boundedmap_from_keys::<u32, u32, B2>(&[1, 2]);
		assert_eq!(b1, b2);
	}
}
