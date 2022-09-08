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

//! Traits, types and structs to support putting a bounded vector into storage, as a raw value, map
//! or a double map.

use super::{BoundedSlice, BoundedVec};
use crate::Get;
use codec::{Decode, Encode, MaxEncodedLen};
use core::{
	ops::{Deref, Index, IndexMut},
	slice::SliceIndex,
};
#[cfg(feature = "std")]
use serde::{
	de::{Error, SeqAccess, Visitor},
	Deserialize, Deserializer, Serialize,
};
use sp_std::{marker::PhantomData, prelude::*};

/// A weakly bounded vector.
///
/// It has implementations for efficient append and length decoding, as with a normal `Vec<_>`, once
/// put into storage as a raw value, map or double-map.
///
/// The length of the vec is not strictly bounded. Decoding a vec with more element that the bound
/// is accepted, and some method allow to bypass the restriction with warnings.
#[cfg_attr(feature = "std", derive(Serialize), serde(transparent))]
#[derive(Encode, scale_info::TypeInfo)]
#[scale_info(skip_type_params(S))]
pub struct WeakBoundedVec<T, S>(
	pub(super) Vec<T>,
	#[cfg_attr(feature = "std", serde(skip_serializing))] PhantomData<S>,
);

#[cfg(feature = "std")]
impl<'de, T, S: Get<u32>> Deserialize<'de> for WeakBoundedVec<T, S>
where
	T: Deserialize<'de>,
{
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
	where
		D: Deserializer<'de>,
	{
		struct VecVisitor<T, S: Get<u32>>(PhantomData<(T, S)>);

		impl<'de, T, S: Get<u32>> Visitor<'de> for VecVisitor<T, S>
		where
			T: Deserialize<'de>,
		{
			type Value = Vec<T>;

			fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
				formatter.write_str("a sequence")
			}

			fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
			where
				A: SeqAccess<'de>,
			{
				let size = seq.size_hint().unwrap_or(0);
				let max = match usize::try_from(S::get()) {
					Ok(n) => n,
					Err(_) => return Err(A::Error::custom("can't convert to usize")),
				};
				if size > max {
					log::warn!(
						target: "runtime",
						"length of a bounded vector while deserializing is not respected.",
					);
				}
				let mut values = Vec::with_capacity(size);

				while let Some(value) = seq.next_element()? {
					values.push(value);
					if values.len() > max {
						log::warn!(
							target: "runtime",
							"length of a bounded vector while deserializing is not respected.",
						);
					}
				}

				Ok(values)
			}
		}

		let visitor: VecVisitor<T, S> = VecVisitor(PhantomData);
		deserializer.deserialize_seq(visitor).map(|v| {
			WeakBoundedVec::<T, S>::try_from(v).map_err(|_| Error::custom("out of bounds"))
		})?
	}
}

impl<T: Decode, S: Get<u32>> Decode for WeakBoundedVec<T, S> {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let inner = Vec::<T>::decode(input)?;
		Ok(Self::force_from(inner, Some("decode")))
	}

	fn skip<I: codec::Input>(input: &mut I) -> Result<(), codec::Error> {
		Vec::<T>::skip(input)
	}
}

impl<T, S> WeakBoundedVec<T, S> {
	/// Create `Self` from `t` without any checks.
	fn unchecked_from(t: Vec<T>) -> Self {
		Self(t, Default::default())
	}

	/// Consume self, and return the inner `Vec`. Henceforth, the `Vec<_>` can be altered in an
	/// arbitrary way. At some point, if the reverse conversion is required, `TryFrom<Vec<_>>` can
	/// be used.
	///
	/// This is useful for cases if you need access to an internal API of the inner `Vec<_>` which
	/// is not provided by the wrapper `WeakBoundedVec`.
	pub fn into_inner(self) -> Vec<T> {
		self.0
	}

	/// Exactly the same semantics as [`Vec::remove`].
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn remove(&mut self, index: usize) -> T {
		self.0.remove(index)
	}

	/// Exactly the same semantics as [`Vec::swap_remove`].
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn swap_remove(&mut self, index: usize) -> T {
		self.0.swap_remove(index)
	}

	/// Exactly the same semantics as [`Vec::retain`].
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, f: F) {
		self.0.retain(f)
	}

	/// Exactly the same semantics as [`slice::get_mut`].
	pub fn get_mut<I: SliceIndex<[T]>>(
		&mut self,
		index: I,
	) -> Option<&mut <I as SliceIndex<[T]>>::Output> {
		self.0.get_mut(index)
	}
}

impl<T, S: Get<u32>> WeakBoundedVec<T, S> {
	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		S::get() as usize
	}

	/// Create `Self` from `t` without any checks. Logs warnings if the bound is not being
	/// respected. The additional scope can be used to indicate where a potential overflow is
	/// happening.
	pub fn force_from(t: Vec<T>, scope: Option<&'static str>) -> Self {
		if t.len() > Self::bound() {
			log::warn!(
				target: "runtime",
				"length of a bounded vector in scope {} is not respected.",
				scope.unwrap_or("UNKNOWN"),
			);
		}

		Self::unchecked_from(t)
	}

	/// Consumes self and mutates self via the given `mutate` function.
	///
	/// If the outcome of mutation is within bounds, `Some(Self)` is returned. Else, `None` is
	/// returned.
	///
	/// This is essentially a *consuming* shorthand [`Self::into_inner`] -> `...` ->
	/// [`Self::try_from`].
	pub fn try_mutate(mut self, mut mutate: impl FnMut(&mut Vec<T>)) -> Option<Self> {
		mutate(&mut self.0);
		(self.0.len() <= Self::bound()).then(move || self)
	}

	/// Exactly the same semantics as [`Vec::insert`], but returns an `Err` (and is a noop) if the
	/// new length of the vector exceeds `S`.
	///
	/// # Panics
	///
	/// Panics if `index > len`.
	pub fn try_insert(&mut self, index: usize, element: T) -> Result<(), ()> {
		if self.len() < Self::bound() {
			self.0.insert(index, element);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Exactly the same semantics as [`Vec::push`], but returns an `Err` (and is a noop) if the
	/// new length of the vector exceeds `S`.
	///
	/// # Panics
	///
	/// Panics if the new capacity exceeds isize::MAX bytes.
	pub fn try_push(&mut self, element: T) -> Result<(), ()> {
		if self.len() < Self::bound() {
			self.0.push(element);
			Ok(())
		} else {
			Err(())
		}
	}
}

impl<T, S> Default for WeakBoundedVec<T, S> {
	fn default() -> Self {
		// the bound cannot be below 0, which is satisfied by an empty vector
		Self::unchecked_from(Vec::default())
	}
}

impl<T, S> sp_std::fmt::Debug for WeakBoundedVec<T, S>
where
	Vec<T>: sp_std::fmt::Debug,
	S: Get<u32>,
{
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		f.debug_tuple("WeakBoundedVec").field(&self.0).field(&Self::bound()).finish()
	}
}

impl<T, S> Clone for WeakBoundedVec<T, S>
where
	T: Clone,
{
	fn clone(&self) -> Self {
		// bound is retained
		Self::unchecked_from(self.0.clone())
	}
}

impl<T, S: Get<u32>> TryFrom<Vec<T>> for WeakBoundedVec<T, S> {
	type Error = ();
	fn try_from(t: Vec<T>) -> Result<Self, Self::Error> {
		if t.len() <= Self::bound() {
			// explicit check just above
			Ok(Self::unchecked_from(t))
		} else {
			Err(())
		}
	}
}

// It is okay to give a non-mutable reference of the inner vec to anyone.
impl<T, S> AsRef<Vec<T>> for WeakBoundedVec<T, S> {
	fn as_ref(&self) -> &Vec<T> {
		&self.0
	}
}

impl<T, S> AsRef<[T]> for WeakBoundedVec<T, S> {
	fn as_ref(&self) -> &[T] {
		&self.0
	}
}

impl<T, S> AsMut<[T]> for WeakBoundedVec<T, S> {
	fn as_mut(&mut self) -> &mut [T] {
		&mut self.0
	}
}

// will allow for immutable all operations of `Vec<T>` on `WeakBoundedVec<T>`.
impl<T, S> Deref for WeakBoundedVec<T, S> {
	type Target = Vec<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

// Allows for indexing similar to a normal `Vec`. Can panic if out of bound.
impl<T, S, I> Index<I> for WeakBoundedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	type Output = I::Output;

	#[inline]
	fn index(&self, index: I) -> &Self::Output {
		self.0.index(index)
	}
}

impl<T, S, I> IndexMut<I> for WeakBoundedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	#[inline]
	fn index_mut(&mut self, index: I) -> &mut Self::Output {
		self.0.index_mut(index)
	}
}

impl<T, S> sp_std::iter::IntoIterator for WeakBoundedVec<T, S> {
	type Item = T;
	type IntoIter = sp_std::vec::IntoIter<T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<'a, T, S> sp_std::iter::IntoIterator for &'a WeakBoundedVec<T, S> {
	type Item = &'a T;
	type IntoIter = sp_std::slice::Iter<'a, T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.iter()
	}
}

impl<'a, T, S> sp_std::iter::IntoIterator for &'a mut WeakBoundedVec<T, S> {
	type Item = &'a mut T;
	type IntoIter = sp_std::slice::IterMut<'a, T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.iter_mut()
	}
}

impl<T, S> codec::DecodeLength for WeakBoundedVec<T, S> {
	fn len(self_encoded: &[u8]) -> Result<usize, codec::Error> {
		// `WeakBoundedVec<T, _>` stored just a `Vec<T>`, thus the length is at the beginning in
		// `Compact` form, and same implementation as `Vec<T>` can be used.
		<Vec<T> as codec::DecodeLength>::len(self_encoded)
	}
}

impl<T, BoundSelf, BoundRhs> PartialEq<WeakBoundedVec<T, BoundRhs>> for WeakBoundedVec<T, BoundSelf>
where
	T: PartialEq,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn eq(&self, rhs: &WeakBoundedVec<T, BoundRhs>) -> bool {
		self.0 == rhs.0
	}
}

impl<T, BoundSelf, BoundRhs> PartialEq<BoundedVec<T, BoundRhs>> for WeakBoundedVec<T, BoundSelf>
where
	T: PartialEq,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn eq(&self, rhs: &BoundedVec<T, BoundRhs>) -> bool {
		self.0 == rhs.0
	}
}

impl<'a, T, BoundSelf, BoundRhs> PartialEq<BoundedSlice<'a, T, BoundRhs>>
	for WeakBoundedVec<T, BoundSelf>
where
	T: PartialEq,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn eq(&self, rhs: &BoundedSlice<'a, T, BoundRhs>) -> bool {
		self.0 == rhs.0
	}
}

impl<T: PartialEq, S: Get<u32>> PartialEq<Vec<T>> for WeakBoundedVec<T, S> {
	fn eq(&self, other: &Vec<T>) -> bool {
		&self.0 == other
	}
}

impl<T, S: Get<u32>> Eq for WeakBoundedVec<T, S> where T: Eq {}

impl<T, BoundSelf, BoundRhs> PartialOrd<WeakBoundedVec<T, BoundRhs>>
	for WeakBoundedVec<T, BoundSelf>
where
	T: PartialOrd,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn partial_cmp(&self, other: &WeakBoundedVec<T, BoundRhs>) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<T, BoundSelf, BoundRhs> PartialOrd<BoundedVec<T, BoundRhs>> for WeakBoundedVec<T, BoundSelf>
where
	T: PartialOrd,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn partial_cmp(&self, other: &BoundedVec<T, BoundRhs>) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<'a, T, BoundSelf, BoundRhs> PartialOrd<BoundedSlice<'a, T, BoundRhs>>
	for WeakBoundedVec<T, BoundSelf>
where
	T: PartialOrd,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn partial_cmp(&self, other: &BoundedSlice<'a, T, BoundRhs>) -> Option<sp_std::cmp::Ordering> {
		(&*self.0).partial_cmp(other.0)
	}
}

impl<T: Ord, S: Get<u32>> Ord for WeakBoundedVec<T, S> {
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.0.cmp(&other.0)
	}
}

impl<T, S> MaxEncodedLen for WeakBoundedVec<T, S>
where
	T: MaxEncodedLen,
	S: Get<u32>,
	WeakBoundedVec<T, S>: Encode,
{
	fn max_encoded_len() -> usize {
		// WeakBoundedVec<T, S> encodes like Vec<T> which encodes like [T], which is a compact u32
		// plus each item in the slice:
		// See: https://docs.substrate.io/reference/scale-codec/
		codec::Compact(S::get())
			.encoded_size()
			.saturating_add(Self::bound().saturating_mul(T::max_encoded_len()))
	}
}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::ConstU32;

	#[test]
	fn bound_returns_correct_value() {
		assert_eq!(WeakBoundedVec::<u32, ConstU32<7>>::bound(), 7);
	}

	#[test]
	fn try_insert_works() {
		let mut bounded: WeakBoundedVec<u32, ConstU32<4>> = vec![1, 2, 3].try_into().unwrap();
		bounded.try_insert(1, 0).unwrap();
		assert_eq!(*bounded, vec![1, 0, 2, 3]);

		assert!(bounded.try_insert(0, 9).is_err());
		assert_eq!(*bounded, vec![1, 0, 2, 3]);
	}

	#[test]
	#[should_panic(expected = "insertion index (is 9) should be <= len (is 3)")]
	fn try_inert_panics_if_oob() {
		let mut bounded: WeakBoundedVec<u32, ConstU32<4>> = vec![1, 2, 3].try_into().unwrap();
		bounded.try_insert(9, 0).unwrap();
	}

	#[test]
	fn try_push_works() {
		let mut bounded: WeakBoundedVec<u32, ConstU32<4>> = vec![1, 2, 3].try_into().unwrap();
		bounded.try_push(0).unwrap();
		assert_eq!(*bounded, vec![1, 2, 3, 0]);

		assert!(bounded.try_push(9).is_err());
	}

	#[test]
	fn deref_coercion_works() {
		let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3].try_into().unwrap();
		// these methods come from deref-ed vec.
		assert_eq!(bounded.len(), 3);
		assert!(bounded.iter().next().is_some());
		assert!(!bounded.is_empty());
	}

	#[test]
	fn try_mutate_works() {
		let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3, 4, 5, 6].try_into().unwrap();
		let bounded = bounded.try_mutate(|v| v.push(7)).unwrap();
		assert_eq!(bounded.len(), 7);
		assert!(bounded.try_mutate(|v| v.push(8)).is_none());
	}

	#[test]
	fn slice_indexing_works() {
		let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3, 4, 5, 6].try_into().unwrap();
		assert_eq!(&bounded[0..=2], &[1, 2, 3]);
	}

	#[test]
	fn vec_eq_works() {
		let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3, 4, 5, 6].try_into().unwrap();
		assert_eq!(bounded, vec![1, 2, 3, 4, 5, 6]);
	}

	#[test]
	fn too_big_succeed_to_decode() {
		let v: Vec<u32> = vec![1, 2, 3, 4, 5];
		let w = WeakBoundedVec::<u32, ConstU32<4>>::decode(&mut &v.encode()[..]).unwrap();
		assert_eq!(v, *w);
	}
}
