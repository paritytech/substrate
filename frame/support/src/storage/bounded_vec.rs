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

use crate::{
	storage::{StorageDecodeLength, StorageTryAppend},
	traits::{Get, TryCollect},
	WeakBoundedVec,
};
use codec::{Decode, Encode, EncodeLike, MaxEncodedLen};
use core::{
	ops::{Deref, Index, IndexMut, RangeBounds},
	slice::SliceIndex,
};
use sp_std::{marker::PhantomData, prelude::*};

/// A bounded vector.
///
/// It has implementations for efficient append and length decoding, as with a normal `Vec<_>`, once
/// put into storage as a raw value, map or double-map.
///
/// As the name suggests, the length of the queue is always bounded. All internal operations ensure
/// this bound is respected.
#[derive(Encode, scale_info::TypeInfo)]
#[scale_info(skip_type_params(S))]
pub struct BoundedVec<T, S>(Vec<T>, PhantomData<S>);

/// A bounded slice.
///
/// Similar to a `BoundedVec`, but not owned and cannot be decoded.
#[derive(Encode, scale_info::TypeInfo)]
#[scale_info(skip_type_params(S))]
pub struct BoundedSlice<'a, T, S>(&'a [T], PhantomData<S>);

// `BoundedSlice`s encode to something which will always decode into a `BoundedVec`,
// `WeakBoundedVec`, or a `Vec`.
impl<'a, T: Encode + Decode, S: Get<u32>> EncodeLike<BoundedVec<T, S>> for BoundedSlice<'a, T, S> {}
impl<'a, T: Encode + Decode, S: Get<u32>> EncodeLike<WeakBoundedVec<T, S>>
	for BoundedSlice<'a, T, S>
{
}
impl<'a, T: Encode + Decode, S: Get<u32>> EncodeLike<Vec<T>> for BoundedSlice<'a, T, S> {}

impl<T: PartialOrd, Bound: Get<u32>> PartialOrd for BoundedVec<T, Bound> {
	fn partial_cmp(&self, other: &Self) -> Option<sp_std::cmp::Ordering> {
		self.0.partial_cmp(&other.0)
	}
}

impl<T: Ord, Bound: Get<u32>> Ord for BoundedVec<T, Bound> {
	fn cmp(&self, other: &Self) -> sp_std::cmp::Ordering {
		self.0.cmp(&other.0)
	}
}

impl<'a, T, S: Get<u32>> TryFrom<&'a [T]> for BoundedSlice<'a, T, S> {
	type Error = ();
	fn try_from(t: &'a [T]) -> Result<Self, Self::Error> {
		if t.len() < S::get() as usize {
			Ok(BoundedSlice(t, PhantomData))
		} else {
			Err(())
		}
	}
}

impl<'a, T, S> From<BoundedSlice<'a, T, S>> for &'a [T] {
	fn from(t: BoundedSlice<'a, T, S>) -> Self {
		t.0
	}
}

impl<T: Decode, S: Get<u32>> Decode for BoundedVec<T, S> {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let inner = Vec::<T>::decode(input)?;
		if inner.len() > S::get() as usize {
			return Err("BoundedVec exceeds its limit".into())
		}
		Ok(Self(inner, PhantomData))
	}

	fn skip<I: codec::Input>(input: &mut I) -> Result<(), codec::Error> {
		Vec::<T>::skip(input)
	}
}

// `BoundedVec`s encode to something which will always decode as a `Vec`.
impl<T: Encode + Decode, S: Get<u32>> EncodeLike<Vec<T>> for BoundedVec<T, S> {}

impl<T, S> BoundedVec<T, S> {
	/// Create `Self` from `t` without any checks.
	fn unchecked_from(t: Vec<T>) -> Self {
		Self(t, Default::default())
	}

	/// Consume self, and return the inner `Vec`. Henceforth, the `Vec<_>` can be altered in an
	/// arbitrary way. At some point, if the reverse conversion is required, `TryFrom<Vec<_>>` can
	/// be used.
	///
	/// This is useful for cases if you need access to an internal API of the inner `Vec<_>` which
	/// is not provided by the wrapper `BoundedVec`.
	pub fn into_inner(self) -> Vec<T> {
		self.0
	}

	/// Exactly the same semantics as [`slice::sort_by`].
	///
	/// This is safe since sorting cannot change the number of elements in the vector.
	pub fn sort_by<F>(&mut self, compare: F)
	where
		F: FnMut(&T, &T) -> sp_std::cmp::Ordering,
	{
		self.0.sort_by(compare)
	}

	/// Exactly the same semantics as [`slice::sort`].
	///
	/// This is safe since sorting cannot change the number of elements in the vector.
	pub fn sort(&mut self)
	where
		T: sp_std::cmp::Ord,
	{
		self.0.sort()
	}

	/// Exactly the same semantics as `Vec::remove`.
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn remove(&mut self, index: usize) -> T {
		self.0.remove(index)
	}

	/// Exactly the same semantics as `slice::swap_remove`.
	///
	/// # Panics
	///
	/// Panics if `index` is out of bounds.
	pub fn swap_remove(&mut self, index: usize) -> T {
		self.0.swap_remove(index)
	}

	/// Exactly the same semantics as `Vec::retain`.
	pub fn retain<F: FnMut(&T) -> bool>(&mut self, f: F) {
		self.0.retain(f)
	}

	/// Exactly the same semantics as `slice::get_mut`.
	pub fn get_mut<I: SliceIndex<[T]>>(
		&mut self,
		index: I,
	) -> Option<&mut <I as SliceIndex<[T]>>::Output> {
		self.0.get_mut(index)
	}

	/// Exactly the same semantics as `Vec::truncate`.
	///
	/// This is safe because `truncate` can never increase the length of the internal vector.
	pub fn truncate(&mut self, s: usize) {
		self.0.truncate(s);
	}

	/// Exactly the same semantics as `Vec::pop`.
	///
	/// This is safe since popping can only shrink the inner vector.
	pub fn pop(&mut self) -> Option<T> {
		self.0.pop()
	}

	/// Exactly the same semantics as [`slice::iter_mut`].
	pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
		self.0.iter_mut()
	}

	/// Exactly the same semantics as [`slice::last_mut`].
	pub fn last_mut(&mut self) -> Option<&mut T> {
		self.0.last_mut()
	}

	/// Exact same semantics as [`Vec::drain`].
	pub fn drain<R>(&mut self, range: R) -> sp_std::vec::Drain<'_, T>
	where
		R: RangeBounds<usize>,
	{
		self.0.drain(range)
	}
}

impl<T, S: Get<u32>> From<BoundedVec<T, S>> for Vec<T> {
	fn from(x: BoundedVec<T, S>) -> Vec<T> {
		x.0
	}
}

impl<T, S: Get<u32>> BoundedVec<T, S> {
	/// Pre-allocate `capacity` items in self.
	///
	/// If `capacity` is greater than [`Self::bound`], then the minimum of the two is used.
	pub fn with_bounded_capacity(capacity: usize) -> Self {
		let capacity = capacity.min(Self::bound());
		Self(Vec::with_capacity(capacity), Default::default())
	}

	/// Allocate self with the maximum possible capacity.
	pub fn with_max_capacity() -> Self {
		Self::with_bounded_capacity(Self::bound())
	}

	/// Get the bound of the type in `usize`.
	pub fn bound() -> usize {
		S::get() as usize
	}

	/// Returns true of this collection is full.
	pub fn is_full(&self) -> bool {
		self.len() >= Self::bound()
	}

	/// Forces the insertion of `element` into `self` retaining all items with index at least
	/// `index`.
	///
	/// If `index == 0` and `self.len() == Self::bound()`, then this is a no-op.
	///
	/// If `Self::bound() < index` or `self.len() < index`, then this is also a no-op.
	///
	/// Returns `Ok(maybe_removed)` if the item was inserted, where `maybe_removed` is
	/// `Some(removed)` if an item was removed to make room for the new one. Returns `Err(())` if
	/// `element` cannot be inserted.
	pub fn force_insert_keep_right(
		&mut self,
		index: usize,
		mut element: T,
	) -> Result<Option<T>, ()> {
		// Check against panics.
		if Self::bound() < index || self.len() < index {
			Err(())
		} else if self.len() < Self::bound() {
			// Cannot panic since self.len() >= index;
			self.0.insert(index, element);
			Ok(None)
		} else {
			if index == 0 {
				return Err(())
			}
			sp_std::mem::swap(&mut self[0], &mut element);
			// `[0..index] cannot panic since self.len() >= index.
			// `rotate_left(1)` cannot panic because there is at least 1 element.
			self[0..index].rotate_left(1);
			Ok(Some(element))
		}
	}

	/// Forces the insertion of `element` into `self` retaining all items with index at most
	/// `index`.
	///
	/// If `index == Self::bound()` and `self.len() == Self::bound()`, then this is a no-op.
	///
	/// If `Self::bound() < index` or `self.len() < index`, then this is also a no-op.
	///
	/// Returns `Ok(maybe_removed)` if the item was inserted, where `maybe_removed` is
	/// `Some(removed)` if an item was removed to make room for the new one. Returns `Err(())` if
	/// `element` cannot be inserted.
	pub fn force_insert_keep_left(&mut self, index: usize, element: T) -> Result<Option<T>, ()> {
		// Check against panics.
		if Self::bound() < index || self.len() < index || Self::bound() == 0 {
			return Err(())
		}
		// Noop condition.
		if Self::bound() == index && self.len() <= Self::bound() {
			return Err(())
		}
		let maybe_removed = if self.is_full() {
			// defensive-only: since we are at capacity, this is a noop.
			self.0.truncate(Self::bound());
			// if we truncate anything, it will be the last one.
			self.0.pop()
		} else {
			None
		};

		// Cannot panic since `self.len() >= index`;
		self.0.insert(index, element);
		Ok(maybe_removed)
	}

	/// Move the position of an item from one location to another in the slice.
	///
	/// Except for the item being moved, the order of the slice remains the same.
	///
	/// - `index` is the location of the item to be moved.
	/// - `insert_position` is the index of the item in the slice which should *immediately follow*
	///   the item which is being moved.
	///
	/// Returns `true` of the operation was successful, otherwise `false` if a noop.
	pub fn slide(&mut self, index: usize, insert_position: usize) -> bool {
		// Check against panics.
		if self.len() <= index || self.len() < insert_position || index == usize::MAX {
			return false
		}
		// Noop conditions.
		if index == insert_position || index + 1 == insert_position {
			return false
		}
		if insert_position < index && index < self.len() {
			// --- --- --- === === === === @@@ --- --- ---
			//            ^-- N            ^O^
			// ...
			//               /-----<<<-----\
			// --- --- --- === === === === @@@ --- --- ---
			//               >>> >>> >>> >>>
			// ...
			// --- --- --- @@@ === === === === --- --- ---
			//             ^N^
			self[insert_position..index + 1].rotate_right(1);
			return true
		} else if insert_position > 0 && index + 1 < insert_position {
			// Note that the apparent asymmetry of these two branches is due to the
			// fact that the "new" position is the position to be inserted *before*.
			// --- --- --- @@@ === === === === --- --- ---
			//             ^O^                ^-- N
			// ...
			//               /----->>>-----\
			// --- --- --- @@@ === === === === --- --- ---
			//               <<< <<< <<< <<<
			// ...
			// --- --- --- === === === === @@@ --- --- ---
			//                             ^N^
			self[index..insert_position].rotate_left(1);
			return true
		}

		debug_assert!(false, "all noop conditions should have been covered above");
		false
	}

	/// Forces the insertion of `s` into `self` truncating first if necessary.
	///
	/// Infallible, but if the bound is zero, then it's a no-op.
	pub fn force_push(&mut self, element: T) {
		if Self::bound() > 0 {
			self.0.truncate(Self::bound() as usize - 1);
			self.0.push(element);
		}
	}

	/// Same as `Vec::resize`, but if `size` is more than [`Self::bound`], then [`Self::bound`] is
	/// used.
	pub fn bounded_resize(&mut self, size: usize, value: T)
	where
		T: Clone,
	{
		let size = size.min(Self::bound());
		self.0.resize(size, value);
	}

	/// Exactly the same semantics as [`Vec::extend`], but returns an error and does nothing if the
	/// length of the outcome is larger than the bound.
	pub fn try_extend(
		&mut self,
		with: impl IntoIterator<Item = T> + ExactSizeIterator,
	) -> Result<(), ()> {
		if with.len().saturating_add(self.len()) <= Self::bound() {
			self.0.extend(with);
			Ok(())
		} else {
			Err(())
		}
	}

	/// Exactly the same semantics as [`Vec::append`], but returns an error and does nothing if the
	/// length of the outcome is larger than the bound.
	pub fn try_append(&mut self, other: &mut Vec<T>) -> Result<(), ()> {
		if other.len().saturating_add(self.len()) <= Self::bound() {
			self.0.append(other);
			Ok(())
		} else {
			Err(())
		}
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

impl<T, S> Default for BoundedVec<T, S> {
	fn default() -> Self {
		// the bound cannot be below 0, which is satisfied by an empty vector
		Self::unchecked_from(Vec::default())
	}
}

impl<T, S> sp_std::fmt::Debug for BoundedVec<T, S>
where
	T: sp_std::fmt::Debug,
	S: Get<u32>,
{
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		f.debug_tuple("BoundedVec").field(&self.0).field(&Self::bound()).finish()
	}
}

impl<T, S> Clone for BoundedVec<T, S>
where
	T: Clone,
{
	fn clone(&self) -> Self {
		// bound is retained
		Self::unchecked_from(self.0.clone())
	}
}

impl<T, S: Get<u32>> TryFrom<Vec<T>> for BoundedVec<T, S> {
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
impl<T, S> AsRef<Vec<T>> for BoundedVec<T, S> {
	fn as_ref(&self) -> &Vec<T> {
		&self.0
	}
}

impl<T, S> AsRef<[T]> for BoundedVec<T, S> {
	fn as_ref(&self) -> &[T] {
		&self.0
	}
}

impl<T, S> AsMut<[T]> for BoundedVec<T, S> {
	fn as_mut(&mut self) -> &mut [T] {
		&mut self.0
	}
}

// will allow for immutable all operations of `Vec<T>` on `BoundedVec<T>`.
impl<T, S> Deref for BoundedVec<T, S> {
	type Target = Vec<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

// Allows for indexing similar to a normal `Vec`. Can panic if out of bound.
impl<T, S, I> Index<I> for BoundedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	type Output = I::Output;

	#[inline]
	fn index(&self, index: I) -> &Self::Output {
		self.0.index(index)
	}
}

impl<T, S, I> IndexMut<I> for BoundedVec<T, S>
where
	I: SliceIndex<[T]>,
{
	#[inline]
	fn index_mut(&mut self, index: I) -> &mut Self::Output {
		self.0.index_mut(index)
	}
}

impl<T, S> sp_std::iter::IntoIterator for BoundedVec<T, S> {
	type Item = T;
	type IntoIter = sp_std::vec::IntoIter<T>;
	fn into_iter(self) -> Self::IntoIter {
		self.0.into_iter()
	}
}

impl<T, S> codec::DecodeLength for BoundedVec<T, S> {
	fn len(self_encoded: &[u8]) -> Result<usize, codec::Error> {
		// `BoundedVec<T, _>` stored just a `Vec<T>`, thus the length is at the beginning in
		// `Compact` form, and same implementation as `Vec<T>` can be used.
		<Vec<T> as codec::DecodeLength>::len(self_encoded)
	}
}

impl<T, BoundSelf, BoundRhs> PartialEq<BoundedVec<T, BoundRhs>> for BoundedVec<T, BoundSelf>
where
	T: PartialEq,
	BoundSelf: Get<u32>,
	BoundRhs: Get<u32>,
{
	fn eq(&self, rhs: &BoundedVec<T, BoundRhs>) -> bool {
		BoundSelf::get() == BoundRhs::get() && self.0 == rhs.0
	}
}

impl<T: PartialEq, S: Get<u32>> PartialEq<Vec<T>> for BoundedVec<T, S> {
	fn eq(&self, other: &Vec<T>) -> bool {
		&self.0 == other
	}
}

impl<T, S: Get<u32>> Eq for BoundedVec<T, S> where T: Eq {}

impl<T, S> StorageDecodeLength for BoundedVec<T, S> {}

impl<T, S: Get<u32>> StorageTryAppend<T> for BoundedVec<T, S> {
	fn bound() -> usize {
		S::get() as usize
	}
}

impl<T, S> MaxEncodedLen for BoundedVec<T, S>
where
	T: MaxEncodedLen,
	S: Get<u32>,
	BoundedVec<T, S>: Encode,
{
	fn max_encoded_len() -> usize {
		// BoundedVec<T, S> encodes like Vec<T> which encodes like [T], which is a compact u32
		// plus each item in the slice:
		// https://docs.substrate.io/v3/advanced/scale-codec
		codec::Compact(S::get())
			.encoded_size()
			.saturating_add(Self::bound().saturating_mul(T::max_encoded_len()))
	}
}

impl<I, T, Bound> TryCollect<BoundedVec<T, Bound>> for I
where
	I: ExactSizeIterator + Iterator<Item = T>,
	Bound: Get<u32>,
{
	type Error = &'static str;

	fn try_collect(self) -> Result<BoundedVec<T, Bound>, Self::Error> {
		if self.len() > Bound::get() as usize {
			Err("iterator length too big")
		} else {
			Ok(BoundedVec::<T, Bound>::unchecked_from(self.collect::<Vec<T>>()))
		}
	}
}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::{bounded_vec, traits::ConstU32, Twox128};
	use sp_io::TestExternalities;

	crate::generate_storage_alias! { Prefix, Foo => Value<BoundedVec<u32, ConstU32<7>>> }
	crate::generate_storage_alias! { Prefix, FooMap => Map<(Twox128, u32), BoundedVec<u32, ConstU32<7>>> }
	crate::generate_storage_alias! {
		Prefix,
		FooDoubleMap => DoubleMap<(Twox128, u32), (Twox128, u32), BoundedVec<u32, ConstU32<7>>>
	}

	#[test]
	fn slide_works() {
		let mut b: BoundedVec<u32, ConstU32<6>> = bounded_vec![0, 1, 2, 3, 4, 5];
		assert!(b.slide(1, 5));
		assert_eq!(*b, vec![0, 2, 3, 4, 1, 5]);
		assert!(b.slide(4, 0));
		assert_eq!(*b, vec![1, 0, 2, 3, 4, 5]);
		assert!(b.slide(0, 2));
		assert_eq!(*b, vec![0, 1, 2, 3, 4, 5]);
		assert!(b.slide(1, 6));
		assert_eq!(*b, vec![0, 2, 3, 4, 5, 1]);
		assert!(b.slide(0, 6));
		assert_eq!(*b, vec![2, 3, 4, 5, 1, 0]);
		assert!(b.slide(5, 0));
		assert_eq!(*b, vec![0, 2, 3, 4, 5, 1]);
		assert!(!b.slide(6, 0));
		assert!(!b.slide(7, 0));
		assert_eq!(*b, vec![0, 2, 3, 4, 5, 1]);

		let mut c: BoundedVec<u32, ConstU32<6>> = bounded_vec![0, 1, 2];
		assert!(!c.slide(1, 5));
		assert_eq!(*c, vec![0, 1, 2]);
		assert!(!c.slide(4, 0));
		assert_eq!(*c, vec![0, 1, 2]);
		assert!(!c.slide(3, 0));
		assert_eq!(*c, vec![0, 1, 2]);
		assert!(c.slide(2, 0));
		assert_eq!(*c, vec![2, 0, 1]);
	}

	#[test]
	fn slide_noops_work() {
		let mut b: BoundedVec<u32, ConstU32<6>> = bounded_vec![0, 1, 2, 3, 4, 5];
		assert!(!b.slide(3, 3));
		assert_eq!(*b, vec![0, 1, 2, 3, 4, 5]);
		assert!(!b.slide(3, 4));
		assert_eq!(*b, vec![0, 1, 2, 3, 4, 5]);
	}

	#[test]
	fn force_insert_keep_left_works() {
		let mut b: BoundedVec<u32, ConstU32<4>> = bounded_vec![];
		assert_eq!(b.force_insert_keep_left(1, 10), Err(()));
		assert!(b.is_empty());

		assert_eq!(b.force_insert_keep_left(0, 30), Ok(None));
		assert_eq!(b.force_insert_keep_left(0, 10), Ok(None));
		assert_eq!(b.force_insert_keep_left(1, 20), Ok(None));
		assert_eq!(b.force_insert_keep_left(3, 40), Ok(None));
		assert_eq!(*b, vec![10, 20, 30, 40]);
		// at capacity.
		assert_eq!(b.force_insert_keep_left(4, 41), Err(()));
		assert_eq!(*b, vec![10, 20, 30, 40]);
		assert_eq!(b.force_insert_keep_left(3, 31), Ok(Some(40)));
		assert_eq!(*b, vec![10, 20, 30, 31]);
		assert_eq!(b.force_insert_keep_left(1, 11), Ok(Some(31)));
		assert_eq!(*b, vec![10, 11, 20, 30]);
		assert_eq!(b.force_insert_keep_left(0, 1), Ok(Some(30)));
		assert_eq!(*b, vec![1, 10, 11, 20]);

		let mut z: BoundedVec<u32, ConstU32<0>> = bounded_vec![];
		assert!(z.is_empty());
		assert_eq!(z.force_insert_keep_left(0, 10), Err(()));
		assert!(z.is_empty());
	}

	#[test]
	fn force_insert_keep_right_works() {
		let mut b: BoundedVec<u32, ConstU32<4>> = bounded_vec![];
		assert_eq!(b.force_insert_keep_right(1, 10), Err(()));
		assert!(b.is_empty());

		assert_eq!(b.force_insert_keep_right(0, 30), Ok(None));
		assert_eq!(b.force_insert_keep_right(0, 10), Ok(None));
		assert_eq!(b.force_insert_keep_right(1, 20), Ok(None));
		assert_eq!(b.force_insert_keep_right(3, 40), Ok(None));
		assert_eq!(*b, vec![10, 20, 30, 40]);

		// at capacity.
		assert_eq!(b.force_insert_keep_right(0, 0), Err(()));
		assert_eq!(*b, vec![10, 20, 30, 40]);
		assert_eq!(b.force_insert_keep_right(1, 11), Ok(Some(10)));
		assert_eq!(*b, vec![11, 20, 30, 40]);
		assert_eq!(b.force_insert_keep_right(3, 31), Ok(Some(11)));
		assert_eq!(*b, vec![20, 30, 31, 40]);
		assert_eq!(b.force_insert_keep_right(4, 41), Ok(Some(20)));
		assert_eq!(*b, vec![30, 31, 40, 41]);

		assert_eq!(b.force_insert_keep_right(5, 69), Err(()));
		assert_eq!(*b, vec![30, 31, 40, 41]);

		let mut z: BoundedVec<u32, ConstU32<0>> = bounded_vec![];
		assert!(z.is_empty());
		assert_eq!(z.force_insert_keep_right(0, 10), Err(()));
		assert!(z.is_empty());
	}

	#[test]
	fn bound_returns_correct_value() {
		assert_eq!(BoundedVec::<u32, ConstU32<7>>::bound(), 7);
	}

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}

	#[test]
	fn try_insert_works() {
		let mut bounded: BoundedVec<u32, ConstU32<4>> = bounded_vec![1, 2, 3];
		bounded.try_insert(1, 0).unwrap();
		assert_eq!(*bounded, vec![1, 0, 2, 3]);

		assert!(bounded.try_insert(0, 9).is_err());
		assert_eq!(*bounded, vec![1, 0, 2, 3]);
	}

	#[test]
	fn constructor_macro_works() {
		use frame_support::bounded_vec;

		// With values. Use some brackets to make sure the macro doesn't expand.
		let bv: BoundedVec<(u32, u32), ConstU32<3>> = bounded_vec![(1, 2), (1, 2), (1, 2)];
		assert_eq!(bv, vec![(1, 2), (1, 2), (1, 2)]);

		// With repetition.
		let bv: BoundedVec<(u32, u32), ConstU32<3>> = bounded_vec![(1, 2); 3];
		assert_eq!(bv, vec![(1, 2), (1, 2), (1, 2)]);
	}

	#[test]
	#[should_panic(expected = "insertion index (is 9) should be <= len (is 3)")]
	fn try_inert_panics_if_oob() {
		let mut bounded: BoundedVec<u32, ConstU32<4>> = bounded_vec![1, 2, 3];
		bounded.try_insert(9, 0).unwrap();
	}

	#[test]
	fn try_push_works() {
		let mut bounded: BoundedVec<u32, ConstU32<4>> = bounded_vec![1, 2, 3];
		bounded.try_push(0).unwrap();
		assert_eq!(*bounded, vec![1, 2, 3, 0]);

		assert!(bounded.try_push(9).is_err());
	}

	#[test]
	fn deref_coercion_works() {
		let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
		// these methods come from deref-ed vec.
		assert_eq!(bounded.len(), 3);
		assert!(bounded.iter().next().is_some());
		assert!(!bounded.is_empty());
	}

	#[test]
	fn try_mutate_works() {
		let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3, 4, 5, 6];
		let bounded = bounded.try_mutate(|v| v.push(7)).unwrap();
		assert_eq!(bounded.len(), 7);
		assert!(bounded.try_mutate(|v| v.push(8)).is_none());
	}

	#[test]
	fn slice_indexing_works() {
		let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3, 4, 5, 6];
		assert_eq!(&bounded[0..=2], &[1, 2, 3]);
	}

	#[test]
	fn vec_eq_works() {
		let bounded: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3, 4, 5, 6];
		assert_eq!(bounded, vec![1, 2, 3, 4, 5, 6]);
	}

	#[test]
	fn too_big_vec_fail_to_decode() {
		let v: Vec<u32> = vec![1, 2, 3, 4, 5];
		assert_eq!(
			BoundedVec::<u32, ConstU32<4>>::decode(&mut &v.encode()[..]),
			Err("BoundedVec exceeds its limit".into()),
		);
	}

	#[test]
	fn can_be_collected() {
		let b1: BoundedVec<u32, ConstU32<5>> = bounded_vec![1, 2, 3, 4];
		let b2: BoundedVec<u32, ConstU32<5>> = b1.iter().map(|x| x + 1).try_collect().unwrap();
		assert_eq!(b2, vec![2, 3, 4, 5]);

		// can also be collected into a collection of length 4.
		let b2: BoundedVec<u32, ConstU32<4>> = b1.iter().map(|x| x + 1).try_collect().unwrap();
		assert_eq!(b2, vec![2, 3, 4, 5]);

		// can be mutated further into iterators that are `ExactSizedIterator`.
		let b2: BoundedVec<u32, ConstU32<4>> =
			b1.iter().map(|x| x + 1).rev().try_collect().unwrap();
		assert_eq!(b2, vec![5, 4, 3, 2]);

		let b2: BoundedVec<u32, ConstU32<4>> =
			b1.iter().map(|x| x + 1).rev().skip(2).try_collect().unwrap();
		assert_eq!(b2, vec![3, 2]);
		let b2: BoundedVec<u32, ConstU32<2>> =
			b1.iter().map(|x| x + 1).rev().skip(2).try_collect().unwrap();
		assert_eq!(b2, vec![3, 2]);

		let b2: BoundedVec<u32, ConstU32<4>> =
			b1.iter().map(|x| x + 1).rev().take(2).try_collect().unwrap();
		assert_eq!(b2, vec![5, 4]);
		let b2: BoundedVec<u32, ConstU32<2>> =
			b1.iter().map(|x| x + 1).rev().take(2).try_collect().unwrap();
		assert_eq!(b2, vec![5, 4]);

		// but these worn't work
		let b2: Result<BoundedVec<u32, ConstU32<3>>, _> = b1.iter().map(|x| x + 1).try_collect();
		assert!(b2.is_err());

		let b2: Result<BoundedVec<u32, ConstU32<1>>, _> =
			b1.iter().map(|x| x + 1).rev().take(2).try_collect();
		assert!(b2.is_err());
	}

	#[test]
	fn eq_works() {
		// of same type
		let b1: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
		let b2: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
		assert_eq!(b1, b2);

		// of different type, but same value and bound.
		crate::parameter_types! {
			B1: u32 = 7;
			B2: u32 = 7;
		}
		let b1: BoundedVec<u32, B1> = bounded_vec![1, 2, 3];
		let b2: BoundedVec<u32, B2> = bounded_vec![1, 2, 3];
		assert_eq!(b1, b2);
	}

	#[test]
	fn ord_works() {
		use std::cmp::Ordering;
		let b1: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 2, 3];
		let b2: BoundedVec<u32, ConstU32<7>> = bounded_vec![1, 3, 2];

		// ordering for vec is lexicographic.
		assert_eq!(b1.cmp(&b2), Ordering::Less);
		assert_eq!(b1.cmp(&b2), b1.into_inner().cmp(&b2.into_inner()));
	}

	#[test]
	fn try_extend_works() {
		let mut b: BoundedVec<u32, ConstU32<5>> = bounded_vec![1, 2, 3];

		assert!(b.try_extend(vec![4].into_iter()).is_ok());
		assert_eq!(*b, vec![1, 2, 3, 4]);

		assert!(b.try_extend(vec![5].into_iter()).is_ok());
		assert_eq!(*b, vec![1, 2, 3, 4, 5]);

		assert!(b.try_extend(vec![6].into_iter()).is_err());
		assert_eq!(*b, vec![1, 2, 3, 4, 5]);

		let mut b: BoundedVec<u32, ConstU32<5>> = bounded_vec![1, 2, 3];
		assert!(b.try_extend(vec![4, 5].into_iter()).is_ok());
		assert_eq!(*b, vec![1, 2, 3, 4, 5]);

		let mut b: BoundedVec<u32, ConstU32<5>> = bounded_vec![1, 2, 3];
		assert!(b.try_extend(vec![4, 5, 6].into_iter()).is_err());
		assert_eq!(*b, vec![1, 2, 3]);
	}
}
