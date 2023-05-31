// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Paged storage list.

// links are better than no links - even when they refer to private stuff.
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

use codec::{Decode, Encode, EncodeLike, FullCodec};
use core::marker::PhantomData;
use frame_support::{
	defensive,
	storage::StoragePrefixedContainer,
	traits::{Get, StorageInstance},
	CloneNoBound, DebugNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound,
};
use sp_runtime::traits::Saturating;
use sp_std::prelude::*;

pub type PageIndex = u32;
pub type ValueIndex = u32;

/// A paginated storage list.
///
/// # Motivation
///
/// This type replaces `StorageValue<Vec<V>>` in situations where only iteration and appending is
/// needed. There are a few places where this is the case. A paginated structure reduces the memory
/// usage when a storage transactions needs to be rolled back. The main motivation is therefore a
/// reduction of runtime memory on storage transaction rollback. Should be configured such that the
/// size of a page is about 64KiB. This can only be ensured when `V` implements `MaxEncodedLen`.
///
/// # Implementation
///
/// The metadata of this struct is stored in [`StoragePagedListMeta`]. The data is stored in
/// [`Page`]s.
///
/// Each [`Page`] holds at most `ValuesPerNewPage` values in its `values` vector. The last page is
/// the only one that could have less than `ValuesPerNewPage` values.  
/// **Iteration** happens by starting
/// at [`first_page`][StoragePagedListMeta::first_page]/
/// [`first_value_offset`][StoragePagedListMeta::first_value_offset] and incrementing these indices
/// as long as there are elements in the page and there are pages in storage. All elements of a page
/// are loaded once a page is read from storage. Iteration then happens on the cached elements. This
/// reduces the number of storage `read` calls on the overlay. **Appending** to the list happens by
/// appending to the last page by utilizing [`sp_io::storage::append`]. It allows to directly extend
/// the elements of `values` vector of the page without loading the whole vector from storage. A new
/// page is instantiated once [`Page::next`] overflows `ValuesPerNewPage`. Its vector will also be
/// created through [`sp_io::storage::append`]. **Draining** advances the internal indices identical
/// to Iteration. It additionally persists the increments to storage and thereby 'drains' elements.
/// Completely drained pages are deleted from storage.
///
/// # Further Observations
///
/// - The encoded layout of a page is exactly its [`Page::values`]. The [`Page::next`] offset is
///   stored in the [`StoragePagedListMeta`] instead. There is no particular reason for this,
///   besides having all management state handy in one location.
/// - The PoV complexity of iterating compared to a `StorageValue<Vec<V>>` is improved for
///   "shortish" iterations and worse for total iteration. The append complexity is identical in the
///   asymptotic case when using an `Appender`, and worse in all. For example when appending just
///   one value.
/// - It does incur a read overhead on the host side as compared to a `StorageValue<Vec<V>>`.
pub struct StoragePagedList<Prefix, Value, ValuesPerNewPage> {
	_phantom: PhantomData<(Prefix, Value, ValuesPerNewPage)>,
}

/// The state of a [`StoragePagedList`].
///
/// This struct doubles as [`frame_support::storage::StorageList::Appender`].
#[derive(
	Encode, Decode, CloneNoBound, PartialEqNoBound, EqNoBound, DebugNoBound, DefaultNoBound,
)]
// todo ignore scale bounds
pub struct StoragePagedListMeta<Prefix, Value, ValuesPerNewPage> {
	/// The first page that could contain a value.
	///
	/// Can be >0 when pages were deleted.
	pub first_page: PageIndex,
	/// The first index inside `first_page` that could contain a value.
	///
	/// Can be >0 when values were deleted.
	pub first_value_offset: ValueIndex,

	/// The last page that could contain data.
	///
	/// Appending starts at this page index.
	pub last_page: PageIndex,
	/// The last value inside `last_page` that could contain a value.
	///
	/// Appending starts at this index. If the page does not hold a value at this index, then the
	/// whole list is empty. The only case where this can happen is when both are `0`.
	pub last_page_len: ValueIndex,

	_phantom: PhantomData<(Prefix, Value, ValuesPerNewPage)>,
}

impl<Prefix, Value, ValuesPerNewPage> frame_support::storage::StorageAppender<Value>
	for StoragePagedListMeta<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	fn append<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		self.append_one(item);
	}
}

impl<Prefix, Value, ValuesPerNewPage> StoragePagedListMeta<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	pub fn from_storage() -> Option<Self> {
		let key = Self::key();

		sp_io::storage::get(&key).and_then(|raw| Self::decode(&mut &raw[..]).ok())
	}

	pub fn key() -> Vec<u8> {
		meta_key::<Prefix>()
	}

	pub fn append_one<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		// Note: we use >= here in case someone decreased it in a runtime upgrade.
		if self.last_page_len >= ValuesPerNewPage::get() {
			self.last_page.saturating_inc();
			self.last_page_len = 0;
		}
		let key = page_key::<Prefix>(self.last_page);
		self.last_page_len.saturating_inc();
		sp_io::storage::append(&key, item.encode());
		self.store();
	}

	pub fn store(&self) {
		let key = Self::key();
		self.using_encoded(|enc| sp_io::storage::set(&key, enc));
	}

	pub fn reset(&mut self) {
		*self = Default::default();
		Self::delete();
	}

	pub fn delete() {
		sp_io::storage::clear(&Self::key());
	}
}

/// A page that was decoded from storage and caches its values.
pub struct Page<V> {
	/// The index of the page.
	index: PageIndex,
	/// The remaining values of the page, to be drained by [`Page::next`].
	values: sp_std::iter::Skip<sp_std::vec::IntoIter<V>>,
}

impl<V: FullCodec> Page<V> {
	/// Read the page with `index` from storage and assume the first value at `value_index`.
	pub fn from_storage<Prefix: StorageInstance>(
		index: PageIndex,
		value_index: ValueIndex,
	) -> Option<Self> {
		let key = page_key::<Prefix>(index);
		let values = sp_io::storage::get(&key)
			.and_then(|raw| sp_std::vec::Vec::<V>::decode(&mut &raw[..]).ok())?;
		if values.is_empty() {
			// Dont create empty pages.
			return None
		}
		let values = values.into_iter().skip(value_index as usize);

		Some(Self { index, values })
	}

	/// Whether no more values can be read from this page.
	pub fn is_eof(&self) -> bool {
		self.values.len() == 0
	}

	/// Delete this page from storage.
	pub fn delete<Prefix: StorageInstance>(&self) {
		delete_page::<Prefix>(self.index);
	}
}

/// Delete a page with `index` from storage.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn delete_page<Prefix: StorageInstance>(index: PageIndex) {
	let key = page_key::<Prefix>(index);
	sp_io::storage::clear(&key);
}

/// Storage key of a page with `index`.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn page_key<Prefix: StorageInstance>(index: PageIndex) -> Vec<u8> {
	(StoragePagedListPrefix::<Prefix>::final_prefix(), b"page", index).encode()
}

pub(crate) fn meta_key<Prefix: StorageInstance>() -> Vec<u8> {
	(StoragePagedListPrefix::<Prefix>::final_prefix(), b"meta").encode()
}

impl<V> Iterator for Page<V> {
	type Item = V;

	fn next(&mut self) -> Option<Self::Item> {
		self.values.next()
	}
}

/// Iterates over values of a [`StoragePagedList`].
///
/// Can optionally drain the iterated values.
pub struct StoragePagedListIterator<Prefix, Value, ValuesPerNewPage> {
	// Design: we put the Page into the iterator to have fewer storage look-ups. Yes, these
	// look-ups would be cached anyway, but bugging the overlay on each `.next` call still seems
	// like a poor trade-off than caching it in the iterator directly. Iterating and modifying is
	// not allowed at the same time anyway, just like with maps. Note: if Page is empty then
	// the iterator did not find any data upon setup or ran out of pages.
	page: Option<Page<Value>>,
	drain: bool,
	meta: StoragePagedListMeta<Prefix, Value, ValuesPerNewPage>,
}

impl<Prefix, Value, ValuesPerNewPage> StoragePagedListIterator<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	/// Read self from the storage.
	pub fn from_meta(
		meta: StoragePagedListMeta<Prefix, Value, ValuesPerNewPage>,
		drain: bool,
	) -> Self {
		let page = Page::<Value>::from_storage::<Prefix>(meta.first_page, meta.first_value_offset);
		Self { page, drain, meta }
	}
}

impl<Prefix, Value, ValuesPerNewPage> Iterator
	for StoragePagedListIterator<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		let page = self.page.as_mut()?;
		let value = match page.next() {
			Some(value) => value,
			None => {
				defensive!("There are no empty pages in storage; nuking the list");
				self.meta.reset();
				self.page = None;
				return None
			},
		};

		if page.is_eof() {
			if self.drain {
				page.delete::<Prefix>();
				self.meta.first_value_offset = 0;
				self.meta.first_page.saturating_inc();
			}

			debug_assert!(!self.drain || self.meta.first_page == page.index + 1);
			self.page = Page::from_storage::<Prefix>(page.index.saturating_add(1), 0);
			if self.drain {
				if self.page.is_none() {
					self.meta.reset();
				} else {
					self.meta.store();
				}
			}
		} else {
			if self.drain {
				self.meta.first_value_offset.saturating_inc();
				self.meta.store();
			}
		}
		Some(value)
	}
}

impl<Prefix, Value, ValuesPerNewPage> frame_support::storage::StorageList<Value>
	for StoragePagedList<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	type Iterator = StoragePagedListIterator<Prefix, Value, ValuesPerNewPage>;
	type Appender = StoragePagedListMeta<Prefix, Value, ValuesPerNewPage>;

	fn iter() -> Self::Iterator {
		StoragePagedListIterator::from_meta(Self::read_meta(), false)
	}

	fn drain() -> Self::Iterator {
		StoragePagedListIterator::from_meta(Self::read_meta(), true)
	}

	fn appender() -> Self::Appender {
		Self::appender()
	}
}

impl<Prefix, Value, ValuesPerNewPage> StoragePagedList<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	fn read_meta() -> StoragePagedListMeta<Prefix, Value, ValuesPerNewPage> {
		// Use default here to not require a setup migration.
		StoragePagedListMeta::from_storage().unwrap_or_default()
	}

	/// Provides a fast append iterator.
	///
	/// The list should not be modified while appending. Also don't call it recursively.
	fn appender() -> StoragePagedListMeta<Prefix, Value, ValuesPerNewPage> {
		Self::read_meta()
	}

	/// Return the elements of the list.
	#[cfg(test)]
	fn as_vec() -> Vec<Value> {
		<Self as frame_support::storage::StorageList<_>>::iter().collect()
	}

	/// Return and remove the elements of the list.
	#[cfg(test)]
	fn as_drained_vec() -> Vec<Value> {
		<Self as frame_support::storage::StorageList<_>>::drain().collect()
	}
}

/// Provides the final prefix for a [`StoragePagedList`].
///
/// It solely exists so that when re-using it from the iterator and meta struct, none of the un-used
/// generics bleed through. Otherwise when only having the `StoragePrefixedContainer` implementation
/// on the list directly, the iterator and metadata need to muster *all* generics, even the ones
/// that are completely useless for prefix calculation.
struct StoragePagedListPrefix<Prefix>(PhantomData<Prefix>);

impl<Prefix> frame_support::storage::StoragePrefixedContainer for StoragePagedListPrefix<Prefix>
where
	Prefix: StorageInstance,
{
	fn module_prefix() -> &'static [u8] {
		Prefix::pallet_prefix().as_bytes()
	}

	fn storage_prefix() -> &'static [u8] {
		Prefix::STORAGE_PREFIX.as_bytes()
	}
}

impl<Prefix, Value, ValuesPerNewPage> frame_support::storage::StoragePrefixedContainer
	for StoragePagedList<Prefix, Value, ValuesPerNewPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	ValuesPerNewPage: Get<u32>,
{
	fn module_prefix() -> &'static [u8] {
		StoragePagedListPrefix::<Prefix>::module_prefix()
	}

	fn storage_prefix() -> &'static [u8] {
		StoragePagedListPrefix::<Prefix>::storage_prefix()
	}
}

/// Prelude for (doc)tests.
#[cfg(feature = "std")]
#[allow(dead_code)]
pub(crate) mod mock {
	pub use super::*;
	pub use frame_support::{
		metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
		parameter_types,
		storage::{types::ValueQuery, StorageList as _},
		StorageNoopGuard,
	};
	pub use sp_io::{hashing::twox_128, TestExternalities};

	parameter_types! {
		pub const ValuesPerNewPage: u32 = 5;
		pub const MaxPages: Option<u32> = Some(20);
	}

	pub struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "foo";
	}

	pub type List = StoragePagedList<Prefix, u32, ValuesPerNewPage>;
}

#[cfg(test)]
mod tests {
	use super::mock::*;

	#[test]
	fn append_works() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..1000);
			assert_eq!(List::as_vec(), (0..1000).collect::<Vec<_>>());
		});
	}

	/// Draining all works.
	#[test]
	fn simple_drain_works() {
		TestExternalities::default().execute_with(|| {
			let _g = StorageNoopGuard::default(); // All in all a No-Op
			List::append_many(0..1000);

			assert_eq!(List::as_drained_vec(), (0..1000).collect::<Vec<_>>());

			assert_eq!(List::read_meta(), Default::default());

			// all gone
			assert_eq!(List::as_vec(), Vec::<u32>::new());
			// Need to delete the metadata manually.
			StoragePagedListMeta::<Prefix, u32, ValuesPerNewPage>::delete();
		});
	}

	/// Drain half of the elements and iterator the rest.
	#[test]
	fn partial_drain_works() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..100);

			let vals = List::drain().take(50).collect::<Vec<_>>();
			assert_eq!(vals, (0..50).collect::<Vec<_>>());

			let meta = List::read_meta();
			// Will switch over to `10/0`, but will in the next call.
			assert_eq!((meta.first_page, meta.first_value_offset), (10, 0));

			// 50 gone, 50 to go
			assert_eq!(List::as_vec(), (50..100).collect::<Vec<_>>());
		});
	}

	/// Draining, appending and iterating work together.
	#[test]
	fn drain_append_iter_works() {
		TestExternalities::default().execute_with(|| {
			for r in 1..=100 {
				List::append_many(0..12);
				List::append_many(0..12);

				let dropped = List::drain().take(12).collect::<Vec<_>>();
				assert_eq!(dropped, (0..12).collect::<Vec<_>>());

				assert_eq!(List::as_vec(), (0..12).cycle().take(r * 12).collect::<Vec<_>>());
			}
		});
	}

	/// Pages are removed ASAP.
	#[test]
	fn drain_eager_page_removal() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..9);

			assert!(sp_io::storage::exists(&page_key::<Prefix>(0)));
			assert!(sp_io::storage::exists(&page_key::<Prefix>(1)));

			assert_eq!(List::drain().take(5).count(), 5);
			// Page 0 is eagerly removed.
			assert!(!sp_io::storage::exists(&page_key::<Prefix>(0)));
			assert!(sp_io::storage::exists(&page_key::<Prefix>(1)));
		});
	}

	/// Appending encodes pages as `Vec`.
	#[test]
	fn append_storage_layout() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..9);

			let key = page_key::<Prefix>(0);
			let raw = sp_io::storage::get(&key).expect("Page should be present");
			let as_vec = Vec::<u32>::decode(&mut &raw[..]).unwrap();
			assert_eq!(as_vec.len(), 5, "First page contains 5");

			let key = page_key::<Prefix>(1);
			let raw = sp_io::storage::get(&key).expect("Page should be present");
			let as_vec = Vec::<u32>::decode(&mut &raw[..]).unwrap();
			assert_eq!(as_vec.len(), 4, "Second page contains 4");

			let meta = sp_io::storage::get(&meta_key::<Prefix>()).expect("Meta should be present");
			let meta: StoragePagedListMeta<Prefix, u32, ValuesPerNewPage> =
				Decode::decode(&mut &meta[..]).unwrap();
			assert_eq!(meta.first_page, 0);
			assert_eq!(meta.first_value_offset, 0);
			assert_eq!(meta.last_page, 1);
			assert_eq!(meta.last_page_len, 4);

			let page = Page::<u32>::from_storage::<Prefix>(0, 0).unwrap();
			assert_eq!(page.index, 0);
			assert_eq!(page.values.count(), 5);

			let page = Page::<u32>::from_storage::<Prefix>(1, 0).unwrap();
			assert_eq!(page.index, 1);
			assert_eq!(page.values.count(), 4);
		});
	}

	#[test]
	fn page_key_correct() {
		let got = page_key::<Prefix>(0);
		let pallet_prefix = StoragePagedListPrefix::<Prefix>::final_prefix();
		let want = (pallet_prefix, b"page", 0).encode();

		assert_eq!(want.len(), 32 + 4 + 4);
		assert!(want.starts_with(&pallet_prefix[..]));
		assert_eq!(got, want);
	}

	#[test]
	fn meta_key_correct() {
		let got = meta_key::<Prefix>();
		let pallet_prefix = StoragePagedListPrefix::<Prefix>::final_prefix();
		let want = (pallet_prefix, b"meta").encode();

		assert_eq!(want.len(), 32 + 4);
		assert!(want.starts_with(&pallet_prefix[..]));
		assert_eq!(got, want);
	}

	#[test]
	fn peekable_drain_also_deletes() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..10);

			let mut iter = List::drain().peekable();
			assert_eq!(iter.peek(), Some(&0));
			// `peek` does remove one element...
			assert_eq!(List::iter().count(), 9);
		});
	}
}
