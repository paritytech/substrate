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

use crate::{
	defensive,
	traits::{Get, GetDefault, StorageInstance},
	CloneNoBound, DebugNoBound, DefaultNoBound, EqNoBound, PartialEqNoBound, StorageHasher,
};
use codec::{Decode, Encode, EncodeLike, FullCodec};
use core::marker::PhantomData;
use sp_arithmetic::traits::Saturating;
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
/// Each [`Page`] holds at most `ValuesPerPage` values in its `values` vector. The last page is the
/// only one that could have less than `ValuesPerPage` values.  
/// **Iteration** happens by starting
/// at [`first_page`][StoragePagedListMeta::first_page]/[`first_value`][StoragePagedListMeta::first_value] and incrementing
/// these indices as long as there are elements in the page and there are pages in storage. All
/// elements of a page are loaded once a page is read from storage. Iteration then happens on the
/// cached elements. This reduces the storage `read` calls on the overlay.  
/// **Appending** to the list happens by appending to the last page by utilizing
/// [`sp_io::storage::append`]. It allows to directly extend the elements of `values` vector of the
/// page without loading the whole vector from storage. A new page is instanced once [`Page::next`]
/// overflows `ValuesPerPage`. Its vector will also be created through [`sp_io::storage::append`].  
/// **Draining** advances the internal indices identical to Iteration. It additionally persists the
/// increments to storage and thereby 'drains' elements. Completely drained pages are deleted from
/// storage.
///
/// # Further Observations
///
/// - The encoded layout of a page is exactly its [`Page::values`]. The [`Page::next`] offset is
///   stored in the [`StoragePagedListMeta`] instead. There is no particular reason for this,
///   besides having all management state handy in one location.
/// - The PoV complexity of iterating compared to a `StorageValue<Vec<V>>` is improved for
///   "shortish" iterations and worse for total iteration. The append complexity is identical in the
///   asymptotic case when using an `Appendix`, and worse in all. For example when appending just
///   one value.
/// - It does incur a read overhead on the host side as compared to a `StorageValue<Vec<V>>`.
pub struct StoragePagedList<Prefix, Hasher, Value, ValuesPerPage, MaxPages = GetDefault> {
	_phantom: PhantomData<(Prefix, Hasher, Value, ValuesPerPage, MaxPages)>,
}

/// The state of a [`StoragePagedList`].
///
/// This struct doubles as [`crate::storage::StorageList::Appendix`].
#[derive(
	Encode, Decode, CloneNoBound, PartialEqNoBound, EqNoBound, DebugNoBound, DefaultNoBound,
)]
// todo ignore scale bounds
pub struct StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage> {
	/// The first page that contains a value.
	///
	/// Can be >0 when pages were deleted.
	pub first_page: PageIndex,
	/// The first value inside `first_page` that contains a value.
	///
	/// Can be >0 when values were deleted.
	pub first_value: ValueIndex,

	/// The last page that could contain data.
	///
	/// Iteration starts at this page index.
	pub last_page: PageIndex,
	/// The last value inside `last_page` that could contain a value.
	///
	/// Iteration starts at this index. If the page does not hold a value at this index, then the
	/// whole list is empty. The only case where this can happen is when both are `0`.
	pub last_value: ValueIndex,

	_phantom: PhantomData<(Prefix, Value, Hasher, ValuesPerPage)>,
}

impl<Prefix, Value, Hasher, ValuesPerPage> crate::storage::StorageAppendix<Value>
	for StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
{
	fn append<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		self.append_one(item);
	}
}

impl<Prefix, Value, Hasher, ValuesPerPage>
	StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
{
	pub fn from_storage() -> Option<Self> {
		let key = Self::key();

		sp_io::storage::get(key.as_ref()).and_then(|raw| {
			Self::decode(&mut &raw[..]).ok()
		})
	}

	pub fn key() -> Hasher::Output {
		(Prefix::STORAGE_PREFIX, b"meta").using_encoded(Hasher::hash)
	}

	pub fn append_one<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		// Note: we use >= here in case someone decreased it in a runtime upgrade.
		if self.last_value >= ValuesPerPage::get() {
			self.last_value = 0;
			self.last_page.saturating_inc();
		}
		let key = page_key::<Prefix, Hasher>(self.last_page);
		self.last_value.saturating_inc();
		log::info!("Appending to page/val {}/{}", self.last_page, self.last_value);
		// Pages are `Vec` and therefore appendable.
		sp_io::storage::append(key.as_ref(), item.encode());
		self.store();
	}

	pub fn store(&self) {
		let key = Self::key();
		log::info!("Storing: {:?}", &self);
		self.using_encoded(|encoded| sp_io::storage::set(key.as_ref(), encoded));
	}

	pub fn reset(&mut self) {
		*self = Default::default();
		Self::clear();
	}

	pub fn clear() {
		let key = Self::key();
		sp_io::storage::clear(key.as_ref());
	}
}

pub struct Page<V> {
	next: ValueIndex,
	index: PageIndex,
	// invariant: this is **never** empty
	values: sp_std::vec::Vec<V>,
}

impl<V: FullCodec> Page<V> {
	/// Decode a page with `index` from storage.
	pub fn from_storage<Prefix: StorageInstance, Hasher: StorageHasher>(
		index: PageIndex,
	) -> Option<Self> {
		let key = page_key::<Prefix, Hasher>(index);
		let values = sp_io::storage::get(key.as_ref())
			.and_then(|raw| sp_std::vec::Vec::<V>::decode(&mut &raw[..]).ok());
		let values = values.unwrap_or_default();
		if values.is_empty() {
			None
		} else {
			Some(Self { next: 0, index, values })
		}
	}

	/// Delete this page from storage.
	pub fn delete<Prefix: StorageInstance, Hasher: StorageHasher>(&self) {
		delete_page::<Prefix, Hasher>(self.index);
	}
}

/// Delete a page with `index` from storage.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn delete_page<Prefix: StorageInstance, Hasher: StorageHasher>(index: PageIndex) {
	let key = page_key::<Prefix, Hasher>(index);
	sp_io::storage::clear(key.as_ref());
}

/// Storage key of a page with `index`.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn page_key<Prefix: StorageInstance, Hasher: StorageHasher>(
	index: PageIndex,
) -> Hasher::Output {
	(Prefix::STORAGE_PREFIX, b"page", index).using_encoded(Hasher::hash)
}

impl<V: Clone> Iterator for Page<V> {
	type Item = V;

	fn next(&mut self) -> Option<Self::Item> {
		let val = self.values.get(self.next as usize).cloned();
		self.next.saturating_inc();
		val
	}
}

/// Iterates over values of a [`StoragePagedList`].
///
/// Can optionally drain the iterated values.
pub struct StoragePagedListIterator<Prefix, Value, Hasher, ValuesPerPage> {
	// Design: we put the Page into the iterator to have fewer storage look-ups. Yes, these
	// look-ups would be cached anyway, but bugging the overlay on each `.next` call still seems
	// like a poor trade-off than caching it in the iterator directly. Iterating and modifying is
	// not allowed at the same time anyway, just like with maps. Note: if Page is empty then
	// the iterator did not find any data upon setup or ran out of pages.
	page: Option<Page<Value>>,
	drain: bool,
	meta: StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>,
}

impl<Prefix, Value, Hasher, ValuesPerPage>
	StoragePagedListIterator<Prefix, Value, Hasher, ValuesPerPage>
where
	Prefix: StorageInstance,
	Value: FullCodec + Clone,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
{
	/// Read self from the storage.
	pub fn from_meta(
		meta: StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>,
		drain: bool,
	) -> Self {
		let mut page = Page::<Value>::from_storage::<Prefix, Hasher>(meta.first_page);

		if let Some(ref mut page) = page {
			page.next = meta.first_value;
		}

		Self { page, drain, meta }
	}
}

impl<Prefix, Value, Hasher, ValuesPerPage> Iterator
	for StoragePagedListIterator<Prefix, Value, Hasher, ValuesPerPage>
where
	Prefix: StorageInstance,
	Value: FullCodec + Clone,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
{
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		let page = self.page.as_mut()?;

		if let Some(val) = page.next() {
			if self.drain {
				self.meta.first_value.saturating_inc();
				self.meta.store()
			}
			return Some(val)
		}
		if self.drain {
			// page is empty
			page.delete::<Prefix, Hasher>();
			self.meta.first_value = 0;
			self.meta.first_page.saturating_inc();
			self.meta.store();
		}

		let Some(mut page) = Page::from_storage::<Prefix, Hasher>(page.index.saturating_add(1)) else {
			self.page = None;
			if self.drain {
				self.meta.reset();
			}
			return None;
		};

		if let Some(val) = page.next() {
			self.page = Some(page);
			if self.drain {
				self.meta.first_value.saturating_inc();
				self.meta.store();
			}
			return Some(val)
		}

		defensive!("StoragePagedListIterator: empty pages do not exist: storage corrupted");
		// Put the storage back into a consistent state.
		self.meta.reset();
		self.page = None;
		None
	}
}

impl<Prefix, Hasher, Value, ValuesPerPage, MaxPages> crate::storage::StorageList<Value>
	for StoragePagedList<Prefix, Hasher, Value, ValuesPerPage, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec + Clone,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	type Iterator = StoragePagedListIterator<Prefix, Value, Hasher, ValuesPerPage>;
	type Appendix = StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>;

	fn iter() -> Self::Iterator {
		StoragePagedListIterator::from_meta(Self::read_meta(), false)
	}

	fn drain() -> Self::Iterator {
		StoragePagedListIterator::from_meta(Self::read_meta(), true)
	}

	fn appendix() -> Self::Appendix {
		Self::appendix()
	}
}


#[cfg(feature = "std")]
impl<Prefix, Hasher, Value, ValuesPerPage, MaxPages> crate::storage::TestingStoragePagedList<Value>
	for StoragePagedList<Prefix, Hasher, Value, ValuesPerPage, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec + Clone,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	type Metadata = StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage>;

	fn read_meta() -> Option<Self::Metadata> {
		Self::Metadata::from_storage()
	}

	fn clear_meta() {
		Self::Metadata::clear()
	}
}

impl<Prefix, Hasher, Value, ValuesPerPage, MaxPages>
	StoragePagedList<Prefix, Hasher, Value, ValuesPerPage, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec + Clone,
	Hasher: StorageHasher,
	ValuesPerPage: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	fn read_meta() -> StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage> {
		// Use default here to not require a setup migration.
		StoragePagedListMeta::from_storage().unwrap_or_default()
	}

	/// Provides a fast append iterator.
	///
	/// The list should not be modified while appending. Also don't call it recursively.
	fn appendix() -> StoragePagedListMeta<Prefix, Value, Hasher, ValuesPerPage> {
		Self::read_meta()
	}
}

/// Prelude for doc-tests.
#[cfg(feature = "std")]
#[allow(dead_code)]
pub(crate) mod mock {
	pub use super::*;
	pub use crate::{
		hash::*,
		metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
		parameter_types,
		storage::{types::ValueQuery, StorageList as _, TestingStoragePagedList},
		StorageNoopGuard,
	};
	pub use sp_io::{hashing::twox_128, TestExternalities};

	parameter_types! {
		pub const ValuesPerPage: u32 = 5;
		pub const MaxPages: Option<u32> = Some(20);
	}

	pub struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "foo";
	}

	pub type List = StoragePagedList<Prefix, Blake2_128Concat, u32, ValuesPerPage, MaxPages>;
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
			StoragePagedListMeta::<Prefix, u32, Blake2_128Concat, ValuesPerPage>::clear();
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
			assert_eq!((meta.first_page, meta.first_value), (9, 5));

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
