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

//! Paged storage n-map.

// links are better than no links - even when they refer to private stuff.
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

use super::key::KeyGenerator;
use crate::{
	metadata_ir::{StorageEntryMetadataIR, StorageEntryTypeIR},
	storage::{types::StorageEntryMetadataBuilder, EncodeLikeTuple, TupleToEncodedIter},
	traits::{StorageInfo, StorageInstance},
	StorageHasher,
};
use codec::{Decode, Encode, EncodeLike, FullCodec};
use core::marker::PhantomData;
use frame_support::{
	defensive, storage::StoragePrefixedContainer, traits::Get, CloneNoBound, DebugNoBound,
	DefaultNoBound, EqNoBound, PartialEqNoBound,
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
/// The metadata of this struct is stored in [`StoragePagedNMapMeta`]. The data is stored in
/// [`Page`]s.
///
/// Each [`Page`] holds at most `HeapSize` values in its `values` vector. The last page is
/// the only one that could have less than `HeapSize` values.  
/// **Iteration** happens by starting
/// at [`first_page`][StoragePagedNMapMeta::first_page]/
/// [`first_value_offset`][StoragePagedNMapMeta::first_value_offset] and incrementing these indices
/// as long as there are elements in the page and there are pages in storage. All elements of a page
/// are loaded once a page is read from storage. Iteration then happens on the cached elements. This
/// reduces the number of storage `read` calls on the overlay. **Appending** to the list happens by
/// appending to the last page by utilizing [`sp_io::storage::append`]. It allows to directly extend
/// the elements of `values` vector of the page without loading the whole vector from storage. A new
/// page is instantiated once [`Page::next`] overflows `HeapSize`. Its vector will also be
/// created through [`sp_io::storage::append`]. **Draining** advances the internal indices identical
/// to Iteration. It additionally persists the increments to storage and thereby 'drains' elements.
/// Completely drained pages are deleted from storage.
///
/// # Further Observations
///
/// - The encoded layout of a page is exactly its [`Page::values`]. The [`Page::next`] offset is
///   stored in the [`StoragePagedNMapMeta`] instead. There is no particular reason for this,
///   besides having all management state handy in one location.
/// - The PoV complexity of iterating compared to a `StorageValue<Vec<V>>` is improved for
///   "shortish" iterations and worse for total iteration. The append complexity is identical in the
///   asymptotic case when using an `Appender`, and worse in all. For example when appending just
///   one value.
/// - It does incur a read overhead on the host side as compared to a `StorageValue<Vec<V>>`.
#[derive(Default)]
pub struct StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages = ()> {
	/// Phantom data.
	pub _phantom: PhantomData<(Prefix, Key, Value, HeapSize, MaxPages)>,
}

// FAIL-CI: TODO add test for Value MEL bound to be <= HeapSize

/// The state of a [`StoragePagedNMap`].
///
/// This struct doubles as [`frame_support::storage::StorageList::Appender`].
#[derive(
	Encode, Decode, CloneNoBound, PartialEqNoBound, EqNoBound, DebugNoBound, DefaultNoBound,
)]
pub struct StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages = ()> {
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
	pub last_page_byte_offset: u32,

	/// The total number of items currently present in the list.
	pub total_items: u64,
	/// Phantom data.
	pub _phantom: PhantomData<(Prefix, Key, KArg, Value, HeapSize, MaxPages)>,
}

pub struct StoragePagedNMapAppender<Prefix, Key, KArg, Value, HeapSize, MaxPages = ()> {
	/// The inner metadata.
	pub meta: StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages>,
	/// The key that values will be appended to.
	pub key: KArg,
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages>
	frame_support::storage::StorageListAppender<Value>
	for StoragePagedNMapAppender<Prefix, Key, KArg, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	fn append<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		self.append_one(item);
	}
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages>
	StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	/// Read the metadata from storage.
	pub fn from_storage(key: KArg) -> Option<Self> {
		let mk = Self::storage_key(key);

		sp_io::storage::get(&mk).and_then(|raw| Self::decode(&mut &raw[..]).ok())
	}

	/// The key under which the metadata is stored.
	pub fn storage_key(key: KArg) -> Vec<u8> {
		meta_key::<Prefix, Key, KArg>(key)
	}

	/// Write the metadata to storage.
	pub fn store(&self, k: KArg) {
		let key = Self::storage_key(k);
		self.using_encoded(|enc| sp_io::storage::set(&key, enc));
	}

	/// Reset the metadata to default and delete it from storage.
	pub fn reset(&mut self, key: KArg) {
		*self = Default::default();
		Self::delete(key);
	}

	/// Delete the metadata from storage.
	pub fn delete(key: KArg) {
		sp_io::storage::clear(&Self::storage_key(key));
	}
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages>
	StoragePagedNMapAppender<Prefix, Key, KArg, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	pub fn append_one<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		let enc_size = item.encoded_size() as u32;
		if (self.meta.last_page_byte_offset.saturating_add(enc_size)) > HeapSize::get() {
			self.meta.last_page.saturating_inc();
			self.meta.last_page_byte_offset = 0;
		}
		let pk = page_key::<Prefix, Key, KArg>(self.key.clone(), self.meta.last_page);
		self.meta.last_page_byte_offset.saturating_accrue(enc_size);
		self.meta.total_items.saturating_inc();
		sp_io::storage::append(&pk, item.encode());
		self.meta.store(self.key.clone());
	}
}

/// A page that was decoded from storage and caches its values.
pub struct Page<K, KArg, V> {
	/// The index of the page.
	pub(crate) index: PageIndex,
	/// The remaining values of the page, to be drained by [`Page::next`].
	pub(crate) values: sp_std::iter::Skip<sp_std::vec::IntoIter<V>>,

	pub(crate) key: KArg,
	_phantom: PhantomData<K>,
}

impl<
		Key: KeyGenerator,
		KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
		V: FullCodec,
	> Page<Key, KArg, V>
{
	/// Read the page with `index` from storage and assume the first value at `value_index`.
	pub fn from_storage<Prefix: StorageInstance>(
		k: KArg,
		index: PageIndex,
		value_index: ValueIndex,
	) -> Option<Self> {
		let key = page_key::<Prefix, Key, KArg>(k.clone(), index);
		let values = sp_io::storage::get(&key)
			.and_then(|raw| sp_std::vec::Vec::<V>::decode(&mut &raw[..]).ok())?;
		if values.is_empty() {
			// Dont create empty pages.
			return None
		}
		let values = values.into_iter().skip(value_index as usize);

		Some(Self { index, values, key: k, _phantom: PhantomData })
	}

	/// Whether no more values can be read from this page.
	pub fn is_eof(&self) -> bool {
		self.values.len() == 0
	}

	/// Delete this page from storage.
	pub fn delete<Prefix: StorageInstance>(&self) {
		delete_page::<Prefix, Key, KArg>(self.key.clone(), self.index);
	}
}

/// Delete a page with `index` from storage.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn delete_page<
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
>(
	key: KArg,
	index: PageIndex,
) {
	let key = page_key::<Prefix, Key, KArg>(key, index);
	sp_io::storage::clear(&key);
}

/// Storage key of a page with `index`.
// Does not live under `Page` since it does not require the `Value` generic.
pub(crate) fn page_key<
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
>(
	key: KArg,
	index: PageIndex,
) -> Vec<u8> {
	let k1 = StoragePagedNMapPrefix::<Prefix>::final_prefix();
	let k2 = Key::final_key(key);

	[&k1[..], &k2[..], b"page", &index.encode()[..]].concat()
}

pub(crate) fn meta_key<
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
>(
	key: KArg,
) -> Vec<u8> {
	let k1 = StoragePagedNMapPrefix::<Prefix>::final_prefix();
	let k2 = Key::final_key(key);

	[&k1[..], &k2[..], b"meta"].concat()
}

impl<K, KArg, V> Iterator for Page<K, KArg, V> {
	type Item = V;

	fn next(&mut self) -> Option<Self::Item> {
		self.values.next()
	}
}

/// Iterates over values of a [`StoragePagedNMap`].
///
/// Can optionally drain the iterated values.
pub struct StoragePagedNMapIterator<Prefix, Key, KArg, Value, HeapSize, MaxPages> {
	// Design: we put the Page into the iterator to have fewer storage look-ups. Yes, these
	// look-ups would be cached anyway, but bugging the overlay on each `.next` call still seems
	// like a poor trade-off than caching it in the iterator directly. Iterating and modifying is
	// not allowed at the same time anyway, just like with maps. Note: if Page is empty then
	// the iterator did not find any data upon setup or ran out of pages.
	page: Option<Page<Key, KArg, Value>>,
	drain: bool,
	meta: StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages>,
	key: KArg,
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages>
	StoragePagedNMapIterator<Prefix, Key, KArg, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	/// Read self from the storage.
	pub fn from_meta(
		meta: StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages>,
		key: KArg,
		drain: bool,
	) -> Self {
		let page = Page::<Key, KArg, Value>::from_storage::<Prefix>(
			key.clone(),
			meta.first_page,
			meta.first_value_offset,
		);
		Self { page, drain, meta, key }
	}
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages> Iterator
	for StoragePagedNMapIterator<Prefix, Key, KArg, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		let page = self.page.as_mut()?;
		let value = match page.next() {
			Some(value) => value,
			None => {
				defensive!("There are no empty pages in storage; nuking the list");
				self.meta.reset(self.key.clone());
				self.page = None;
				return None
			},
		};

		if page.is_eof() {
			if self.drain {
				page.delete::<Prefix>();
				self.meta.first_value_offset = 0;
				self.meta.first_page.saturating_inc();
				self.meta.total_items.saturating_dec();
			}

			debug_assert!(!self.drain || self.meta.first_page == page.index + 1);
			self.page =
				Page::from_storage::<Prefix>(self.key.clone(), page.index.saturating_add(1), 0);
			if self.drain {
				if self.page.is_none() {
					self.meta.reset(self.key.clone());
				} else {
					self.meta.store(self.key.clone());
				}
			}
		} else {
			if self.drain {
				self.meta.first_value_offset.saturating_inc();
				self.meta.total_items.saturating_dec();
				self.meta.store(self.key.clone());
			}
		}
		Some(value)
	}
}

impl<Prefix, Key, KArg, Value, HeapSize, MaxPages>
	frame_support::storage::StorageKeyedList<KArg, Value>
	for StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	type Iterator = StoragePagedNMapIterator<Prefix, Key, KArg, Value, HeapSize, MaxPages>;
	type Appender = StoragePagedNMapAppender<Prefix, Key, KArg, Value, HeapSize, MaxPages>;

	fn len(key: KArg) -> u64 {
		Self::meta(key).total_items
	}

	fn iter(key: KArg) -> Self::Iterator {
		StoragePagedNMapIterator::from_meta(Self::meta(key.clone()), key, false)
	}

	fn drain(key: KArg) -> Self::Iterator {
		StoragePagedNMapIterator::from_meta(Self::meta(key.clone()), key, true)
	}

	fn appender(key: KArg) -> Self::Appender {
		Self::appender(key)
	}
}

impl<Prefix, Key, Value, HeapSize, MaxPages>
	StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Key: KeyGenerator,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	/// Return the metadata of the map.
	#[cfg(feature = "std")]
	pub fn meta<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone>(
		key: KArg,
	) -> StoragePagedNMapMeta<Prefix, Key, KArg, Value, HeapSize, MaxPages> {
		// Use default here to not require a setup migration.
		StoragePagedNMapMeta::from_storage(key).unwrap_or_default()
	}

	/// Provides a fast append iterator.
	///
	/// The list should not be modified while appending. Also don't call it recursively.
	fn appender<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone>(
		key: KArg,
	) -> StoragePagedNMapAppender<Prefix, Key, KArg, Value, HeapSize, MaxPages> {
		StoragePagedNMapAppender { meta: Self::meta(key.clone()), key }
	}

	/// Return the elements of the list.
	#[cfg(feature = "std")]
	pub fn as_vec<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone>(
		key: KArg,
	) -> Vec<Value> {
		<Self as frame_support::storage::StorageKeyedList<_, _>>::iter(key).collect()
	}

	/// Return and remove the elements of the list.
	#[cfg(feature = "std")]
	pub fn as_drained_vec<KArg: EncodeLikeTuple<Key::KArg> + TupleToEncodedIter + Clone>(
		key: KArg,
	) -> Vec<Value> {
		<Self as frame_support::storage::StorageKeyedList<_, _>>::drain(key).collect()
	}
}

/// Provides the final prefix for a [`StoragePagedNMap`].
///
/// It solely exists so that when re-using it from the iterator and meta struct, none of the un-used
/// generics bleed through. Otherwise when only having the `StoragePrefixedContainer` implementation
/// on the list directly, the iterator and metadata need to muster *all* generics, even the ones
/// that are completely useless for prefix calculation.
pub(crate) struct StoragePagedNMapPrefix<Prefix>(PhantomData<Prefix>);

impl<Prefix> frame_support::storage::StoragePrefixedContainer for StoragePagedNMapPrefix<Prefix>
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

impl<Prefix, Key, Value, HeapSize, MaxPages> frame_support::storage::StoragePrefixedContainer
	for StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	fn module_prefix() -> &'static [u8] {
		StoragePagedNMapPrefix::<Prefix>::module_prefix()
	}

	fn storage_prefix() -> &'static [u8] {
		StoragePagedNMapPrefix::<Prefix>::storage_prefix()
	}
}

// Needed for FRAME
impl<Prefix, Key, Value, HeapSize, MaxPages> crate::traits::StorageInfoTrait
	for StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec + codec::MaxEncodedLen,
	HeapSize: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	fn storage_info() -> Vec<StorageInfo> {
		vec![StorageInfo {
			pallet_name: Self::module_prefix().to_vec(),
			storage_name: Self::storage_prefix().to_vec(),
			prefix: Self::final_prefix().to_vec(),
			max_values: MaxPages::get(),
			max_size: Some(HeapSize::get()),
		}]
	}
}

// Needed for FRAME
impl<Prefix, Key, Value, HeapSize, MaxPages> StorageEntryMetadataBuilder
	for StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec + scale_info::StaticTypeInfo,
{
	fn build_metadata(docs: Vec<&'static str>, entries: &mut Vec<StorageEntryMetadataIR>) {
		let docs = if cfg!(feature = "no-metadata-docs") { vec![] } else { docs };

		let entry = StorageEntryMetadataIR {
			name: Prefix::STORAGE_PREFIX,
			modifier: crate::storage::types::StorageEntryModifierIR::Optional, // FAIL-CI
			ty: StorageEntryTypeIR::Map {
				hashers: vec![crate::Twox64Concat::METADATA],
				key: scale_info::meta_type::<u32>(),
				value: scale_info::meta_type::<Vec<Value>>(),
			},
			default: vec![], // FAIL-CI
			docs,
		};

		entries.push(entry);
	}
}

// Needed for FRAME
/*impl<Prefix, Key, Value, HeapSize, MaxPages> Get<u32>
	for KeyLenOf<StoragePagedNMap<Prefix, Key, Value, HeapSize, MaxPages>>
where
	Prefix: StorageInstance,
	HeapSize: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	fn get() -> u32 {
		page_key::<Prefix>(&None, u32::MAX).len() as u32
	}
}*/

/// Prelude for (doc)tests.
#[cfg(feature = "std")]
#[allow(dead_code)]
pub(crate) mod mock {
	pub use super::*;
	pub use crate::{
		pallet_prelude::{ConstU32, NMapKey},
		storage::StorageKeyedList,
	};
	use codec::Compact;
	pub use frame_support::{
		metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
		parameter_types,
		storage::{types::ValueQuery, StorageList as _},
		Blake2_128Concat, StorageNoopGuard,
	};
	pub use sp_io::{hashing::twox_128, TestExternalities};

	parameter_types! {
		pub const HeapSize: u32 = 20;
		pub const MaxPages: Option<u32> = Some(20);
	}

	pub struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"FinalKeysNone"
		}
		const STORAGE_PREFIX: &'static str = "PagedMap";
	}
	pub struct Prefix2;
	impl StorageInstance for Prefix2 {
		fn pallet_prefix() -> &'static str {
			"FinalKeysNone"
		}
		const STORAGE_PREFIX: &'static str = "PagedMap2";
	}

	pub type NMap = StoragePagedNMap<Prefix, KeyGen, u32, HeapSize>;
	pub type KeyGen = (NMapKey<Blake2_128Concat, u32>,);
	pub type Key = (u32,);

	pub type NMapCompact =
		StoragePagedNMap<Prefix2, (NMapKey<Blake2_128Concat, u32>,), Compact<u32>, HeapSize>;
}

#[cfg(test)]
mod tests {
	use super::mock::*;

	#[test]
	fn append_works() {
		TestExternalities::default().execute_with(|| {
			<NMap as StorageKeyedList<_, _>>::append_many((123,), 0..1000);
			assert_eq!(NMap::as_vec((123,)), (0..1000).collect::<Vec<_>>());
		});
	}

	/// Draining all works.
	#[test]
	fn simple_drain_works() {
		TestExternalities::default().execute_with(|| {
			let _g = StorageNoopGuard::default(); // All in all a No-Op
			NMap::append_many((123,), 0..1000);

			assert_eq!(NMap::as_drained_vec((123,)), (0..1000).collect::<Vec<_>>());

			assert_eq!(NMap::meta((123,)), Default::default());

			// all gone
			assert_eq!(NMap::as_vec((123,)), Vec::<u32>::new());
			// Need to delete the metadata manually.
			StoragePagedNMapMeta::<Prefix, (
				NMapKey<Blake2_128Concat, u32>,), (u32,), u32, (), ()>::delete((123,));
		});
	}

	/// Drain half of the elements and iterator the rest.
	#[test]
	fn partial_drain_works() {
		TestExternalities::default().execute_with(|| {
			NMap::append_many((123,), 0..100);

			let vals = NMap::drain((123,)).take(50).collect::<Vec<_>>();
			assert_eq!(vals, (0..50).collect::<Vec<_>>());

			let meta = NMap::meta((123,));
			// Will switch over to `10/0`, but will in the next call.
			assert_eq!((meta.first_page, meta.first_value_offset), (10, 0));
			assert_eq!(NMap::len((123,)), 50);

			// 50 gone, 50 to go
			assert_eq!(NMap::as_vec((123,)), (50..100).collect::<Vec<_>>());
		});
	}

	/// Draining, appending and iterating work together.
	#[test]
	fn drain_append_iter_works() {
		TestExternalities::default().execute_with(|| {
			for r in 1..=100 {
				NMap::append_many((123,), 0..12);
				NMap::append_many((123,), 0..12);

				let dropped = NMap::drain((123,)).take(12).collect::<Vec<_>>();
				assert_eq!(dropped, (0..12).collect::<Vec<_>>());

				assert_eq!(NMap::as_vec((123,)), (0..12).cycle().take(r * 12).collect::<Vec<_>>());
				assert_eq!(NMap::len((123,)) as usize, r * 12);
			}
		});
	}

	/// Pages are removed ASAP.
	#[test]
	fn drain_eager_page_removal() {
		TestExternalities::default().execute_with(|| {
			NMap::append_many((123,), 0..9);

			assert!(sp_io::storage::exists(&page_key::<Prefix, KeyGen, Key>((123,), 0)));
			assert!(sp_io::storage::exists(&page_key::<Prefix, KeyGen, Key>((123,), 1)));

			assert_eq!(NMap::drain((123,)).take(5).count(), 5);
			// Page 0 is eagerly removed.
			assert!(!sp_io::storage::exists(&page_key::<Prefix, KeyGen, Key>((123,), 0)));
			assert!(sp_io::storage::exists(&page_key::<Prefix, KeyGen, Key>((123,), 1)));
		});
	}

	/// Appending encodes pages as `Vec`.
	#[test]
	fn append_storage_layout() {
		TestExternalities::default().execute_with(|| {
			NMap::append_many((123,), 0..9);

			let key = page_key::<Prefix, KeyGen, Key>((123,), 0);
			let raw = sp_io::storage::get(&key).expect("Page should be present");
			let as_vec = Vec::<u32>::decode(&mut &raw[..]).unwrap();
			assert_eq!(as_vec.len(), 5, "First page contains 5");

			let key = page_key::<Prefix, KeyGen, Key>((123,), 1);
			let raw = sp_io::storage::get(&key).expect("Page should be present");
			let as_vec = Vec::<u32>::decode(&mut &raw[..]).unwrap();
			assert_eq!(as_vec.len(), 4, "Second page contains 4");

			let meta = sp_io::storage::get(&meta_key::<Prefix, KeyGen, Key>((123,)))
				.expect("Meta should be present");
			let meta: StoragePagedNMapMeta<Prefix, KeyGen, Key, (), ()> =
				Decode::decode(&mut &meta[..]).unwrap();
			assert_eq!(meta.first_page, 0);
			assert_eq!(meta.first_value_offset, 0);
			assert_eq!(meta.last_page, 1);
			assert_eq!(meta.last_page_byte_offset, 16);

			let page = Page::<KeyGen, Key, u32>::from_storage::<Prefix>((123,), 0, 0).unwrap();
			assert_eq!(page.index, 0);
			assert_eq!(page.values.count(), 5);

			let page = Page::<KeyGen, Key, u32>::from_storage::<Prefix>((123,), 1, 0).unwrap();
			assert_eq!(page.index, 1);
			assert_eq!(page.values.count(), 4);
		});
	}

	#[test]
	fn final_prefix_correct() {
		let got = StoragePagedNMapPrefix::<Prefix>::final_prefix();
		let want = [twox_128(b"FinalKeysNone"), twox_128(b"PagedMap")].concat();

		assert_eq!(want, got);
	}

	#[test]
	fn page_key_correct() {
		let got = page_key::<Prefix, KeyGen, Key>((123,), 11);
		let pallet_prefix = StoragePagedNMapPrefix::<Prefix>::final_prefix();
		let hashed_key = Blake2_128Concat::hash(&123u32.encode());
		let want = [&pallet_prefix[..], &hashed_key, b"page", 11u32.encode().as_slice()].concat();

		assert_eq!(want.len(), 32 + (16 + 4) + 4 + 4);
		assert!(want.starts_with(&pallet_prefix[..]));
		assert_eq!(got, want);
	}

	#[test]
	fn meta_key_correct() {
		let got = meta_key::<Prefix, KeyGen, Key>((123,));
		let pallet_prefix = StoragePagedNMapPrefix::<Prefix>::final_prefix();
		let hashed_key = Blake2_128Concat::hash(&123u32.encode());
		let want = [&pallet_prefix[..], hashed_key.as_slice(), b"meta"].concat();

		assert_eq!(want.len(), 32 + (16 + 4) + 4);
		assert!(want.starts_with(&pallet_prefix[..]));
		assert_eq!(got.len(), want.len());
		assert_eq!(got, want);
	}

	#[test]
	fn peekable_drain_also_deletes() {
		TestExternalities::default().execute_with(|| {
			NMap::append_many((123,), 0..10);

			let mut iter = NMap::drain((123,)).peekable();
			assert_eq!(iter.peek(), Some(&0));
			// `peek` does remove one element...
			assert_eq!(NMap::iter((123,)).count(), 9);
		});
	}

	#[test]
	fn heap_size_works() {
		use codec::Compact;
		TestExternalities::default().execute_with(|| {
			NMap::append_many((123,), 0..100);
			// FAIL-CI add more prefix
			NMapCompact::append_many((123,), (0..100).map(|i| Compact(i)));

			// They should have the same number of items:
			assert_eq!(NMap::meta((123,)).total_items, NMapCompact::meta((123,)).total_items); // FAIL-CI check tracking
			assert_eq!(NMap::meta((123,)).total_items, 100);
			// But the compact variant should have more values per page:
		});
	}
}
