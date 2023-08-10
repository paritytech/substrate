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

use super::{
	key::KeyGenerator,
	paged_nmap::{StoragePagedNMap, StoragePagedNMapAppender, StoragePagedNMapIterator},
};
#[cfg(feature = "std")]
use crate::storage::types::paged_nmap::StoragePagedNMapMeta;
use crate::{
	hash::StorageHasher,
	metadata_ir::{StorageEntryMetadataIR, StorageEntryTypeIR},
	storage::{
		lists::*, types::paged_nmap::StoragePagedNMapPrefix, EncodeLikeTuple, KeyLenOf,
		StorageEntryMetadataBuilder, StoragePrefixedContainer, TupleToEncodedIter,
	},
	traits::{StorageInfo, StorageInstance},
	DefaultNoBound,
};
use codec::{EncodeLike, FullCodec};
use core::marker::PhantomData;
use frame_support::traits::Get;
use sp_std::prelude::*;

/// A list in storage that stores items in a paged manner.
#[derive(DefaultNoBound)]
pub struct StoragePagedList<Prefix, Value, HeapSize, MaxPages = ()> {
	/// Phantom data.
	pub _phantom: PhantomData<(Prefix, Value, HeapSize, MaxPages)>,
}

/// The metadata of a [`StoragePagedList`].
pub type StoragePagedListMeta<Prefix, Value, HeapSize, MaxPages = ()> =
	StoragePagedNMapMeta<Prefix, EmptyKeyGen, EmptyKey, Value, HeapSize, MaxPages>;

/// Iterator type to inspect elements of a [`StoragePagedList`].
pub struct StoragePagedListIterator<Prefix, Value, HeapSize, MaxPages = ()> {
	inner: StoragePagedNMapIterator<Prefix, EmptyKeyGen, EmptyKey, Value, HeapSize, MaxPages>,
}

/// Iterator type to append elements to a [`StoragePagedList`].
pub struct StoragePagedListAppender<Prefix, Value, HeapSize, MaxPages = ()> {
	inner: StoragePagedNMapAppender<Prefix, EmptyKeyGen, EmptyKey, Value, HeapSize, MaxPages>,
}

/// An implementation of [`KeyGenerator`] that uses `()` as key type and does nothing.
pub struct EmptyKeyGen;

/// The key type of [`EmptyKeyGen`].
pub type EmptyKey = ((),);

impl KeyGenerator for EmptyKeyGen {
	type Key = ();
	type KArg = EmptyKey;
	type HashFn = Box<dyn FnOnce(&[u8]) -> Vec<u8>>;
	type HArg = ();

	const HASHER_METADATA: &'static [crate::metadata_ir::StorageHasherIR] = &[];

	fn final_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(_key: KArg) -> Vec<u8> {
		Vec::new()
	}

	fn migrate_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(
		_key: &KArg,
		_hash_fns: Self::HArg,
	) -> Vec<u8> {
		Vec::new()
	}
}

impl<Prefix, Value, HeapSize, MaxPages> StorageList<Value>
	for StoragePagedList<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	type Iterator = StoragePagedListIterator<Prefix, Value, HeapSize, MaxPages>;
	type Appender = StoragePagedListAppender<Prefix, Value, HeapSize, MaxPages>;

	fn len() -> u64 {
		<StoragePagedNMap<Prefix, EmptyKeyGen, Value, HeapSize, MaxPages> as StorageKeyedList<
			((),),
			Value,
		>>::len(((),))
	}

	fn iter() -> Self::Iterator {
		StoragePagedListIterator { inner: <StoragePagedNMap<Prefix, EmptyKeyGen, Value, HeapSize, MaxPages> as StorageKeyedList<EmptyKey, Value>>::iter(((),)) }
	}

	fn drain() -> Self::Iterator {
		StoragePagedListIterator { inner: <StoragePagedNMap<Prefix, EmptyKeyGen, Value, HeapSize, MaxPages> as StorageKeyedList<EmptyKey, Value>>::drain(((),)) }
	}

	fn appender() -> Self::Appender {
		StoragePagedListAppender { inner: <StoragePagedNMap<Prefix, EmptyKeyGen, Value, HeapSize, MaxPages> as StorageKeyedList<EmptyKey, Value>>::appender(((),)) }
	}
}

impl<Prefix, Value, HeapSize, MaxPages> Iterator
	for StoragePagedListIterator<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	type Item = Value;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<Prefix, Value, HeapSize, MaxPages> StorageListAppender<Value>
	for StoragePagedListAppender<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	fn append<EncodeLikeValue>(&mut self, item: EncodeLikeValue)
	where
		EncodeLikeValue: EncodeLike<Value>,
	{
		self.inner.append(item)
	}
}

// Needed for FRAME
impl<Prefix, Value, HeapSize, MaxPages> crate::traits::StorageInfoTrait
	for StoragePagedList<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
	MaxPages: Get<Option<u32>>,
{
	fn storage_info() -> Vec<StorageInfo> {
		vec![StorageInfo {
			pallet_name: <Self as StoragePrefixedContainer>::module_prefix().to_vec(),
			storage_name: Self::storage_prefix().to_vec(),
			prefix: Self::final_prefix().to_vec(),
			max_values: MaxPages::get(),
			max_size: Some(HeapSize::get()),
		}]
	}
}

// Needed for FRAME
impl<Prefix, Value, HeapSize, MaxPages> StoragePrefixedContainer
	for StoragePagedList<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	fn module_prefix() -> &'static [u8] {
		// There is no difference between the prefices of a List and NMap.
		StoragePagedNMapPrefix::<Prefix>::module_prefix()
	}

	fn storage_prefix() -> &'static [u8] {
		StoragePagedNMapPrefix::<Prefix>::storage_prefix()
	}
}

// Needed for FRAME
impl<Prefix, Value, HeapSize, MaxPages> StorageEntryMetadataBuilder
	for StoragePagedList<Prefix, Value, HeapSize, MaxPages>
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
impl<Prefix, Value, HeapSize, MaxPages> Get<u32>
	for KeyLenOf<StoragePagedList<Prefix, Value, HeapSize, MaxPages>>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	fn get() -> u32 {
		super::paged_nmap::page_key::<Prefix, EmptyKeyGen, EmptyKey>(((),), u32::MAX).len() as u32
	}
}

// Test helpers:
#[cfg(feature = "std")]
#[allow(dead_code)]
impl<Prefix, Value, HeapSize, MaxPages> StoragePagedList<Prefix, Value, HeapSize, MaxPages>
where
	Prefix: StorageInstance,
	Value: FullCodec,
	HeapSize: Get<u32>,
{
	/// Return the metadata struct of this list.
	pub fn meta() -> StoragePagedNMapMeta<Prefix, EmptyKeyGen, ((),), Value, HeapSize, MaxPages> {
		// Use default here to not require a setup migration.
		StoragePagedNMap::<Prefix, EmptyKeyGen, Value, HeapSize, MaxPages>::meta(((),))
	}

	/// Return the elements of the list.
	pub fn as_vec() -> Vec<Value> {
		<Self as frame_support::storage::StorageList<_>>::iter().collect()
	}

	/// Return and remove the elements of the list.
	pub fn as_drained_vec() -> Vec<Value> {
		<Self as frame_support::storage::StorageList<_>>::drain().collect()
	}
}

/// Prelude for (doc)tests.
#[cfg(feature = "std")]
#[allow(dead_code)]
pub(crate) mod mock {
	pub use super::*;
	pub use crate::storage::{types::paged_nmap::*, StoragePrefixedContainer};
	pub use codec::{Compact, Decode, Encode};
	pub use frame_support::{
		metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
		parameter_types,
		storage::{types::ValueQuery, StorageList as _},
		StorageNoopGuard,
	};
	pub use sp_io::{hashing::twox_128, TestExternalities};

	pub fn page_key<Prefix: StorageInstance>(page: PageIndex) -> Vec<u8> {
		crate::storage::types::paged_nmap::page_key::<Prefix, EmptyKeyGen, ((),)>(((),), page)
	}

	pub fn meta_key<Prefix: StorageInstance>() -> Vec<u8> {
		crate::storage::types::paged_nmap::meta_key::<Prefix, EmptyKeyGen, ((),)>(((),))
	}

	parameter_types! {
		pub const HeapSize: u32 = 20;
		pub const MaxPages: Option<u32> = Some(20);
	}

	pub struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"FinalKeysNone"
		}
		const STORAGE_PREFIX: &'static str = "PagedList";
	}
	pub struct Prefix2;
	impl StorageInstance for Prefix2 {
		fn pallet_prefix() -> &'static str {
			"FinalKeysNone"
		}
		const STORAGE_PREFIX: &'static str = "PagedList";
	}

	pub type List = StoragePagedList<Prefix, u32, HeapSize>;
	pub type KeyGen = EmptyKeyGen;
	pub type Key = ((),);
	pub type ListCompact = StoragePagedList<Prefix2, Compact<u32>, HeapSize>;
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

			assert_eq!(List::meta(), Default::default());

			// all gone
			assert_eq!(List::as_vec(), Vec::<u32>::new());
			// Need to delete the metadata manually.
			StoragePagedNMapMeta::<Prefix, KeyGen, Key, u32, (), ()>::delete(((),));
		});
	}

	/// Drain half of the elements and iterator the rest.
	#[test]
	fn partial_drain_works() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..100);

			let vals = List::drain().take(50).collect::<Vec<_>>();
			assert_eq!(vals, (0..50).collect::<Vec<_>>());

			let meta = List::meta();
			// Will switch over to `10/0`, but will in the next call.
			assert_eq!((meta.first_page, meta.first_value_offset), (10, 0));
			assert_eq!(List::len(), 50);

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
				assert_eq!(List::len() as usize, r * 12);
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
			let meta: StoragePagedNMapMeta<Prefix, EmptyKeyGen, (), u32, (), ()> =
				codec::Decode::decode(&mut &meta[..]).unwrap();
			assert_eq!(meta.first_page, 0);
			assert_eq!(meta.first_value_offset, 0);
			assert_eq!(meta.last_page, 1);
			assert_eq!(meta.last_page_byte_offset, 16);

			let page = Page::<KeyGen, Key, u32>::from_storage::<Prefix>(((),), 0, 0).unwrap();
			assert_eq!(page.index, 0);
			assert_eq!(page.values.count(), 5);

			let page = Page::<KeyGen, Key, u32>::from_storage::<Prefix>(((),), 1, 0).unwrap();
			assert_eq!(page.index, 1);
			assert_eq!(page.values.count(), 4);
		});
	}

	#[test]
	fn final_prefix_correct() {
		let got = StoragePagedNMapPrefix::<Prefix>::final_prefix();
		let want = [twox_128(b"FinalKeysNone"), twox_128(b"PagedList")].concat();

		assert_eq!(want, got);
	}

	#[test]
	fn page_key_correct() {
		let got = page_key::<Prefix>(0);
		let pallet_prefix = StoragePagedNMapPrefix::<Prefix>::final_prefix();
		let want = (pallet_prefix, b"page", 0u32).encode();

		assert_eq!(want.len(), 32 + 4 + 4);
		assert!(want.starts_with(&pallet_prefix[..]));
		assert_eq!(got, want);
	}

	#[test]
	fn meta_key_correct() {
		let got = meta_key::<Prefix>();
		let pallet_prefix = StoragePagedNMapPrefix::<Prefix>::final_prefix();
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

	#[test]
	fn heap_size_works() {
		TestExternalities::default().execute_with(|| {
			List::append_many(0..100);
			ListCompact::append_many((0..100).map(|i| Compact(i)));

			// They should have the same number of items:
			assert_eq!(List::meta().total_items, ListCompact::meta().total_items);
			// But the compact variant should have more values per page:
		});
	}
}
