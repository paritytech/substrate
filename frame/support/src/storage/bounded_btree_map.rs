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

use crate::storage::StorageDecodeLength;
pub use sp_runtime::BoundedBTreeMap;

impl<K, V, S> StorageDecodeLength for BoundedBTreeMap<K, V, S> {}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::Twox128;
	use frame_support::traits::{ConstU32, Get};
	use sp_io::TestExternalities;
	use sp_std::collections::btree_map::BTreeMap;

	#[crate::storage_alias]
	type Foo = StorageValue<Prefix, BoundedBTreeMap<u32, (), ConstU32<7>>>;

	#[crate::storage_alias]
	type FooMap = StorageMap<Prefix, Twox128, u32, BoundedBTreeMap<u32, (), ConstU32<7>>>;

	#[crate::storage_alias]
	type FooDoubleMap =
		StorageDoubleMap<Prefix, Twox128, u32, Twox128, u32, BoundedBTreeMap<u32, (), ConstU32<7>>>;

	fn map_from_keys<K>(keys: &[K]) -> BTreeMap<K, ()>
	where
		K: Ord + Copy,
	{
		keys.iter().copied().zip(std::iter::repeat(())).collect()
	}

	fn boundedmap_from_keys<K, S>(keys: &[K]) -> BoundedBTreeMap<K, (), S>
	where
		K: Ord + Copy,
		S: Get<u32>,
	{
		map_from_keys(keys).try_into().unwrap()
	}

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedmap_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}
}
