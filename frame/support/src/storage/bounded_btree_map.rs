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
pub use sp_runtime::BoundedBTreeMap;
use sp_std::collections::btree_map::BTreeMap;

impl<K, V, S> StorageDecodeLength for BoundedBTreeMap<K, V, S> {}

impl<I, K, V, Bound> TryCollect<BoundedBTreeMap<K, V, Bound>> for I
where
	K: Ord,
	I: ExactSizeIterator + Iterator<Item = (K, V)>,
	Bound: Get<u32>,
{
	type Error = &'static str;

	fn try_collect(self) -> Result<BoundedBTreeMap<K, V, Bound>, Self::Error> {
		if self.len() > Bound::get() as usize {
			Err("iterator length too big")
		} else {
			Ok(BoundedBTreeMap::<K, V, Bound>::try_from(self.collect::<BTreeMap<K, V>>())
				.expect("length checked above; qed"))
		}
	}
}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::Twox128;
	use frame_support::traits::ConstU32;
	use sp_io::TestExternalities;

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

	#[test]
	fn can_be_collected() {
		let b1 = boundedmap_from_keys::<u32, ConstU32<5>>(&[1, 2, 3, 4]);
		let b2: BoundedBTreeMap<u32, (), ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can also be collected into a collection of length 4.
		let b2: BoundedBTreeMap<u32, (), ConstU32<4>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can be mutated further into iterators that are `ExactSizedIterator`.
		let b2: BoundedBTreeMap<u32, (), ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).rev().skip(2).try_collect().unwrap();
		// note that the binary tree will re-sort this, so rev() is not really seen
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3]);

		let b2: BoundedBTreeMap<u32, (), ConstU32<5>> =
			b1.iter().map(|(k, v)| (k + 1, *v)).take(2).try_collect().unwrap();
		assert_eq!(b2.into_iter().map(|(k, _)| k).collect::<Vec<_>>(), vec![2, 3]);

		// but these worn't work
		let b2: Result<BoundedBTreeMap<u32, (), ConstU32<3>>, _> =
			b1.iter().map(|(k, v)| (k + 1, *v)).try_collect();
		assert!(b2.is_err());

		let b2: Result<BoundedBTreeMap<u32, (), ConstU32<1>>, _> =
			b1.iter().map(|(k, v)| (k + 1, *v)).skip(2).try_collect();
		assert!(b2.is_err());
	}

	#[test]
	fn eq_works() {
		// of same type
		let b1 = boundedmap_from_keys::<u32, ConstU32<7>>(&[1, 2]);
		let b2 = boundedmap_from_keys::<u32, ConstU32<7>>(&[1, 2]);
		assert_eq!(b1, b2);

		// of different type, but same value and bound.
		crate::parameter_types! {
			B1: u32 = 7;
			B2: u32 = 7;
		}
		let b1 = boundedmap_from_keys::<u32, B1>(&[1, 2]);
		let b2 = boundedmap_from_keys::<u32, B2>(&[1, 2]);
		assert_eq!(b1, b2);
	}
}
