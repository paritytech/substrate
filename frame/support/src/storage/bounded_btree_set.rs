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

//! Traits, types and structs to support a bounded `BTreeSet`.

use crate::{
	storage::StorageDecodeLength,
	traits::{Get, TryCollect},
};
pub use sp_runtime::BoundedBTreeSet;
use sp_std::collections::btree_set::BTreeSet;

impl<T, S> StorageDecodeLength for BoundedBTreeSet<T, S> {}

impl<I, T, Bound> TryCollect<BoundedBTreeSet<T, Bound>> for I
where
	T: Ord,
	I: ExactSizeIterator + Iterator<Item = T>,
	Bound: Get<u32>,
{
	type Error = &'static str;

	fn try_collect(self) -> Result<BoundedBTreeSet<T, Bound>, Self::Error> {
		if self.len() > Bound::get() as usize {
			Err("iterator length too big")
		} else {
			Ok(BoundedBTreeSet::<T, Bound>::try_from(self.collect::<BTreeSet<T>>())
				.expect("length is checked above; qed"))
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
	type Foo = StorageValue<Prefix, BoundedBTreeSet<u32, ConstU32<7>>>;

	#[crate::storage_alias]
	type FooMap = StorageMap<Prefix, Twox128, u32, BoundedBTreeSet<u32, ConstU32<7>>>;

	#[crate::storage_alias]
	type FooDoubleMap =
		StorageDoubleMap<Prefix, Twox128, u32, Twox128, u32, BoundedBTreeSet<u32, ConstU32<7>>>;

	fn set_from_keys<T>(keys: &[T]) -> BTreeSet<T>
	where
		T: Ord + Copy,
	{
		keys.iter().copied().collect()
	}

	fn boundedset_from_keys<T, S>(keys: &[T]) -> BoundedBTreeSet<T, S>
	where
		T: Ord + Copy,
		S: Get<u32>,
	{
		set_from_keys(keys).try_into().unwrap()
	}

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded = boundedset_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedset_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded = boundedset_from_keys::<u32, ConstU32<7>>(&[1, 2, 3]);
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}

	#[test]
	fn can_be_collected() {
		let b1 = boundedset_from_keys::<u32, ConstU32<5>>(&[1, 2, 3, 4]);
		let b2: BoundedBTreeSet<u32, ConstU32<5>> = b1.iter().map(|k| k + 1).try_collect().unwrap();
		assert_eq!(b2.into_iter().collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can also be collected into a collection of length 4.
		let b2: BoundedBTreeSet<u32, ConstU32<4>> = b1.iter().map(|k| k + 1).try_collect().unwrap();
		assert_eq!(b2.into_iter().collect::<Vec<_>>(), vec![2, 3, 4, 5]);

		// can be mutated further into iterators that are `ExactSizedIterator`.
		let b2: BoundedBTreeSet<u32, ConstU32<5>> =
			b1.iter().map(|k| k + 1).rev().skip(2).try_collect().unwrap();
		// note that the binary tree will re-sort this, so rev() is not really seen
		assert_eq!(b2.into_iter().collect::<Vec<_>>(), vec![2, 3]);

		let b2: BoundedBTreeSet<u32, ConstU32<5>> =
			b1.iter().map(|k| k + 1).take(2).try_collect().unwrap();
		assert_eq!(b2.into_iter().collect::<Vec<_>>(), vec![2, 3]);

		// but these worn't work
		let b2: Result<BoundedBTreeSet<u32, ConstU32<3>>, _> =
			b1.iter().map(|k| k + 1).try_collect();
		assert!(b2.is_err());

		let b2: Result<BoundedBTreeSet<u32, ConstU32<1>>, _> =
			b1.iter().map(|k| k + 1).skip(2).try_collect();
		assert!(b2.is_err());
	}
}
