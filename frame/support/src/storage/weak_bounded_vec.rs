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

//! Traits, types and structs to support putting a bounded vector into storage, as a raw value, map
//! or a double map.

use crate::{
	storage::{StorageDecodeLength, StorageTryAppend},
	traits::Get,
};
pub use sp_runtime::WeakBoundedVec;

impl<T, S> StorageDecodeLength for WeakBoundedVec<T, S> {}

impl<T, S: Get<u32>> StorageTryAppend<T> for WeakBoundedVec<T, S> {
	fn bound() -> usize {
		S::get() as usize
	}
}

#[cfg(test)]
pub mod test {
	use super::*;
	use crate::Twox128;
	use frame_support::traits::ConstU32;
	use sp_io::TestExternalities;

	#[crate::storage_alias]
	type Foo = StorageValue<Prefix, WeakBoundedVec<u32, ConstU32<7>>>;
	#[crate::storage_alias]
	type FooMap = StorageMap<Prefix, Twox128, u32, WeakBoundedVec<u32, ConstU32<7>>>;
	#[crate::storage_alias]
	type FooDoubleMap =
		StorageDoubleMap<Prefix, Twox128, u32, Twox128, u32, WeakBoundedVec<u32, ConstU32<7>>>;

	#[test]
	fn decode_len_works() {
		TestExternalities::default().execute_with(|| {
			let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3].try_into().unwrap();
			Foo::put(bounded);
			assert_eq!(Foo::decode_len().unwrap(), 3);
		});

		TestExternalities::default().execute_with(|| {
			let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3].try_into().unwrap();
			FooMap::insert(1, bounded);
			assert_eq!(FooMap::decode_len(1).unwrap(), 3);
			assert!(FooMap::decode_len(0).is_none());
			assert!(FooMap::decode_len(2).is_none());
		});

		TestExternalities::default().execute_with(|| {
			let bounded: WeakBoundedVec<u32, ConstU32<7>> = vec![1, 2, 3].try_into().unwrap();
			FooDoubleMap::insert(1, 1, bounded);
			assert_eq!(FooDoubleMap::decode_len(1, 1).unwrap(), 3);
			assert!(FooDoubleMap::decode_len(2, 1).is_none());
			assert!(FooDoubleMap::decode_len(1, 2).is_none());
			assert!(FooDoubleMap::decode_len(2, 2).is_none());
		});
	}
}
