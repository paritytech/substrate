// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

use frame_support::storage::unhashed;
use codec::Encode;
use frame_support::{StorageDoubleMap, StorageMap, StorageValue, StoragePrefixedMap};
use sp_io::{TestExternalities, hashing::{twox_64, twox_128, blake2_128}};

mod no_instance {
	use codec::{Encode, Decode, EncodeLike};

	pub trait Trait {
		type Origin;
		type BlockNumber: Encode + Decode + EncodeLike + Default + Clone;
	}

	frame_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=self {}
	}

	frame_support::decl_storage!{
		trait Store for Module<T: Trait> as FinalKeysNone {
			pub Value config(value): u32;

			pub Map: map hasher(blake2_128_concat) u32 => u32;
			pub Map2: map hasher(twox_64_concat) u32 => u32;

			pub DoubleMap: double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) u32 => u32;
			pub DoubleMap2: double_map hasher(twox_64_concat) u32, hasher(twox_64_concat) u32 => u32;

			pub TestGenericValue get(fn test_generic_value) config(): Option<T::BlockNumber>;
			pub TestGenericDoubleMap get(fn foo2) config(test_generic_double_map):
				double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) T::BlockNumber => Option<u32>;
		}
	}
}

mod instance {
	use super::no_instance;

	pub trait Trait<I = DefaultInstance>: super::no_instance::Trait {}

	frame_support::decl_module! {
		pub struct Module<T: Trait<I>, I: Instance = DefaultInstance>
			for enum Call where origin: T::Origin, system=no_instance {}
	}

	frame_support::decl_storage!{
		trait Store for Module<T: Trait<I>, I: Instance = DefaultInstance>
			as FinalKeysSome
		{
			pub Value config(value): u32;

			pub Map: map hasher(blake2_128_concat) u32 => u32;
			pub Map2: map hasher(twox_64_concat) u32 => u32;

			pub DoubleMap: double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) u32 => u32;
			pub DoubleMap2: double_map hasher(twox_64_concat) u32, hasher(twox_64_concat) u32 => u32;

			pub TestGenericValue get(fn test_generic_value) config(): Option<T::BlockNumber>;
			pub TestGenericDoubleMap get(fn foo2) config(test_generic_double_map):
				double_map hasher(blake2_128_concat) u32, hasher(blake2_128_concat) T::BlockNumber => Option<u32>;
		}
		add_extra_genesis {
			// See `decl_storage` limitation.
			config(phantom): core::marker::PhantomData<I>;
		}
	}
}

fn twox_64_concat(d: &[u8]) -> Vec<u8> {
	let mut v = twox_64(d).to_vec();
	v.extend_from_slice(d);
	v
}

fn blake2_128_concat(d: &[u8]) -> Vec<u8> {
	let mut v = blake2_128(d).to_vec();
	v.extend_from_slice(d);
	v
}

#[test]
fn final_keys_no_instance() {
	TestExternalities::default().execute_with(|| {
		no_instance::Value::put(1);
		let k = [twox_128(b"FinalKeysNone"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		no_instance::Map::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<no_instance::Map>::final_prefix());

		no_instance::Map2::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<no_instance::Map2>::final_prefix());

		no_instance::DoubleMap::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<no_instance::DoubleMap>::final_prefix());

		no_instance::DoubleMap2::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<no_instance::DoubleMap2>::final_prefix());
	});
}

#[test]
fn final_keys_default_instance() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<instance::DefaultInstance>>::put(1);
		let k = [twox_128(b"FinalKeysSome"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<instance::Map<instance::DefaultInstance>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map<instance::DefaultInstance>>::final_prefix());

		<instance::Map2<instance::DefaultInstance>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map2<instance::DefaultInstance>>::final_prefix());

		<instance::DoubleMap<instance::DefaultInstance>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap<instance::DefaultInstance>>::final_prefix());

		<instance::DoubleMap2<instance::DefaultInstance>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap2<instance::DefaultInstance>>::final_prefix());
	});
}

#[test]
fn final_keys_instance_2() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<instance::Instance2>>::put(1);
		let k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<instance::Map<instance::Instance2>>::insert(1, 2);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map<instance::Instance2>>::final_prefix());

		<instance::Map2<instance::Instance2>>::insert(1, 2);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map2<instance::Instance2>>::final_prefix());

		<instance::DoubleMap<instance::Instance2>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap<instance::Instance2>>::final_prefix());

		<instance::DoubleMap2<instance::Instance2>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap2<instance::Instance2>>::final_prefix());
	});
}
