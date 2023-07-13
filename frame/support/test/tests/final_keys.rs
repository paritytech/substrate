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

use codec::Encode;
use frame_support::{storage::unhashed, StoragePrefixedMap};
use sp_core::sr25519;
use sp_io::{
	hashing::{blake2_128, twox_128, twox_64},
	TestExternalities,
};
use sp_runtime::{
	generic,
	traits::{BlakeTwo256, Verify},
};

#[frame_support::pallet]
mod no_instance {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	#[pallet::storage]
	pub type Value<T> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type Map<T> = StorageMap<_, Blake2_128Concat, u32, u32, ValueQuery>;
	#[pallet::storage]
	pub type Map2<T> = StorageMap<_, Twox64Concat, u32, u32, ValueQuery>;

	#[pallet::storage]
	pub type DoubleMap<T> =
		StorageDoubleMap<_, Blake2_128Concat, u32, Blake2_128Concat, u32, u32, ValueQuery>;
	#[pallet::storage]
	pub type DoubleMap2<T> =
		StorageDoubleMap<_, Twox64Concat, u32, Twox64Concat, u32, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn test_generic_value)]
	pub type TestGenericValue<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;
	#[pallet::storage]
	#[pallet::getter(fn foo2)]
	pub type TestGenericDoubleMap<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		u32,
		Blake2_128Concat,
		T::BlockNumber,
		u32,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub value: u32,
		pub test_generic_value: T::BlockNumber,
		pub test_generic_double_map: Vec<(u32, T::BlockNumber, u32)>,
	}

	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self {
				value: Default::default(),
				test_generic_value: Default::default(),
				test_generic_double_map: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			<Value<T>>::put(self.value);
			<TestGenericValue<T>>::put(&self.test_generic_value);
			for (k1, k2, v) in &self.test_generic_double_map {
				<TestGenericDoubleMap<T>>::insert(k1, k2, v);
			}
		}
	}
}

#[frame_support::pallet]
mod instance {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_support_test as frame_system;

	#[pallet::pallet]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {}

	#[pallet::storage]
	pub type Value<T: Config<I>, I: 'static = ()> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	pub type Map<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, u32, u32, ValueQuery>;
	#[pallet::storage]
	pub type Map2<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, u32, u32, ValueQuery>;

	#[pallet::storage]
	pub type DoubleMap<T: Config<I>, I: 'static = ()> =
		StorageDoubleMap<_, Blake2_128Concat, u32, Blake2_128Concat, u32, u32, ValueQuery>;
	#[pallet::storage]
	pub type DoubleMap2<T: Config<I>, I: 'static = ()> =
		StorageDoubleMap<_, Twox64Concat, u32, Twox64Concat, u32, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn test_generic_value)]
	pub type TestGenericValue<T: Config<I>, I: 'static = ()> =
		StorageValue<_, T::BlockNumber, OptionQuery>;
	#[pallet::storage]
	#[pallet::getter(fn foo2)]
	pub type TestGenericDoubleMap<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		u32,
		Blake2_128Concat,
		T::BlockNumber,
		u32,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub value: u32,
		pub test_generic_value: T::BlockNumber,
		pub test_generic_double_map: Vec<(u32, T::BlockNumber, u32)>,
		pub phantom: PhantomData<I>,
	}

	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self {
				value: Default::default(),
				test_generic_value: Default::default(),
				test_generic_double_map: Default::default(),
				phantom: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> BuildGenesisConfig for GenesisConfig<T, I> {
		fn build(&self) {
			<Value<T, I>>::put(self.value);
			<TestGenericValue<T, I>>::put(&self.test_generic_value);
			for (k1, k2, v) in &self.test_generic_double_map {
				<TestGenericDoubleMap<T, I>>::insert(k1, k2, v);
			}
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

pub type BlockNumber = u32;
pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

frame_support::construct_runtime!(
	pub enum Runtime
	where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_support_test,
		FinalKeysNone: no_instance,
		FinalKeysSome: instance,
		Instance2FinalKeysSome: instance::<Instance2>,
	}
);

impl frame_support_test::Config for Runtime {
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type DbWeight = ();
}

impl no_instance::Config for Runtime {}

impl instance::Config for Runtime {}
impl instance::Config<instance::Instance2> for Runtime {}

#[test]
fn final_keys_no_instance() {
	TestExternalities::default().execute_with(|| {
		<no_instance::Value<Runtime>>::put(1);
		let k = [twox_128(b"FinalKeysNone"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<no_instance::Map<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<no_instance::Map<Runtime>>::final_prefix());

		<no_instance::Map2<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<no_instance::Map2<Runtime>>::final_prefix());

		<no_instance::DoubleMap<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<no_instance::DoubleMap<Runtime>>::final_prefix());

		<no_instance::DoubleMap2<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysNone"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<no_instance::DoubleMap2<Runtime>>::final_prefix());
	});
}

#[test]
fn final_keys_default_instance() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<Runtime>>::put(1);
		let k = [twox_128(b"FinalKeysSome"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<instance::Map<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map<Runtime>>::final_prefix());

		<instance::Map2<Runtime>>::insert(1, 2);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map2<Runtime>>::final_prefix());

		<instance::DoubleMap<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap<Runtime>>::final_prefix());

		<instance::DoubleMap2<Runtime>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"FinalKeysSome"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap2<Runtime>>::final_prefix());
	});
}

#[test]
fn final_keys_instance_2() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<Runtime, instance::Instance2>>::put(1);
		let k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Value")].concat();
		assert_eq!(unhashed::get::<u32>(&k), Some(1u32));

		<instance::Map<Runtime, instance::Instance2>>::insert(1, 2);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Map")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map<Runtime, instance::Instance2>>::final_prefix());

		<instance::Map2<Runtime, instance::Instance2>>::insert(1, 2);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"Map2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(2u32));
		assert_eq!(&k[..32], &<instance::Map2<Runtime, instance::Instance2>>::final_prefix());

		<instance::DoubleMap<Runtime, instance::Instance2>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"DoubleMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		k.extend(2u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap<Runtime, instance::Instance2>>::final_prefix());

		<instance::DoubleMap2<Runtime, instance::Instance2>>::insert(&1, &2, &3);
		let mut k = [twox_128(b"Instance2FinalKeysSome"), twox_128(b"DoubleMap2")].concat();
		k.extend(1u32.using_encoded(twox_64_concat));
		k.extend(2u32.using_encoded(twox_64_concat));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
		assert_eq!(&k[..32], &<instance::DoubleMap2<Runtime, instance::Instance2>>::final_prefix());
	});
}
