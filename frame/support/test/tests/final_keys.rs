// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use support::storage::unhashed;
use codec::Encode;
use support::{StorageDoubleMap, StorageLinkedMap, StorageMap, StorageValue};
use runtime_io::{TestExternalities, hashing};

mod no_instance {
	use codec::{Encode, Decode, EncodeLike};

	pub trait Trait {
		type Origin;
		type BlockNumber: Encode + Decode + EncodeLike + Default + Clone;
	}

	support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}

	support::decl_storage!{
		trait Store for Module<T: Trait> as FinalKeysNone {
			pub Value config(value): u32;

			pub Map: map u32 => u32;
			pub Map2: map hasher(twox_128) u32 => u32;

			pub LinkedMap: linked_map u32 => u32;
			pub LinkedMap2: linked_map hasher(twox_128) u32 => u32;

			pub DoubleMap: double_map u32, blake2_256(u32) => u32;
			pub DoubleMap2: double_map hasher(twox_128) u32, blake2_128(u32) => u32;

			pub TestGenericValue get(fn test_generic_value) config(): Option<T::BlockNumber>;
			pub TestGenericDoubleMap get(fn foo2) config(test_generic_double_map):
				double_map u32, blake2_256(T::BlockNumber) => Option<u32>;
		}
	}
}

mod instance {
	pub trait Trait<I = DefaultInstance>: super::no_instance::Trait {}

	support::decl_module! {
		pub struct Module<T: Trait<I>, I: Instantiable = DefaultInstance>
			for enum Call where origin: T::Origin {}
	}

	support::decl_storage!{
		trait Store for Module<T: Trait<I>, I: Instantiable = DefaultInstance>
			as FinalKeysSome
		{
			pub Value config(value): u32;

			pub Map: map u32 => u32;
			pub Map2: map hasher(twox_128) u32 => u32;

			pub LinkedMap: linked_map u32 => u32;
			pub LinkedMap2: linked_map hasher(twox_128) u32 => u32;

			pub DoubleMap: double_map u32, blake2_256(u32) => u32;
			pub DoubleMap2: double_map hasher(twox_128) u32, blake2_128(u32) => u32;

			pub TestGenericValue get(fn test_generic_value) config(): Option<T::BlockNumber>;
			pub TestGenericDoubleMap get(fn foo2) config(test_generic_double_map):
				double_map u32, blake2_256(T::BlockNumber) => Option<u32>;
		}
		add_extra_genesis {
			// See `decl_storage` limitation.
			config(phantom): core::marker::PhantomData<I>;
		}
	}
}

#[test]
fn final_keys_no_instance() {
	TestExternalities::default().execute_with(|| {
		no_instance::Value::put(1);
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(b"FinalKeysNone Value")), Some(1u32));

		no_instance::Map::insert(1, 2);
		let mut k = b"FinalKeysNone Map".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));

		no_instance::Map2::insert(1, 2);
		let mut k = b"FinalKeysNone Map2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		let head = b"head of FinalKeysNone LinkedMap".to_vec();
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), None);

		no_instance::LinkedMap::insert(1, 2);
		let mut k = b"FinalKeysNone LinkedMap".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), Some(1u32));

		no_instance::LinkedMap2::insert(1, 2);
		let mut k = b"FinalKeysNone LinkedMap2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		no_instance::DoubleMap::insert(&1, &2, &3);
		let mut k = b"FinalKeysNone DoubleMap".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::blake2_256(&k).to_vec();
		k.extend(&hashing::blake2_256(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));

		no_instance::DoubleMap2::insert(&1, &2, &3);
		let mut k = b"FinalKeysNone DoubleMap2".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::twox_128(&k).to_vec();
		k.extend(&hashing::blake2_128(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
	});
}

#[test]
fn final_keys_default_instance() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<instance::DefaultInstance>>::put(1);
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(b"FinalKeysSome Value")), Some(1u32));

		<instance::Map<instance::DefaultInstance>>::insert(1, 2);
		let mut k = b"FinalKeysSome Map".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));

		<instance::Map2<instance::DefaultInstance>>::insert(1, 2);
		let mut k = b"FinalKeysSome Map2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		let head = b"head of FinalKeysSome LinkedMap".to_vec();
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), None);

		<instance::LinkedMap<instance::DefaultInstance>>::insert(1, 2);
		let mut k = b"FinalKeysSome LinkedMap".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), Some(1u32));

		<instance::LinkedMap2<instance::DefaultInstance>>::insert(1, 2);
		let mut k = b"FinalKeysSome LinkedMap2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		<instance::DoubleMap<instance::DefaultInstance>>::insert(&1, &2, &3);
		let mut k = b"FinalKeysSome DoubleMap".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::blake2_256(&k).to_vec();
		k.extend(&hashing::blake2_256(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));

		<instance::DoubleMap2<instance::DefaultInstance>>::insert(&1, &2, &3);
		let mut k = b"FinalKeysSome DoubleMap2".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::twox_128(&k).to_vec();
		k.extend(&hashing::blake2_128(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
	});
}

#[test]
fn final_keys_instance_2() {
	TestExternalities::default().execute_with(|| {
		<instance::Value<instance::Instance2>>::put(1);
		assert_eq!(
			unhashed::get::<u32>(&hashing::twox_128(b"Instance2FinalKeysSome Value")),
			Some(1u32)
		);

		<instance::Map<instance::Instance2>>::insert(1, 2);
		let mut k = b"Instance2FinalKeysSome Map".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));

		<instance::Map2<instance::Instance2>>::insert(1, 2);
		let mut k = b"Instance2FinalKeysSome Map2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		let head = b"head of Instance2FinalKeysSome LinkedMap".to_vec();
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), None);

		<instance::LinkedMap<instance::Instance2>>::insert(1, 2);
		let mut k = b"Instance2FinalKeysSome LinkedMap".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&k)), Some(2u32));
		assert_eq!(unhashed::get::<u32>(&hashing::blake2_256(&head)), Some(1u32));

		<instance::LinkedMap2<instance::Instance2>>::insert(1, 2);
		let mut k = b"Instance2FinalKeysSome LinkedMap2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&hashing::twox_128(&k)), Some(2u32));

		<instance::DoubleMap<instance::Instance2>>::insert(&1, &2, &3);
		let mut k = b"Instance2FinalKeysSome DoubleMap".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::blake2_256(&k).to_vec();
		k.extend(&hashing::blake2_256(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));

		<instance::DoubleMap2<instance::Instance2>>::insert(&1, &2, &3);
		let mut k = b"Instance2FinalKeysSome DoubleMap2".to_vec();
		k.extend(1u32.encode());
		let mut k = hashing::twox_128(&k).to_vec();
		k.extend(&hashing::blake2_128(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
	});
}
