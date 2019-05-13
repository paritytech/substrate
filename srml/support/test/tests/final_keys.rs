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

use runtime_io::{with_externalities, Blake2Hasher};
use srml_support::{StorageValue, StorageMap, StorageDoubleMap};
use srml_support::storage::unhashed;
use srml_support::runtime_primitives::BuildStorage;
use parity_codec::Encode;

pub trait Trait {
	type Origin;
	type BlockNumber;
}

srml_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

srml_support::decl_storage!{
	trait Store for Module<T: Trait> as Module {
		pub Value config(value): u32;

		pub Map: map u32 => u32;
		pub Map2: map hasher(twox_128) u32 => u32;

		pub LinkedMap: linked_map u32 => u32;
		pub LinkedMap2: linked_map hasher(twox_128) u32 => u32;

		pub DoubleMap: double_map u32, blake2_256(u32) => u32;
		pub DoubleMap2: double_map hasher(twox_128) u32, blake2_128(u32) => u32;
	}
}

struct Test;
impl Trait for Test {
	type BlockNumber = u32;
	type Origin = u32;
}

fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
}

#[test]
fn final_keys() {
	with_externalities(&mut new_test_ext(), || {
		<Value<Test>>::put(1);
		assert_eq!(unhashed::get::<u32>(&runtime_io::twox_128(b"Module Value")), Some(1u32));

		<Map<Test>>::insert(1, 2);
		let mut k = b"Module Map".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&runtime_io::blake2_256(&k)), Some(2u32));

		<Map2<Test>>::insert(1, 2);
		let mut k = b"Module Map2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&runtime_io::twox_128(&k)), Some(2u32));

		<LinkedMap<Test>>::insert(1, 2);
		let mut k = b"Module LinkedMap".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&runtime_io::blake2_256(&k)), Some(2u32));

		<LinkedMap2<Test>>::insert(1, 2);
		let mut k = b"Module LinkedMap2".to_vec();
		k.extend(1u32.encode());
		assert_eq!(unhashed::get::<u32>(&runtime_io::twox_128(&k)), Some(2u32));

		<DoubleMap<Test>>::insert(1, 2, 3);
		let mut k = b"Module DoubleMap".to_vec();
		k.extend(1u32.encode());
		let mut k = runtime_io::blake2_256(&k).to_vec();
		k.extend(&runtime_io::blake2_256(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));

		<DoubleMap2<Test>>::insert(1, 2, 3);
		let mut k = b"Module DoubleMap2".to_vec();
		k.extend(1u32.encode());
		let mut k = runtime_io::twox_128(&k).to_vec();
		k.extend(&runtime_io::blake2_128(&2u32.encode()));
		assert_eq!(unhashed::get::<u32>(&k), Some(3u32));
	});
}
