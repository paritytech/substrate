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

//! Generators are a set of trait on which storage traits are implemented.
//!
//! (i.e. implementing the generator for StorageValue on a type will automatically derive the
//! implementation of StorageValue for this type).
//!
//! They are used by `decl_storage`.
//!
//! This is internal api and is subject to change.

mod map;
mod double_map;
mod value;

pub use map::StorageMap;
pub use double_map::StorageDoubleMap;
pub use value::StorageValue;

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use sp_io::TestExternalities;
	use codec::Encode;
	use crate::storage::{unhashed, generator::StorageValue, IterableStorageMap};
	use crate::{assert_noop, assert_ok};

	struct Runtime {}
	pub trait Trait {
		type Origin;
		type BlockNumber;
	}

	impl Trait for Runtime {
		type Origin = u32;
		type BlockNumber = u32;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
	}

	crate::decl_storage! {
		trait Store for Module<T: Trait> as Runtime {
			Value get(fn value) config(): (u64, u64);
			NumberMap: map hasher(identity) u32 => u64;
			DoubleMap: double_map hasher(identity) u32, hasher(identity) u32 => u64;
		}
	}

	#[test]
	fn value_translate_works() {
		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			// put the old value `1111u32` in the storage.
			let key = Value::storage_value_final_key();
			unhashed::put_raw(&key, &1111u32.encode());

			// translate
			let translate_fn = |old: Option<u32>| -> Option<(u64, u64)> {
				old.map(|o| (o.into(), (o*2).into()))
			};
			let _ = Value::translate(translate_fn);

			// new storage should be `(1111, 1111 * 2)`
			assert_eq!(Value::get(), (1111, 2222));
		})
	}

	#[test]
	fn map_translate_works() {
		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			// start with a map of u32 -> u32.
			for i in 0u32..100u32 {
				unhashed::put(&NumberMap::hashed_key_for(&i), &(i as u64));
			}

			assert_eq!(
				NumberMap::iter().collect::<Vec<_>>(),
				(0..100).map(|x| (x as u32, x as u64)).collect::<Vec<_>>(),
			);

			// do translation.
			NumberMap::translate(|k: u32, v: u64| if k % 2 == 0 { Some((k as u64) << 32 | v) } else { None });

			assert_eq!(
				NumberMap::iter().collect::<Vec<_>>(),
				(0..50u32).map(|x| x * 2).map(|x| (x, (x as u64) << 32 | x as u64)).collect::<Vec<_>>(),
			);
		})
	}

	#[test]
	fn try_mutate_works() {
		let t = GenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			assert_eq!(Value::get(), (0, 0));
			assert_eq!(NumberMap::get(0), 0);
			assert_eq!(DoubleMap::get(0, 0), 0);

			// `assert_noop` ensures that the state does not change
			assert_noop!(Value::try_mutate(|value| -> Result<(), &'static str> {
				*value = (2, 2);
				Err("don't change value")
			}), "don't change value");

			assert_noop!(NumberMap::try_mutate(0, |value| -> Result<(), &'static str> {
				*value = 4;
				Err("don't change value")
			}), "don't change value");

			assert_noop!(DoubleMap::try_mutate(0, 0, |value| -> Result<(), &'static str> {
				*value = 6;
				Err("don't change value")
			}), "don't change value");

			// Showing this explicitly for clarity
			assert_eq!(Value::get(), (0, 0));
			assert_eq!(NumberMap::get(0), 0);
			assert_eq!(DoubleMap::get(0, 0), 0);

			assert_ok!(Value::try_mutate(|value| -> Result<(), &'static str> {
				*value = (2, 2);
				Ok(())
			}));

			assert_ok!(NumberMap::try_mutate(0, |value| -> Result<(), &'static str> {
				*value = 4;
				Ok(())
			}));

			assert_ok!(DoubleMap::try_mutate(0, 0, |value| -> Result<(), &'static str> {
				*value = 6;
				Ok(())
			}));

			assert_eq!(Value::get(), (2, 2));
			assert_eq!(NumberMap::get(0), 4);
			assert_eq!(DoubleMap::get(0, 0), 6);
		});
	}
}
