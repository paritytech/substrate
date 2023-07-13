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

//! Generators are a set of trait on which storage traits are implemented.
//!
//! (i.e. implementing the generator for StorageValue on a type will automatically derive the
//! implementation of StorageValue for this type).
//!
//! They are used by `decl_storage`.
//!
//! This is internal api and is subject to change.

mod double_map;
pub(crate) mod map;
mod nmap;
mod value;

pub use double_map::StorageDoubleMap;
pub use map::StorageMap;
pub use nmap::StorageNMap;
pub use value::StorageValue;

#[cfg(test)]
mod tests {
	use codec::Encode;
	use sp_io::TestExternalities;
	use sp_runtime::{generic, traits::BlakeTwo256, BuildStorage};

	use crate::{
		assert_noop, assert_ok,
		storage::{generator::StorageValue, unhashed},
	};

	#[crate::pallet]
	pub mod frame_system {
		#[allow(unused)]
		use super::{frame_system, frame_system::pallet_prelude::*};
		pub use crate::dispatch::RawOrigin;
		use crate::pallet_prelude::*;

		#[pallet::pallet]
		pub struct Pallet<T>(_);

		#[pallet::config]
		#[pallet::disable_frame_system_supertrait_check]
		pub trait Config: 'static {
			type BlockNumber;
			type AccountId;
			type BaseCallFilter: crate::traits::Contains<Self::RuntimeCall>;
			type RuntimeOrigin;
			type RuntimeCall;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: Get<crate::weights::RuntimeDbWeight>;
		}

		#[pallet::origin]
		pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;

		#[pallet::error]
		pub enum Error<T> {
			/// Required by construct_runtime
			CallFiltered,
		}

		#[pallet::call]
		impl<T: Config> Pallet<T> {}

		#[pallet::storage]
		pub type Value<T> = StorageValue<_, (u64, u64), ValueQuery>;

		#[pallet::storage]
		pub type Map<T> = StorageMap<_, Blake2_128Concat, u16, u64, ValueQuery>;

		#[pallet::storage]
		pub type NumberMap<T> = StorageMap<_, Identity, u32, u64, ValueQuery>;

		#[pallet::storage]
		pub type DoubleMap<T> =
			StorageDoubleMap<_, Blake2_128Concat, u16, Twox64Concat, u32, u64, ValueQuery>;

		#[pallet::storage]
		pub type NMap<T> = StorageNMap<
			_,
			(storage::Key<Blake2_128Concat, u16>, storage::Key<Twox64Concat, u32>),
			u64,
			ValueQuery,
		>;

		pub mod pallet_prelude {
			pub type OriginFor<T> = <T as super::Config>::RuntimeOrigin;
		}
	}

	type BlockNumber = u32;
	type AccountId = u32;
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;
	type Block = generic::Block<Header, UncheckedExtrinsic>;

	crate::construct_runtime!(
		pub enum Runtime
		where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: self::frame_system,
		}
	);

	impl self::frame_system::Config for Runtime {
		type BlockNumber = BlockNumber;
		type AccountId = AccountId;
		type BaseCallFilter = crate::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type PalletInfo = PalletInfo;
		type DbWeight = ();
	}

	pub fn key_before_prefix(mut prefix: Vec<u8>) -> Vec<u8> {
		let last = prefix.iter_mut().last().unwrap();
		assert_ne!(*last, 0, "mock function not implemented for this prefix");
		*last -= 1;
		prefix
	}

	pub fn key_after_prefix(mut prefix: Vec<u8>) -> Vec<u8> {
		let last = prefix.iter_mut().last().unwrap();
		assert_ne!(*last, 255, "mock function not implemented for this prefix");
		*last += 1;
		prefix
	}

	#[test]
	fn value_translate_works() {
		let t = RuntimeGenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			type Value = self::frame_system::Value<Runtime>;

			// put the old value `1111u32` in the storage.
			let key = Value::storage_value_final_key();
			unhashed::put_raw(&key, &1111u32.encode());

			// translate
			let translate_fn = |old: Option<u32>| -> Option<(u64, u64)> {
				old.map(|o| (o.into(), (o * 2).into()))
			};
			let res = Value::translate(translate_fn);
			debug_assert!(res.is_ok());

			// new storage should be `(1111, 1111 * 2)`
			assert_eq!(Value::get(), (1111, 2222));
		})
	}

	#[test]
	fn map_translate_works() {
		let t = RuntimeGenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			type NumberMap = self::frame_system::NumberMap<Runtime>;

			// start with a map of u32 -> u64.
			for i in 0u32..100u32 {
				unhashed::put(&NumberMap::hashed_key_for(&i), &(i as u64));
			}

			assert_eq!(
				NumberMap::iter().collect::<Vec<_>>(),
				(0..100).map(|x| (x as u32, x as u64)).collect::<Vec<_>>(),
			);

			// do translation.
			NumberMap::translate(
				|k: u32, v: u64| if k % 2 == 0 { Some((k as u64) << 32 | v) } else { None },
			);

			assert_eq!(
				NumberMap::iter().collect::<Vec<_>>(),
				(0..50u32)
					.map(|x| x * 2)
					.map(|x| (x, (x as u64) << 32 | x as u64))
					.collect::<Vec<_>>(),
			);
		})
	}

	#[test]
	fn try_mutate_works() {
		let t = RuntimeGenesisConfig::default().build_storage().unwrap();
		TestExternalities::new(t).execute_with(|| {
			type Value = self::frame_system::Value<Runtime>;
			type NumberMap = self::frame_system::NumberMap<Runtime>;
			type DoubleMap = self::frame_system::DoubleMap<Runtime>;

			assert_eq!(Value::get(), (0, 0));
			assert_eq!(NumberMap::get(0), 0);
			assert_eq!(DoubleMap::get(0, 0), 0);

			// `assert_noop` ensures that the state does not change
			assert_noop!(
				Value::try_mutate(|value| -> Result<(), &'static str> {
					*value = (2, 2);
					Err("don't change value")
				}),
				"don't change value"
			);

			assert_noop!(
				NumberMap::try_mutate(0, |value| -> Result<(), &'static str> {
					*value = 4;
					Err("don't change value")
				}),
				"don't change value"
			);

			assert_noop!(
				DoubleMap::try_mutate(0, 0, |value| -> Result<(), &'static str> {
					*value = 6;
					Err("don't change value")
				}),
				"don't change value"
			);

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
