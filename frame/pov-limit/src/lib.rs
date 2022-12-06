// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! # Pov Limit Pallet
//!
//! Pallet that consumes up to a specified weight of a block on `on_initialize`.
//! The weight consumed is set as a percentage as a config parameter.
//!
//! NOTE: This is only meant to be used for testing.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{pallet_prelude::*, traits::GenesisBuild};
use sp_core::{Blake2Hasher, Hasher};
use sp_runtime::Perbill;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The number of times the hash function should be called to fill up
		/// all the block's weight.
		#[pallet::constant]
		type HashesForFull: Get<u32>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	pub(crate) type Compute<T: Config> = StorageValue<_, Perbill, ValueQuery>;

	#[pallet::storage]
	pub(crate) type Storage<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub compute: Perbill,
		pub storage: u32,
	}

	#[cfg(feature = "std")]
	impl Default for GenesisConfig {
		fn default() -> Self {
			Self { compute: Default::default(), storage: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			Compute::<T>::set(self.compute);
			Storage::<T>::set(self.storage);
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			for i in 0..(Compute::<T>::get().mul_ceil(T::HashesForFull::get())) {
				Blake2Hasher::hash(&i.to_le_bytes());
			}

			for i in 0..Storage::<T>::get() {
				storage::unhashed::put(&i.to_le_bytes(), &i.to_le_bytes());
				let _: Option<Vec<u8>> = storage::unhashed::get(&i.to_le_bytes());
			}
			Weight::zero()
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set the `Computation` storage value that determines how much of the
		/// block's weight to use up during `on_initialize`.
		///
		/// Only callable by Root.
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_computation(origin: OriginFor<T>, compute: Perbill) -> DispatchResult {
			let _ = ensure_root(origin)?;
			Compute::<T>::set(compute);

			Ok(())
		}

		/// Set the `Storage` storage value that determines the PoV size for
		/// each block.
		///
		/// Only callable by Root.
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_storage(origin: OriginFor<T>, storage: u32) -> DispatchResult {
			let _ = ensure_root(origin)?;
			Storage::<T>::set(storage);

			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate as pallet_pov_limit;

	use frame_support::traits::{ConstU32, ConstU64};
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
	};

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			PovLimit: pallet_pov_limit::{Pallet},
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type RuntimeOrigin = RuntimeOrigin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type RuntimeCall = RuntimeCall;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type RuntimeEvent = RuntimeEvent;
		type BlockHashCount = ConstU64<250>;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = ConstU32<16>;
	}

	impl Config for Test {
		type HashesForFull = ConstU32<1000000>;
	}

	pub fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

		let genesis = pallet::GenesisConfig { compute: Perbill::from_percent(50), storage: 10000 };

		GenesisBuild::<Test>::assimilate_storage(&genesis, &mut t).unwrap();

		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}

	#[test]
	fn hash_value_works() {
		new_test_ext().execute_with(|| {
			PovLimit::on_initialize(0);
		});
	}
}
