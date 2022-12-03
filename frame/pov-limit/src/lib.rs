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
//! NOTE: This is only meant to be used for testing

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::pallet_prelude::*;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Specifies the computation usage of this pallet on `on_initialize`.
		#[pallet::constant]
		type Compute: Get<u32>;

		/// Specifies the storage usage of this pallet on `on_initialize`.
		#[pallet::constant]
		type Storage: Get<u32>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_: BlockNumberFor<T>) -> Weight {
			for i in 0..T::Compute::get() {
				Self::hash_value(i)
			}

			for _i in 0..T::Storage::get() {}
			Weight::zero()
		}
	}

	impl<T: Config> Pallet<T> {
		fn hash_value(value: u32) {
			let config = argon2::Config::default();
			// the salt is really not important here.
			let salt = b"somesalt";
			let _ = argon2::hash_encoded(vec![value as u8, 100].as_slice(), salt, &config);
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
			Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
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

	impl pallet_balances::Config for Test {
		type MaxLocks = ();
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type Balance = u64;
		type RuntimeEvent = RuntimeEvent;
		type DustRemoval = ();
		type ExistentialDeposit = ConstU64<1>;
		type AccountStore = System;
		type WeightInfo = ();
	}

	impl Config for Test {
		type Compute = ConstU32<50>;
		type Storage = ConstU32<50>;
	}

	#[test]
	fn hash_value_works() {
		// I only added this so that I can check whether the hashing actually
		// takes some time(It does, almost 9 seconds on my Apple M1 chip).
		// I WILL REMOVE THIS.
		PovLimit::on_initialize(0);
	}
}
