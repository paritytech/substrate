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

//! Test utilities

use super::*;
use crate as sudo;
use frame_support::traits::{ConstU32, ConstU64, Contains};
use sp_core::H256;
use sp_io;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup},
	BuildStorage,
};

// Logger module to track execution.
#[frame_support::pallet]
pub mod logger {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(*weight)]
		pub fn privileged_i32_log(
			origin: OriginFor<T>,
			i: i32,
			weight: Weight,
		) -> DispatchResultWithPostInfo {
			// Ensure that the `origin` is `Root`.
			ensure_root(origin)?;
			<I32Log<T>>::try_append(i).map_err(|_| "could not append")?;
			Self::deposit_event(Event::AppendI32 { value: i, weight });
			Ok(().into())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(*weight)]
		pub fn non_privileged_log(
			origin: OriginFor<T>,
			i: i32,
			weight: Weight,
		) -> DispatchResultWithPostInfo {
			// Ensure that the `origin` is some signed account.
			let sender = ensure_signed(origin)?;
			<I32Log<T>>::try_append(i).map_err(|_| "could not append")?;
			<AccountLog<T>>::try_append(sender.clone()).map_err(|_| "could not append")?;
			Self::deposit_event(Event::AppendI32AndAccount { sender, value: i, weight });
			Ok(().into())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		AppendI32 { value: i32, weight: Weight },
		AppendI32AndAccount { sender: T::AccountId, value: i32, weight: Weight },
	}

	#[pallet::storage]
	#[pallet::getter(fn account_log)]
	pub(super) type AccountLog<T: Config> =
		StorageValue<_, BoundedVec<T::AccountId, ConstU32<1_000>>, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn i32_log)]
	pub(super) type I32Log<T> = StorageValue<_, BoundedVec<i32, ConstU32<1_000>>, ValueQuery>;
}

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Sudo: sudo::{Pallet, Call, Config<T>, Storage, Event<T>},
		Logger: logger::{Pallet, Call, Storage, Event<T>},
	}
);

pub struct BlockEverything;
impl Contains<RuntimeCall> for BlockEverything {
	fn contains(_: &RuntimeCall) -> bool {
		false
	}
}

impl frame_system::Config for Test {
	type BaseCallFilter = BlockEverything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

// Implement the logger module's `Config` on the Test runtime.
impl logger::Config for Test {
	type RuntimeEvent = RuntimeEvent;
}

// Implement the sudo module's `Config` on the Test runtime.
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type RuntimeCall = RuntimeCall;
	type WeightInfo = ();
}

// New types for dispatchable functions.
pub type SudoCall = sudo::Call<Test>;
pub type LoggerCall = logger::Call<Test>;

// Build test environment by setting the root `key` for the Genesis.
pub fn new_test_ext(root_key: u64) -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	sudo::GenesisConfig::<Test> { key: Some(root_key) }
		.assimilate_storage(&mut t)
		.unwrap();
	t.into()
}

#[cfg(feature = "runtime-benchmarks")]
pub fn new_bench_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::<Test>::default().build_storage().unwrap().into()
}
