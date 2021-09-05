// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! A set of benchmarks which can establish a global baseline for all other
//! benchmarking.

use crate::{account, benchmarks, impl_benchmark_test_suite};
use frame_system::Pallet as System;
use sp_runtime::traits::Hash;
use sp_std::prelude::*;

const SEED: u32 = 1337;

pub struct Pallet<T: Config>(System<T>);
pub trait Config: frame_system::Config {}

benchmarks! {
	addition {
		let i in 0 .. 1_000_000;
		let mut start = 0;
	}: {
		(0..i).for_each(|_| start += 1);
	} verify {
		assert_eq!(start, i);
	}

	subtraction {
		let i in 0 .. 1_000_000;
		let mut start = u32::MAX;
	}: {
		(0..i).for_each(|_| start -= 1);
	} verify {
		assert_eq!(start, u32::MAX - i);
	}

	multiplication {
		let i in 0 .. 1_000_000;
		let mut out = 0;
	}:  {
		(1..=i).for_each(|j| out = i * j);
	} verify {
		assert_eq!(out, i * i);
	}

	division {
		let i in 0 .. 1_000_000;
		let mut out = 0;
	}: {
		(1..=i).for_each(|j| out = i / j);
	} verify {
		assert_eq!(out, i.min(1));
	}

	hashing {
		let i in 0 .. 100_000;
		let mut hash = T::Hash::default();
	}: {
		(0..=i).for_each(|j| hash = T::Hashing::hash(&j.to_be_bytes()));
	} verify {
		if i > 0 { assert!(hash != T::Hash::default()); }
	}

	storage_read {
		let i in 0 .. 1_000;
		let mut people = Vec::new();
		(0..i).for_each(|j| {
			let who: T::AccountId = account("user", j, SEED);
			System::<T>::inc_providers(&who);
			people.push(who);
		});
	}: {
		people.iter().for_each(|who| {
			// This does a storage read
			assert!(System::<T>::can_dec_provider(&who));
		});
	}

	storage_write {
		let i in 0 .. 1_000;
		let mut people = Vec::new();
		(0..i).for_each(|j| {
			let who: T::AccountId = account("user", j, SEED);
			people.push(who);
		});
	}: {
		people.iter().for_each(|who| {
			// This does a storage write
			System::<T>::inc_providers(&who);
		});
	} verify {
		people.iter().for_each(|who| {
			assert!(System::<T>::can_dec_provider(&who));
		});
	}
}

impl_benchmark_test_suite!(
	Pallet,
	crate::baseline::mock::new_test_ext(),
	crate::baseline::mock::Test,
);

#[cfg(test)]
pub mod mock {
	use sp_runtime::{testing::H256, traits::IdentityLookup};

	type AccountId = u64;
	type AccountIndex = u32;
	type BlockNumber = u64;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = AccountIndex;
		type BlockNumber = BlockNumber;
		type Call = Call;
		type Hash = H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::testing::Header;
		type Event = Event;
		type BlockHashCount = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
	}

	impl super::Config for Test {}

	pub fn new_test_ext() -> sp_io::TestExternalities {
		let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		sp_io::TestExternalities::new(t)
	}
}
