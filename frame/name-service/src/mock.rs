// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use super::*;

use crate as pallet_name_service;
use frame_support::{
	ord_parameter_types,
	pallet_prelude::*,
	parameter_types,
	traits::{ConstU32, ConstU64, Everything},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, Identity, IdentityLookup},
	Perbill,
};

use frame_system::{EnsureRoot, EnsureSignedBy};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		NameService: pallet_name_service,
	}
);

type BlockNumber = u64;
type Balance = u64;

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}

impl Config for Test {
	type Event = Event;
	type Currency = Balances;
	type BlockNumberToBalance = Identity;
	// TODO: make a custom handler and test behavior
	type RegistrationFeeHandler = ();
	type CommitmentDeposit = ConstU64<10>;
	type NameDeposit = ConstU64<5>;
	type TierThreeLetters = ConstU64<7>;
	type TierFourLetters = ConstU64<3>;
	type BlocksPerRegistrationPeriod = ConstU64<5256000>;
	type NotificationPeriod = ConstU64<432000>;
	type FeePerRegistrationPeriod = ConstU64<1>;
	type TierDefault = ConstU64<1>;
	type RegistrationManager = EnsureRoot<Self::AccountId>;
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 100), (2, 200), (3, 300), (4, 400), (5, 500), (6, 600)],
	}
	.assimilate_storage(&mut t)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

pub type NameServiceEvent = crate::Event<Test>;
pub type BalancesError = pallet_balances::Error<Test>;
