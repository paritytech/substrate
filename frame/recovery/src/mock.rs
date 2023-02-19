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

use crate as recovery;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64, OnFinalize, OnInitialize},
};
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
		Recovery: recovery::{Pallet, Call, Storage, Event<T>},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u128>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u128;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub const ConfigDepositBase: u64 = 10;
	pub const FriendDepositFactor: u64 = 1;
	pub const RecoveryDeposit: u64 = 10;
	// Large number of friends for benchmarking.
	pub const MaxFriends: u32 = 128;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type RuntimeCall = RuntimeCall;
	type Currency = Balances;
	type ConfigDepositBase = ConfigDepositBase;
	type FriendDepositFactor = FriendDepositFactor;
	type MaxFriends = MaxFriends;
	type RecoveryDeposit = RecoveryDeposit;
}

pub type BalancesCall = pallet_balances::Call<Test>;
pub type RecoveryCall = super::Call<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 100), (2, 100), (3, 100), (4, 100), (5, 100)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	t.into()
}

/// Run until a particular block.
pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		if System::block_number() > 1 {
			System::on_finalize(System::block_number());
		}
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
	}
}
