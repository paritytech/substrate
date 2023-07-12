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

//! # Statement pallet test environment.

use super::*;

use crate as pallet_statement;
use frame_support::{
	ord_parameter_types,
	traits::{ConstU32, ConstU64, Everything},
	weights::constants::RocksDbWeight,
};
use sp_core::{Pair, H256};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	AccountId32, BuildStorage,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

pub const MIN_ALLOWED_STATEMENTS: u32 = 4;
pub const MAX_ALLOWED_STATEMENTS: u32 = 10;
pub const MIN_ALLOWED_BYTES: u32 = 1024;
pub const MAX_ALLOWED_BYTES: u32 = 4096;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		Statement: pallet_statement,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = RocksDbWeight;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId32;
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
	type Balance = u64;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<5>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ConstU32<50>;
	type ReserveIdentifier = [u8; 8];
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = RuntimeHoldReason;
	type MaxHolds = ();
}

ord_parameter_types! {
	pub const One: u64 = 1;
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type StatementCost = ConstU64<1000>;
	type ByteCost = ConstU64<2>;
	type MinAllowedStatements = ConstU32<MIN_ALLOWED_STATEMENTS>;
	type MaxAllowedStatements = ConstU32<MAX_ALLOWED_STATEMENTS>;
	type MinAllowedBytes = ConstU32<MIN_ALLOWED_BYTES>;
	type MaxAllowedBytes = ConstU32<MAX_ALLOWED_BYTES>;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	let balances = pallet_balances::GenesisConfig::<Test> {
		balances: vec![
			(sp_core::sr25519::Pair::from_string("//Alice", None).unwrap().public().into(), 6000),
			(
				sp_core::sr25519::Pair::from_string("//Charlie", None).unwrap().public().into(),
				500000,
			),
		],
	};
	balances.assimilate_storage(&mut t).unwrap();
	t.into()
}
