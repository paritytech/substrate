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

//! Test environment for NIS pallet.

use crate::{self as pallet_nis, Perquintill, WithMaximumOf};

use frame_support::{
	ord_parameter_types, parameter_types,
	traits::{ConstU16, ConstU32, ConstU64, Currency, OnFinalize, OnInitialize, StorageMapShim},
	weights::Weight,
	PalletId,
};
use pallet_balances::{Instance1, Instance2};
use sp_core::{ConstU128, H256};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances::<Instance1>,
		NisBalances: pallet_balances::<Instance2>,
		Nis: pallet_nis,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
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
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ConstU16<42>;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config<Instance1> for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = frame_support::traits::ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ConstU32<1>;
	type ReserveIdentifier = [u8; 8];
}

impl pallet_balances::Config<Instance2> for Test {
	type Balance = u128;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = frame_support::traits::ConstU128<1>;
	type AccountStore = StorageMapShim<
		pallet_balances::Account<Test, Instance2>,
		frame_system::Provider<Test>,
		u64,
		pallet_balances::AccountData<u128>,
	>;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

parameter_types! {
	pub IgnoredIssuance: u64 = Balances::total_balance(&0); // Account zero is ignored.
	pub const NisPalletId: PalletId = PalletId(*b"py/nis  ");
	pub static Target: Perquintill = Perquintill::zero();
	pub const MinReceipt: Perquintill = Perquintill::from_percent(1);
	pub const ThawThrottle: (Perquintill, u64) = (Perquintill::from_percent(25), 5);
	pub static MaxIntakeWeight: Weight = Weight::from_parts(2_000_000_000_000, 0);
	pub const ReserveId: [u8; 8] = *b"py/nis  ";
}

ord_parameter_types! {
	pub const One: u64 = 1;
}

impl pallet_nis::Config for Test {
	type WeightInfo = ();
	type RuntimeEvent = RuntimeEvent;
	type PalletId = NisPalletId;
	type Currency = Balances;
	type CurrencyBalance = <Self as pallet_balances::Config<Instance1>>::Balance;
	type FundOrigin = frame_system::EnsureSigned<Self::AccountId>;
	type Deficit = ();
	type IgnoredIssuance = IgnoredIssuance;
	type Counterpart = NisBalances;
	type CounterpartAmount = WithMaximumOf<ConstU128<21_000_000u128>>;
	type Target = Target;
	type QueueCount = ConstU32<3>;
	type MaxQueueLen = ConstU32<3>;
	type FifoQueueLen = ConstU32<1>;
	type BasePeriod = ConstU64<3>;
	type MinBid = ConstU64<2>;
	type IntakePeriod = ConstU64<2>;
	type MaxIntakeWeight = MaxIntakeWeight;
	type MinReceipt = MinReceipt;
	type ThawThrottle = ThawThrottle;
	type ReserveId = ReserveId;
}

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test, Instance1> {
		balances: vec![(1, 100), (2, 100), (3, 100), (4, 100)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	t.into()
}

pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		Nis::on_finalize(System::block_number());
		Balances::on_finalize(System::block_number());
		System::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		Balances::on_initialize(System::block_number());
		Nis::on_initialize(System::block_number());
	}
}
