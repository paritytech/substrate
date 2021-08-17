// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Test environment for Assets pallet.

use super::*;
use crate as pallet_assets;

use sp_core::H256;
use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::Header};
use frame_support::{parameter_types, construct_runtime};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::AllowAll;
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
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

parameter_types! {
	pub const AssetDeposit: u64 = 1;
	pub const ApprovalDeposit: u64 = 1;
	pub const StringLimit: u32 = 50;
	pub const MetadataDepositBase: u64 = 1;
	pub const MetadataDepositPerByte: u64 = 1;
}

impl Config for Test {
	type Event = Event;
	type Balance = u64;
	type AssetId = u32;
	type Currency = Balances;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type AssetDeposit = AssetDeposit;
	type MetadataDepositBase = MetadataDepositBase;
	type MetadataDepositPerByte = MetadataDepositPerByte;
	type ApprovalDeposit = ApprovalDeposit;
	type StringLimit = StringLimit;
	type Freezer = TestFreezer;
	type WeightInfo = ();
	type Extra = ();
}

use std::cell::RefCell;
use std::collections::HashMap;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Hook {
	Died(u32, u64),
}
thread_local! {
	static FROZEN: RefCell<HashMap<(u32, u64), u64>> = RefCell::new(Default::default());
	static HOOKS: RefCell<Vec<Hook>> = RefCell::new(Default::default());
}

pub struct TestFreezer;
impl FrozenBalance<u32, u64, u64> for TestFreezer {
	fn frozen_balance(asset: u32, who: &u64) -> Option<u64> {
		FROZEN.with(|f| f.borrow().get(&(asset, who.clone())).cloned())
	}

	fn died(asset: u32, who: &u64) {
		HOOKS.with(|h| h.borrow_mut().push(Hook::Died(asset, who.clone())));
	}
}

pub(crate) fn set_frozen_balance(asset: u32, who: u64, amount: u64) {
	FROZEN.with(|f| f.borrow_mut().insert((asset, who), amount));
}
pub(crate) fn clear_frozen_balance(asset: u32, who: u64) {
	FROZEN.with(|f| f.borrow_mut().remove(&(asset, who)));
}
pub(crate) fn hooks() -> Vec<Hook> {
	HOOKS.with(|h| h.borrow().clone())
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}
