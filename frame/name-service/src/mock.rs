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

use sp_runtime::testing::Header;
use sp_runtime::Perbill;
use sp_core::H256;
use frame_support::{impl_outer_origin, impl_outer_event, parameter_types, ord_parameter_types, weights::Weight};
use crate::{self as pallet_name_service, Module, Config, ExtensionConfig};
use frame_system::EnsureSignedBy;

impl_outer_origin!{
	pub enum Origin for Test where system = frame_system {}
}
impl_outer_event!{
	pub enum Event for Test {
		frame_system<T>,
		pallet_balances<T>,
		pallet_name_service<T>,
	}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

type BlockNumber = u64;
type Balance = u64;

impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = ::sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = NameService;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type Balance = Balance;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}


parameter_types! {
	pub const BiddingPeriod: BlockNumber = 10;
	pub const ClaimPeriod: BlockNumber = 5;
	pub const OwnershipPeriod: BlockNumber = 100;
	pub const MinBid: Balance = 5;
	pub ExtensionsOn: ExtensionConfig<BlockNumber, Balance> = ExtensionConfig {
		enabled: true,
		extension_period: 100,
		extension_fee: 5,
	};
}

ord_parameter_types! {
	pub const Manager: u64 = 100;
	pub const Permanence: u64 = 200;
}

impl Config for Test {
	type AccountIndex = ();
	type Currency = Balances;
	type Event = Event;
	type ManagerOrigin = EnsureSignedBy<Manager, u64>;
	type PermanenceOrigin = EnsureSignedBy<Permanence, u64>;
	type BiddingPeriod = BiddingPeriod;
	type ClaimPeriod = ClaimPeriod;
	type OwnershipPeriod = OwnershipPeriod;
	type PaymentDestination = ();
	type MinBid = MinBid;
	type ExtensionConfig = ExtensionsOn;
	type WeightInfo = ();
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		balances: vec![(1, 100), (2, 200), (3, 300), (4, 400), (5, 500), (6, 600)],
	}.assimilate_storage(&mut t).unwrap();
	t.into()
}

pub type System = frame_system::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;
pub type NameService = Module<Test>;
