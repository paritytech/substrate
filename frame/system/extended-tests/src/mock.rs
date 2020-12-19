// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Mock file for extended system tests.

#![cfg(test)]

use sp_core::H256;
use sp_runtime::{
	traits::{IdentityLookup, BlakeTwo256},
	testing::Header,
};
use frame_support::{
	impl_outer_origin, parameter_types, impl_outer_event,
	dispatch::{Dispatchable, DispatchInfo, PostDispatchInfo},
};

type AccountId = u64;
type AccountIndex = u32;
type BlockNumber = u64;

impl_outer_event! {
	pub enum Event for Test {
		frame_system<T>,
		pallet_balances<T>,
		pallet_assets<T>,
	}
}

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Debug, codec::Encode, codec::Decode)]
pub struct Call;

impl Dispatchable for Call {
	type Origin = ();
	type Config = ();
	type Info = DispatchInfo;
	type PostInfo = PostDispatchInfo;
	fn dispatch(self, _origin: Self::Origin)
		-> sp_runtime::DispatchResultWithInfo<Self::PostInfo> {
			panic!("Do not use dummy implementation for dispatch.");
	}
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Test;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
}

impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = AccountIndex;
	type Call = ();
	type BlockNumber = BlockNumber;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
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
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}

parameter_types! {
	pub const AssetDepositBase: u64 = 1;
	pub const AssetDepositPerZombie: u64 = 1;
}

impl pallet_assets::Config for Test {
	type Currency = Balances;
	type Event = Event;
	type Balance = u64;
	type AssetId = u32;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type AssetDepositBase = AssetDepositBase;
	type AssetDepositPerZombie = AssetDepositPerZombie;
	type WeightInfo = ();
}

pub type System = frame_system::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;
pub type Assets = pallet_assets::Module<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	sp_io::TestExternalities::new(t)
}
