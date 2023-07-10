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

#![cfg(test)]

use crate::*;
use frame_support::{parameter_types, traits::fungible::ItemOf};
use sp_core::{H256, ConstU64, ConstU16, ConstU32};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, Identity},
};
use crate::test_fungibles::TestFungibles;

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
		Broker: crate,
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
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ConstU16<42>;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum CoretimeTraceItem {
	AssignCore {
		core: CoreIndex,
		begin: u32,
		assignment: Vec<(CoreAssignment, PartsOf57600)>,
		end_hint: Option<u32>,
	},
}
use CoretimeTraceItem::*;

parameter_types!{
	pub static CoretimeTrace: Vec<(u32, CoretimeTraceItem)> = Default::default();
}

impl CoretimeInterface for CoretimeTrace {
	type AccountId = ();
	type Balance = u64;
	type BlockNumber = u32;
	fn latest() -> Self::BlockNumber { System::block_number() as u32 }
	fn request_core_count(_count: CoreIndex) {}
	fn request_revenue_info_at(_when: Self::BlockNumber) {}
	fn credit_account(_who: Self::AccountId, _amount: Self::Balance) {}
	fn assign_core(
		core: CoreIndex,
		begin: Self::BlockNumber,
		assignment: Vec<(CoreAssignment, PartsOf57600)>,
		end_hint: Option<Self::BlockNumber>,
	) {
		let mut v = CoretimeTrace::get();
		v.push((Self::latest(), AssignCore { core, begin, assignment, end_hint }));
		CoretimeTrace::set(v);
	}
	fn check_notify_core_count() -> Option<u16> { None }
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)> { None }
}

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = ItemOf<TestFungibles<(), u64, (), ConstU64<0>, ()>, (), u64>;
	type OnRevenue = ();
	type TimeslicePeriod = ConstU32<2>;
	type MaxLeasedCores = ConstU32<5>;
	type MaxReservedCores = ConstU32<5>;
	type Coretime = CoretimeTrace;
	type ConvertBalance = Identity;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}
