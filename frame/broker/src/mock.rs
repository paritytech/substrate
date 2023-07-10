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
use frame_support::{parameter_types, traits::{Hooks, fungible::{ItemOf, Mutate}}, assert_ok};
use sp_arithmetic::Perbill;
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

pub fn advance_to(b: u64) {
	while System::block_number() < b {
		System::set_block_number(System::block_number() + 1);
		Broker::on_initialize(System::block_number());
	}
}

pub struct TestExt(ConfigRecordOf<Test>);
impl TestExt {
	pub fn new() -> Self {
		Self(ConfigRecord {
			core_count: 1,
			advance_notice: 1,
			interlude_length: 1,
			leadin_length: 1,
			ideal_bulk_proportion: Default::default(),
			limit_cores_offered: None,
			region_length: 3,
		})
	}

	pub fn core_count(mut self, core_count: CoreIndex) -> Self {
		self.0.core_count = core_count;
		self
	}

	pub fn advance_notice(mut self, advance_notice: Timeslice) -> Self {
		self.0.advance_notice = advance_notice;
		self
	}

	pub fn interlude_length(mut self, interlude_length: u64) -> Self {
		self.0.interlude_length = interlude_length;
		self
	}

	pub fn leadin_length(mut self, leadin_length: u64) -> Self {
		self.0.leadin_length = leadin_length;
		self
	}

	pub fn region_length(mut self, region_length: Timeslice) -> Self {
		self.0.region_length = region_length;
		self
	}

	pub fn ideal_bulk_proportion(mut self, ideal_bulk_proportion: Perbill) -> Self {
		self.0.ideal_bulk_proportion = ideal_bulk_proportion;
		self
	}

	pub fn limit_cores_offered(mut self, limit_cores_offered: Option<CoreIndex>) -> Self {
		self.0.limit_cores_offered = limit_cores_offered;
		self
	}

	pub fn endow(self, who: u64, amount: u64) -> Self {
		assert_ok!(<<Test as Config>::Currency as Mutate<_>>::mint_into(&who, amount));
		self
	}

	pub fn execute_with<R>(self, f: impl Fn() -> R) -> R {
		let c = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		sp_io::TestExternalities::from(c).execute_with(|| {
			assert_ok!(Broker::do_configure(self.0));
			f()
		})
	}
}
