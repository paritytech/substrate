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
use sp_std::collections::btree_map::BTreeMap;
use frame_support::{parameter_types, traits::{Hooks, fungible::{ItemOf, Mutate, Inspect, Credit, Balanced}, OnUnbalanced}, assert_ok, PalletId, ensure};
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
	pub static CoretimeCredit: BTreeMap<u64, u64> = Default::default();
	pub static CoretimeSpending: Vec<(u32, u64)> = Default::default();
	pub static CoretimeWorkplan: BTreeMap<(u32, CoreIndex), Vec<(CoreAssignment, PartsOf57600)>> = Default::default();
	pub static CoretimeUsage: BTreeMap<CoreIndex, Vec<(CoreAssignment, PartsOf57600)>> = Default::default();
	pub static CoretimeInPool: PartCount = 0;
	pub static NotifyCoreCount: Vec<u16> = Default::default();
	pub static NotifyRevenueInfo: Vec<(u32, u64)> = Default::default();
}

pub struct TestCoretimeProvider;
impl CoretimeInterface for TestCoretimeProvider {
	type AccountId = u64;
	type Balance = u64;
	type BlockNumber = u32;
	fn latest() -> Self::BlockNumber { System::block_number() as u32 }
	fn request_core_count(count: CoreIndex) {
		NotifyCoreCount::mutate(|s| s.insert(0, count));
	}
	fn request_revenue_info_at(when: Self::BlockNumber) {
		let mut total = 0;
		CoretimeSpending::mutate(|s| s.retain(|(n, a)| if *n < when { total += a; false } else { true }));
		NotifyRevenueInfo::mutate(|s| s.insert(0, (when, total)));
	}
	fn credit_account(who: Self::AccountId, amount: Self::Balance) {
		CoretimeCredit::mutate(|c| *c.entry(who).or_default() += amount);
	}
	fn assign_core(
		core: CoreIndex,
		begin: Self::BlockNumber,
		assignment: Vec<(CoreAssignment, PartsOf57600)>,
		end_hint: Option<Self::BlockNumber>,
	) {
		CoretimeWorkplan::mutate(|p| p.insert((begin, core), assignment.clone()));
		let item = (Self::latest(), AssignCore { core, begin, assignment, end_hint });
		CoretimeTrace::mutate(|v| v.push(item));
	}
	fn check_notify_core_count() -> Option<u16> {
		NotifyCoreCount::mutate(|s| s.pop())
	}
	fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)> {
		NotifyRevenueInfo::mutate(|s| s.pop())
	}
}
impl TestCoretimeProvider {
	pub fn spend_instantaneous(who: u64, price: u64) -> Result<(), ()> {
		let mut c = CoretimeCredit::get();
		ensure!(CoretimeInPool::get() > 0, ());
		c.insert(who, c.get(&who).ok_or(())?.checked_sub(price).ok_or(())?);
		CoretimeCredit::set(c);
		CoretimeSpending::mutate(|v| v.push((Self::latest(), price)));
		Ok(())
	}
	pub fn bump() {
		let mut pool_size = CoretimeInPool::get();
		let mut workplan = CoretimeWorkplan::get();
		let mut usage = CoretimeUsage::get();
		let now = Self::latest();
		workplan.retain(|(when, core), assignment| {
			if *when <= now {
				if let Some(old_assignment) = usage.get(core) {
					if let Some(a) = old_assignment.iter().find(|i| i.0 == CoreAssignment::Pool) {
						pool_size -= (a.1 / 720) as PartCount;
					}
				}
				if let Some(a) = assignment.iter().find(|i| i.0 == CoreAssignment::Pool) {
					pool_size += (a.1 / 720) as PartCount;
				}
				usage.insert(*core, assignment.clone());
				false
			} else {
				true
			}
		});
		CoretimeInPool::set(pool_size);
		CoretimeWorkplan::set(workplan);
		CoretimeUsage::set(usage);
	}
}

parameter_types! {
	pub const TestBrokerId: PalletId = PalletId(*b"TsBroker");
}

pub struct IntoZero;
impl OnUnbalanced<Credit<u64, <Test as Config>::Currency>> for IntoZero {
	fn on_nonzero_unbalanced(credit: Credit<u64, <Test as Config>::Currency>) {
		let _ = <<Test as Config>::Currency as Balanced<_>>::resolve(&0, credit);
	}
}

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = ItemOf<TestFungibles<(), u64, (), ConstU64<0>, ()>, (), u64>;
	type OnRevenue = IntoZero;
	type TimeslicePeriod = ConstU32<2>;
	type MaxLeasedCores = ConstU32<5>;
	type MaxReservedCores = ConstU32<5>;
	type Coretime = TestCoretimeProvider;
	type ConvertBalance = Identity;
	type WeightInfo = ();
	type PalletId = TestBrokerId;
}

pub fn advance_to(b: u64) {
	while System::block_number() < b {
		System::set_block_number(System::block_number() + 1);
		TestCoretimeProvider::bump();
		Broker::on_initialize(System::block_number());
	}
}

pub fn pot() -> u64 {
	<<Test as Config>::Currency as Inspect<_>>::total_balance(&Broker::account_id())
}

pub fn revenue() -> u64 {
	<<Test as Config>::Currency as Inspect<_>>::total_balance(&0)
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
