// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! The crate's tests.

use std::collections::BTreeMap;

use frame_support::{
	assert_noop, assert_ok,
	pallet_prelude::Weight,
	parameter_types,
	traits::{ConstU32, ConstU64, Everything},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, Identity, IdentityLookup},
};
use sp_std::cell::RefCell;

use super::*;
use crate as pallet_paymaster;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Paymaster: pallet_paymaster::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::from_ref_time(1_000_000));
}
impl frame_system::Config for Test {
	type BaseCallFilter = Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
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
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

thread_local! {
	pub static PAID: RefCell<BTreeMap<u64, u64>> = RefCell::new(BTreeMap::new());
	pub static BUDGET: RefCell<u64> = RefCell::new(10u64);
	pub static LAST_ID: RefCell<u64> = RefCell::new(0u64);
}

fn paid(who: u64) -> u64 {
	PAID.with(|p| p.borrow().get(&who).cloned().unwrap_or(0))
}

pub struct TestPay;
impl Pay for TestPay {
	type AccountId = u64;
	type Balance = u64;
	type Id = u64;

	fn budget() -> Self::Balance {
		BUDGET.with(|b| *b.borrow())
	}

	fn pay(who: &Self::AccountId, amount: Self::Balance) -> Result<Self::Id, ()> {
		PAID.with(|paid| *paid.borrow_mut().entry(*who).or_default() += amount);
		Ok(LAST_ID.with(|lid| {
			let x = *lid.borrow();
			lid.replace(x + 1);
			x
		}))
	}
}

thread_local! {
	pub static CLUB: RefCell<BTreeMap<u64, u64>> = RefCell::new(BTreeMap::new());
}

pub struct TestClub;
impl RankedMembers for TestClub {
	type AccountId = u64;
	type Rank = u64;
	fn rank_of(who: &Self::AccountId) -> Option<Self::Rank> {
		CLUB.with(|club| club.borrow().get(who).cloned())
	}
	fn remove(who: &Self::AccountId) {
		CLUB.with(|club| club.borrow_mut().remove(&who));
	}
	fn change(who: &Self::AccountId, rank: Self::Rank) {
		CLUB.with(|club| club.borrow_mut().insert(*who, rank));
	}
}

impl Config for Test {
	type WeightInfo = ();
	type RuntimeEvent = RuntimeEvent;
	type Paymaster = TestPay;
	type Members = TestClub;
	type ActiveSalaryForRank = Identity;
	type CyclePeriod = ConstU64<4>;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn next_block() {
	System::set_block_number(System::block_number() + 1);
}

#[allow(dead_code)]
fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

#[test]
fn basic_stuff() {
	new_test_ext().execute_with(|| {
		assert!(Paymaster::last_claim(&0).is_err());
		assert_eq!(Paymaster::status(), None);
	});
}

#[test]
fn can_start() {
	new_test_ext().execute_with(|| {
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_eq!(
			Paymaster::status(),
			Some(StatusType { cycle_index: 0, cycle_start: 1, remaining_budget: 10 })
		);
	});
}

#[test]
fn next_cycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		run_to(4);
		assert_noop!(Paymaster::next_cycle(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);

		run_to(5);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_eq!(
			Paymaster::status(),
			Some(StatusType { cycle_index: 1, cycle_start: 5, remaining_budget: 10 })
		);

		run_to(8);
		assert_noop!(Paymaster::next_cycle(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);

		BUDGET.with(|b| b.replace(5));
		run_to(9);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_eq!(
			Paymaster::status(),
			Some(StatusType { cycle_index: 2, cycle_start: 9, remaining_budget: 5 })
		);
	});
}

#[test]
fn induct_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));

		assert_noop!(Paymaster::induct(RuntimeOrigin::signed(1)), Error::<Test>::NotMember);
		TestClub::change(&1, 1);
		assert!(Paymaster::last_claim(&1).is_err());
		assert_ok!(Paymaster::induct(RuntimeOrigin::signed(1)));
		assert_eq!(Paymaster::last_claim(&1).unwrap(), 0);
		assert_noop!(Paymaster::induct(RuntimeOrigin::signed(1)), Error::<Test>::AlreadyInducted);
	});
}

#[test]
fn payment_works() {
	new_test_ext().execute_with(|| {
		TestClub::change(&1, 1);
		assert_noop!(Paymaster::induct(RuntimeOrigin::signed(1)), Error::<Test>::NotStarted);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_noop!(Paymaster::payout(RuntimeOrigin::signed(1)), Error::<Test>::NotInducted);
		assert_ok!(Paymaster::induct(RuntimeOrigin::signed(1)));
		// No claim on the cycle active during induction.
		assert_noop!(Paymaster::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);

		run_to(5);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_ok!(Paymaster::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 1);
		assert_eq!(Paymaster::status().unwrap().remaining_budget, 9);
		assert_noop!(Paymaster::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		run_to(8);
		assert_noop!(Paymaster::next_cycle(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);
		run_to(9);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_ok!(Paymaster::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 2);
		assert_eq!(Paymaster::status().unwrap().remaining_budget, 9);
	});
}

#[test]
fn zero_payment_fails() {
	new_test_ext().execute_with(|| {
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		TestClub::change(&1, 0);
		assert_ok!(Paymaster::induct(RuntimeOrigin::signed(1)));
		run_to(5);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_noop!(Paymaster::payout(RuntimeOrigin::signed(1)), Error::<Test>::ClaimZero);
	});
}

#[test]
fn bankrupt_fails_gracefully() {
	new_test_ext().execute_with(|| {
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		TestClub::change(&1, 11);
		assert_ok!(Paymaster::induct(RuntimeOrigin::signed(1)));
		run_to(5);
		assert_ok!(Paymaster::next_cycle(RuntimeOrigin::signed(1)));
		assert_noop!(Paymaster::payout(RuntimeOrigin::signed(1)), Error::<Test>::Bankrupt);
		assert_eq!(paid(1), 0);
	});
}
