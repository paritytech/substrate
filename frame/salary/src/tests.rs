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
	traits::{tokens::ConvertRank, ConstU32, ConstU64, Everything},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, Identity, IdentityLookup},
	DispatchResult,
};
use sp_std::cell::RefCell;

use super::*;
use crate as pallet_salary;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Salary: pallet_salary::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::from_parts(1_000_000, 0));
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
	pub static STATUS: RefCell<BTreeMap<u64, PaymentStatus>> = RefCell::new(BTreeMap::new());
	pub static LAST_ID: RefCell<u64> = RefCell::new(0u64);
}

fn paid(who: u64) -> u64 {
	PAID.with(|p| p.borrow().get(&who).cloned().unwrap_or(0))
}
fn unpay(who: u64, amount: u64) {
	PAID.with(|p| p.borrow_mut().entry(who).or_default().saturating_reduce(amount))
}
fn set_status(id: u64, s: PaymentStatus) {
	STATUS.with(|m| m.borrow_mut().insert(id, s));
}

pub struct TestPay;
impl Pay for TestPay {
	type Beneficiary = u64;
	type Balance = u64;
	type Id = u64;
	type AssetKind = ();

	fn pay(
		who: &Self::Beneficiary,
		_: Self::AssetKind,
		amount: Self::Balance,
	) -> Result<Self::Id, ()> {
		PAID.with(|paid| *paid.borrow_mut().entry(*who).or_default() += amount);
		Ok(LAST_ID.with(|lid| {
			let x = *lid.borrow();
			lid.replace(x + 1);
			x
		}))
	}
	fn check_payment(id: Self::Id) -> PaymentStatus {
		STATUS.with(|s| s.borrow().get(&id).cloned().unwrap_or(PaymentStatus::Unknown))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(_: &Self::Beneficiary, _: Self::Balance) {}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(id: Self::Id) {
		set_status(id, PaymentStatus::Failure)
	}
}

thread_local! {
	pub static CLUB: RefCell<BTreeMap<u64, u64>> = RefCell::new(BTreeMap::new());
}

pub struct TestClub;
impl RankedMembers for TestClub {
	type AccountId = u64;
	type Rank = u64;
	fn min_rank() -> Self::Rank {
		0
	}
	fn rank_of(who: &Self::AccountId) -> Option<Self::Rank> {
		CLUB.with(|club| club.borrow().get(who).cloned())
	}
	fn induct(who: &Self::AccountId) -> DispatchResult {
		CLUB.with(|club| club.borrow_mut().insert(*who, 0));
		Ok(())
	}
	fn promote(who: &Self::AccountId) -> DispatchResult {
		CLUB.with(|club| {
			club.borrow_mut().entry(*who).and_modify(|r| *r += 1);
		});
		Ok(())
	}
	fn demote(who: &Self::AccountId) -> DispatchResult {
		CLUB.with(|club| match club.borrow().get(who) {
			None => Err(sp_runtime::DispatchError::Unavailable),
			Some(&0) => {
				club.borrow_mut().remove(&who);
				Ok(())
			},
			Some(_) => {
				club.borrow_mut().entry(*who).and_modify(|x| *x -= 1);
				Ok(())
			},
		})
	}
}

fn set_rank(who: u64, rank: u64) {
	CLUB.with(|club| club.borrow_mut().insert(who, rank));
}

parameter_types! {
	pub static Budget: u64 = 10;
}

impl Config for Test {
	type WeightInfo = ();
	type RuntimeEvent = RuntimeEvent;
	type Paymaster = TestPay;
	type Members = TestClub;
	type Salary = ConvertRank<Identity>;
	type RegistrationPeriod = ConstU64<2>;
	type PayoutPeriod = ConstU64<2>;
	type Budget = Budget;
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
		assert!(Salary::last_active(&0).is_err());
		assert_eq!(Salary::status(), None);
	});
}

#[test]
fn can_start() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_eq!(
			Salary::status(),
			Some(StatusType {
				cycle_index: 0,
				cycle_start: 1,
				budget: 10,
				total_registrations: 0,
				total_unregistered_paid: 0,
			})
		);
	});
}

#[test]
fn bump_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		run_to(4);
		assert_noop!(Salary::bump(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);

		run_to(5);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_eq!(
			Salary::status(),
			Some(StatusType {
				cycle_index: 1,
				cycle_start: 5,
				budget: 10,
				total_registrations: 0,
				total_unregistered_paid: 0
			})
		);

		run_to(8);
		assert_noop!(Salary::bump(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);

		BUDGET.with(|b| b.replace(5));
		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_eq!(
			Salary::status(),
			Some(StatusType {
				cycle_index: 2,
				cycle_start: 9,
				budget: 5,
				total_registrations: 0,
				total_unregistered_paid: 0
			})
		);
	});
}

#[test]
fn induct_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));

		assert_noop!(Salary::induct(RuntimeOrigin::signed(1)), Error::<Test>::NotMember);
		set_rank(1, 1);
		assert!(Salary::last_active(&1).is_err());
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		assert_eq!(Salary::last_active(&1).unwrap(), 0);
		assert_noop!(Salary::induct(RuntimeOrigin::signed(1)), Error::<Test>::AlreadyInducted);
	});
}

#[test]
fn unregistered_payment_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_noop!(Salary::induct(RuntimeOrigin::signed(1)), Error::<Test>::NotStarted);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NotInducted);
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		// No claim on the cycle active during induction.
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::TooEarly);
		run_to(3);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);

		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::TooEarly);
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		run_to(8);
		assert_noop!(Salary::bump(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);
		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(11);
		assert_ok!(Salary::payout_other(RuntimeOrigin::signed(1), 10));
		assert_eq!(paid(1), 1);
		assert_eq!(paid(10), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
	});
}

#[test]
fn retry_payment_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		// Payment failed.
		unpay(1, 1);
		set_status(0, PaymentStatus::Failure);

		assert_eq!(paid(1), 0);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);

		// Can't just retry.
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		// Check status.
		assert_ok!(Salary::check_payment(RuntimeOrigin::signed(1)));
		// Allowed to try again.
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);

		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		run_to(8);
		assert_noop!(Salary::bump(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);
		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(11);
		assert_ok!(Salary::payout_other(RuntimeOrigin::signed(1), 10));
		assert_eq!(paid(1), 1);
		assert_eq!(paid(10), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
	});
}

#[test]
fn retry_registered_payment_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		// Payment failed.
		unpay(1, 1);
		set_status(0, PaymentStatus::Failure);

		assert_eq!(paid(1), 0);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 0);

		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		// Check status.
		assert_ok!(Salary::check_payment(RuntimeOrigin::signed(1)));
		// Allowed to try again.
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 0);
	});
}

#[test]
fn retry_payment_later_is_not_allowed() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		// Payment failed.
		unpay(1, 1);
		set_status(0, PaymentStatus::Failure);

		assert_eq!(paid(1), 0);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);

		// Can't just retry.
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);

		// Next cycle.
		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));

		// Payment did fail but now too late to retry.
		assert_noop!(Salary::check_payment(RuntimeOrigin::signed(1)), Error::<Test>::NotCurrent);

		// We do get this cycle's payout, but we must wait for the payout period to start.
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::TooEarly);

		run_to(11);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
	});
}

#[test]
fn retry_payment_later_without_bump_is_allowed() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		// Payment failed.
		unpay(1, 1);
		set_status(0, PaymentStatus::Failure);

		// Next cycle.
		run_to(9);

		// Payment did fail but we can still retry as long as we don't `bump`.
		assert_ok!(Salary::check_payment(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
	});
}

#[test]
fn retry_payment_to_other_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(6);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::payout_other(RuntimeOrigin::signed(1), 10));

		// Payment failed.
		unpay(10, 1);
		set_status(0, PaymentStatus::Failure);

		// Can't just retry.
		assert_noop!(Salary::payout_other(RuntimeOrigin::signed(1), 10), Error::<Test>::NoClaim);
		// Check status.
		assert_ok!(Salary::check_payment(RuntimeOrigin::signed(1)));
		// Allowed to try again.
		assert_ok!(Salary::payout_other(RuntimeOrigin::signed(1), 10));

		assert_eq!(paid(10), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);

		assert_noop!(Salary::payout_other(RuntimeOrigin::signed(1), 10), Error::<Test>::NoClaim);
		run_to(8);
		assert_noop!(Salary::bump(RuntimeOrigin::signed(1)), Error::<Test>::NotYet);
		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		run_to(11);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 1);
		assert_eq!(paid(10), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 1);
	});
}

#[test]
fn registered_payment_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_noop!(Salary::induct(RuntimeOrigin::signed(1)), Error::<Test>::NotStarted);
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NotInducted);
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		// No claim on the cycle active during induction.
		assert_noop!(Salary::register(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);
		run_to(3);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);

		run_to(5);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(1)));
		assert_eq!(Salary::status().unwrap().total_registrations, 1);
		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 1);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 0);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::NoClaim);

		run_to(9);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_eq!(Salary::status().unwrap().total_registrations, 0);
		assert_ok!(Salary::register(RuntimeOrigin::signed(1)));
		assert_eq!(Salary::status().unwrap().total_registrations, 1);
		run_to(11);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_eq!(paid(1), 2);
		assert_eq!(Salary::status().unwrap().total_unregistered_paid, 0);
	});
}

#[test]
fn zero_payment_fails() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		set_rank(1, 0);
		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		run_to(7);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::ClaimZero);
	});
}

#[test]
fn unregistered_bankrupcy_fails_gracefully() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		set_rank(1, 2);
		set_rank(2, 6);
		set_rank(3, 12);

		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(3)));

		run_to(7);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(3)));

		assert_eq!(paid(1), 2);
		assert_eq!(paid(2), 6);
		assert_eq!(paid(3), 2);
	});
}

#[test]
fn registered_bankrupcy_fails_gracefully() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		set_rank(1, 2);
		set_rank(2, 6);
		set_rank(3, 12);

		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(3)));

		run_to(5);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(3)));

		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(3)));

		assert_eq!(paid(1), 1);
		assert_eq!(paid(2), 3);
		assert_eq!(paid(3), 6);
	});
}

#[test]
fn mixed_bankrupcy_fails_gracefully() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		set_rank(1, 2);
		set_rank(2, 6);
		set_rank(3, 12);

		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(3)));

		run_to(5);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(2)));

		run_to(7);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(3)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(1)));

		assert_eq!(paid(1), 2);
		assert_eq!(paid(2), 6);
		assert_eq!(paid(3), 2);
	});
}

#[test]
fn other_mixed_bankrupcy_fails_gracefully() {
	new_test_ext().execute_with(|| {
		assert_ok!(Salary::init(RuntimeOrigin::signed(1)));
		set_rank(1, 2);
		set_rank(2, 6);
		set_rank(3, 12);

		assert_ok!(Salary::induct(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::induct(RuntimeOrigin::signed(3)));

		run_to(5);
		assert_ok!(Salary::bump(RuntimeOrigin::signed(1)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::register(RuntimeOrigin::signed(3)));

		run_to(7);
		assert_noop!(Salary::payout(RuntimeOrigin::signed(1)), Error::<Test>::ClaimZero);
		assert_ok!(Salary::payout(RuntimeOrigin::signed(2)));
		assert_ok!(Salary::payout(RuntimeOrigin::signed(3)));

		assert_eq!(paid(1), 0);
		assert_eq!(paid(2), 3);
		assert_eq!(paid(3), 6);
	});
}
