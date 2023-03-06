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
	assert_noop, assert_ok, ord_parameter_types,
	pallet_prelude::Weight,
	parameter_types,
	traits::{tokens::GetSalary, ConstU32, ConstU64, Everything, IsInVec, TryMapSuccess},
};
use frame_system::EnsureSignedBy;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, TryMorphInto},
	DispatchError, DispatchResult,
};
use sp_std::cell::RefCell;

use super::*;
use crate as pallet_core_fellowship;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		CoreFellowship: pallet_core_fellowship::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::from_parts(1_000_000, u64::max_value()));
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
	pub static CLUB: RefCell<BTreeMap<u64, u16>> = RefCell::new(BTreeMap::new());
}

pub struct TestClub;
impl RankedMembers for TestClub {
	type AccountId = u64;
	type Rank = u16;
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
		CLUB.with(|club| match Self::rank_of(who) {
			None => Err(sp_runtime::DispatchError::Unavailable),
			Some(0) => {
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

fn set_rank(who: u64, rank: u16) {
	CLUB.with(|club| club.borrow_mut().insert(who, rank));
}

fn unrank(who: u64) {
	CLUB.with(|club| club.borrow_mut().remove(&who));
}

parameter_types! {
	pub ZeroToNine: Vec<u64> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
}
ord_parameter_types! {
	pub const One: u64 = 1;
}

impl Config for Test {
	type WeightInfo = ();
	type RuntimeEvent = RuntimeEvent;
	type Members = TestClub;
	type Balance = u64;
	type ParamsOrigin = EnsureSignedBy<One, u64>;
	type InductOrigin = EnsureInducted<Test, (), 1>;
	type ApproveOrigin = TryMapSuccess<EnsureSignedBy<IsInVec<ZeroToNine>, u64>, TryMorphInto<u16>>;
	type PromoteOrigin = TryMapSuccess<EnsureSignedBy<IsInVec<ZeroToNine>, u64>, TryMorphInto<u16>>;
	type EvidenceSize = ConstU32<1024>;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		let params = ParamsType {
			active_salary: [10, 20, 30, 40, 50, 60, 70, 80, 90],
			passive_salary: [1, 2, 3, 4, 5, 6, 7, 8, 9],
			demotion_period: [2, 4, 6, 8, 10, 12, 14, 16, 18],
			min_promotion_period: [3, 6, 9, 12, 15, 18, 21, 24, 27],
			offboard_timeout: 1,
		};
		assert_ok!(CoreFellowship::set_params(signed(1), Box::new(params)));
		System::set_block_number(1);
	});
	ext
}

fn next_block() {
	System::set_block_number(System::block_number() + 1);
}

fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

fn signed(who: u64) -> RuntimeOrigin {
	RuntimeOrigin::signed(who)
}

fn next_demotion(who: u64) -> u64 {
	let member = Member::<Test>::get(who).unwrap();
	let demotion_period = Params::<Test>::get().demotion_period;
	member.last_proof + demotion_period[TestClub::rank_of(&who).unwrap() as usize - 1]
}

#[test]
fn basic_stuff() {
	new_test_ext().execute_with(|| {
		assert_eq!(CoreFellowship::rank_to_index(0), None);
		assert_eq!(CoreFellowship::rank_to_index(1), Some(0));
		assert_eq!(CoreFellowship::rank_to_index(9), Some(8));
		assert_eq!(CoreFellowship::rank_to_index(10), None);
		assert_eq!(CoreFellowship::get_salary(0, &1), 0);
	});
}

#[test]
fn set_params_works() {
	new_test_ext().execute_with(|| {
		let params = ParamsType {
			active_salary: [10, 20, 30, 40, 50, 60, 70, 80, 90],
			passive_salary: [1, 2, 3, 4, 5, 6, 7, 8, 9],
			demotion_period: [1, 2, 3, 4, 5, 6, 7, 8, 9],
			min_promotion_period: [1, 2, 3, 4, 5, 10, 15, 20, 30],
			offboard_timeout: 1,
		};
		assert_noop!(
			CoreFellowship::set_params(signed(2), Box::new(params.clone())),
			DispatchError::BadOrigin
		);
		assert_ok!(CoreFellowship::set_params(signed(1), Box::new(params)));
	});
}

#[test]
fn induct_works() {
	new_test_ext().execute_with(|| {
		set_rank(0, 0);
		assert_ok!(CoreFellowship::import(signed(0)));
		set_rank(1, 1);
		assert_ok!(CoreFellowship::import(signed(1)));

		assert_noop!(CoreFellowship::induct(signed(10), 10), DispatchError::BadOrigin);
		assert_noop!(CoreFellowship::induct(signed(0), 10), DispatchError::BadOrigin);
		assert_ok!(CoreFellowship::induct(signed(1), 10));
		assert_noop!(CoreFellowship::induct(signed(1), 10), Error::<Test>::AlreadyInducted);
	});
}

#[test]
fn promote_works() {
	new_test_ext().execute_with(|| {
		set_rank(1, 1);
		assert_ok!(CoreFellowship::import(signed(1)));
		assert_noop!(CoreFellowship::promote(signed(1), 10, 1), Error::<Test>::Unranked);

		assert_ok!(CoreFellowship::induct(signed(1), 10));
		assert_noop!(CoreFellowship::promote(signed(10), 10, 1), DispatchError::BadOrigin);
		assert_noop!(CoreFellowship::promote(signed(0), 10, 1), Error::<Test>::NoPermission);
		assert_noop!(CoreFellowship::promote(signed(3), 10, 2), Error::<Test>::UnexpectedRank);
		run_to(3);
		assert_noop!(CoreFellowship::promote(signed(1), 10, 1), Error::<Test>::TooSoon);
		run_to(4);
		assert_ok!(CoreFellowship::promote(signed(1), 10, 1));
		set_rank(11, 0);
		assert_noop!(CoreFellowship::promote(signed(1), 11, 1), Error::<Test>::NotTracked);
	});
}

#[test]
fn sync_works() {
	new_test_ext().execute_with(|| {
		set_rank(10, 5);
		assert_noop!(CoreFellowship::approve(signed(4), 10, 5), Error::<Test>::NoPermission);
		assert_noop!(CoreFellowship::approve(signed(6), 10, 6), Error::<Test>::UnexpectedRank);
		assert_ok!(CoreFellowship::import(signed(10)));
		assert!(Member::<Test>::contains_key(10));
		assert_eq!(next_demotion(10), 11);
	});
}

#[test]
fn auto_demote_works() {
	new_test_ext().execute_with(|| {
		set_rank(10, 5);
		assert_ok!(CoreFellowship::import(signed(10)));

		run_to(10);
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NothingDoing);
		run_to(11);
		assert_ok!(CoreFellowship::bump(signed(0), 10));
		assert_eq!(TestClub::rank_of(&10), Some(4));
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NothingDoing);
		assert_eq!(next_demotion(10), 19);
	});
}

#[test]
fn auto_demote_offboard_works() {
	new_test_ext().execute_with(|| {
		set_rank(10, 1);
		assert_ok!(CoreFellowship::import(signed(10)));

		run_to(3);
		assert_ok!(CoreFellowship::bump(signed(0), 10));
		assert_eq!(TestClub::rank_of(&10), Some(0));
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NothingDoing);
		run_to(4);
		assert_ok!(CoreFellowship::bump(signed(0), 10));
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NotTracked);
	});
}

#[test]
fn offboard_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(CoreFellowship::offboard(signed(0), 10), Error::<Test>::NotTracked);
		set_rank(10, 0);
		assert_noop!(CoreFellowship::offboard(signed(0), 10), Error::<Test>::Ranked);

		assert_ok!(CoreFellowship::import(signed(10)));
		assert_noop!(CoreFellowship::offboard(signed(0), 10), Error::<Test>::Ranked);

		unrank(10);
		assert_ok!(CoreFellowship::offboard(signed(0), 10));
		assert_noop!(CoreFellowship::offboard(signed(0), 10), Error::<Test>::NotTracked);
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NotTracked);
	});
}

#[test]
fn proof_postpones_auto_demote() {
	new_test_ext().execute_with(|| {
		set_rank(10, 5);
		assert_ok!(CoreFellowship::import(signed(10)));

		run_to(11);
		assert_ok!(CoreFellowship::approve(signed(5), 10, 5));
		assert_eq!(next_demotion(10), 21);
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NothingDoing);
	});
}

#[test]
fn promote_postpones_auto_demote() {
	new_test_ext().execute_with(|| {
		set_rank(10, 5);
		assert_ok!(CoreFellowship::import(signed(10)));

		run_to(19);
		assert_ok!(CoreFellowship::promote(signed(6), 10, 6));
		assert_eq!(next_demotion(10), 31);
		assert_noop!(CoreFellowship::bump(signed(0), 10), Error::<Test>::NothingDoing);
	});
}

#[test]
fn get_salary_works() {
	new_test_ext().execute_with(|| {
		for i in 1..=9u64 {
			set_rank(10 + i, i as u16);
			assert_ok!(CoreFellowship::import(signed(10 + i)));
			assert_eq!(CoreFellowship::get_salary(i as u16, &(10 + i)), i * 10);
		}
	});
}

#[test]
fn active_changing_get_salary_works() {
	new_test_ext().execute_with(|| {
		for i in 1..=9u64 {
			set_rank(10 + i, i as u16);
			assert_ok!(CoreFellowship::import(signed(10 + i)));
			assert_ok!(CoreFellowship::set_active(signed(10 + i), false));
			assert_eq!(CoreFellowship::get_salary(i as u16, &(10 + i)), i);
			assert_ok!(CoreFellowship::set_active(signed(10 + i), true));
			assert_eq!(CoreFellowship::get_salary(i as u16, &(10 + i)), i * 10);
		}
	});
}
