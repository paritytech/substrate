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
	pallet_prelude::Weight,
	parameter_types,
	traits::{ConstU32, ConstU64, Everything, IsInVec, TryMapSuccess, tokens::GetSalary}, ord_parameter_types, assert_noop, assert_ok,
};
use frame_system::EnsureSignedBy;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, TryMorphInto},
	DispatchResult, DispatchError,
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

fn set_rank(who: u64, rank: u16) {
	CLUB.with(|club| club.borrow_mut().insert(who, rank));
}

parameter_types! {
	pub OneToNine: Vec<u64> = vec![1u64, 2, 3, 4, 5, 6, 7, 8, 9];
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
	type ProofOrigin = TryMapSuccess<EnsureSignedBy<IsInVec<OneToNine>, u64>, TryMorphInto<u16>>;
	type PromoteOrigin = TryMapSuccess<EnsureSignedBy<IsInVec<OneToNine>, u64>, TryMorphInto<u16>>;
	type ApprovePeriod = ConstU64<2>;
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

fn signed(who: u64) -> RuntimeOrigin {
	RuntimeOrigin::signed(who)
}

#[test]
fn basic_stuff() {
	new_test_ext().execute_with(|| {
		assert_eq!(CoreFellowship::rank_to_index(0), None);
		assert_eq!(CoreFellowship::rank_to_index(1), Some(0));
		assert_eq!(CoreFellowship::rank_to_index(9), Some(8));
		assert_eq!(CoreFellowship::rank_to_index(10), None);
		assert_noop!(CoreFellowship::induct(signed(1), 1), Error::<Test>::NotMember);
		assert_eq!(CoreFellowship::get_salary(0, &1), 0);
	});
}

#[test]
fn set_params_works() {
	new_test_ext().execute_with(|| {
		let params = ParamsType {
			active_salary: [10, 20, 30, 40, 50, 60, 70, 80, 90],
			passive_salary: [1, 2, 3, 4, 5, 6, 7, 8, 9],
			demotion_period: [3, 3, 3, 6, 6, 6, 1000, 1000, 1000],
			min_promotion_period: [1, 1, 1, 1, 2, 2, 6, 10, 20],
		};
		assert_noop!(CoreFellowship::set_params(signed(2), params.clone()), DispatchError::BadOrigin);
		assert_ok!(CoreFellowship::set_params(signed(1), params));
	});
}

#[test]
fn set_params_works() {
	new_test_ext().execute_with(|| {
		let params = ParamsType {
			active_salary: [10, 20, 30, 40, 50, 60, 70, 80, 90],
			passive_salary: [1, 2, 3, 4, 5, 6, 7, 8, 9],
			demotion_period: [3, 3, 3, 6, 6, 6, 1000, 1000, 1000],
			min_promotion_period: [1, 1, 1, 1, 2, 2, 6, 10, 20],
		};
		assert_noop!(CoreFellowship::set_params(signed(2), params.clone()), DispatchError::BadOrigin);
		assert_ok!(CoreFellowship::set_params(signed(1), params));
	});
}
