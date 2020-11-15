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

//! Treasury pallet tests.

#![cfg(test)]

use super::*;
use std::cell::RefCell;
use frame_support::{
	assert_noop, assert_ok, impl_outer_origin, impl_outer_event, parameter_types, weights::Weight,
	traits::{Contains, OnInitialize}
};
use sp_core::H256;
use sp_runtime::{
	Perbill, ModuleId,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, BadOrigin},
};

impl_outer_origin! {
	pub enum Origin for TestRuntime where system = frame_system {}
}

mod tips {
	// Re-export needed for `impl_outer_event!`.
	pub use crate::*;
}

// impl_outer_event! {
// 	pub enum Event for Test {
// 		system<T>,
// 		pallet_balances<T>,
// 		pallet_treasury<T>,
// 		tips<T>,
// 	}
// }

#[derive(Clone, Eq, PartialEq)]
pub struct TestRuntime;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for TestRuntime {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	// type Event = Event;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
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
impl pallet_balances::Trait for TestRuntime {
	type MaxLocks = ();
	type Balance = u64;
	// type Event = Event;
	type Event = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
thread_local! {
	static TEN_TO_FOURTEEN: RefCell<Vec<u128>> = RefCell::new(vec![10,11,12,13,14]);
}
pub struct TenToFourteen;
impl Contains<u128> for TenToFourteen {
	fn sorted_members() -> Vec<u128> {
		TEN_TO_FOURTEEN.with(|v| {
			v.borrow().clone()
		})
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(new: &u128) {
		TEN_TO_FOURTEEN.with(|v| {
			let mut members = v.borrow_mut();
			members.push(*new);
			members.sort();
		})
	}
}
impl ContainsLengthBound for TenToFourteen {
	fn max_len() -> usize {
		TEN_TO_FOURTEEN.with(|v| v.borrow().len())
	}
	fn min_len() -> usize { 0 }
}
parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const ProposalBondMinimum: u64 = 1;
	pub const SpendPeriod: u64 = 2;
	pub const Burn: Permill = Permill::from_percent(50);
	pub const DataDepositPerByte: u64 = 1;
	pub const TreasuryModuleId: ModuleId = ModuleId(*b"py/trsry");
	pub const MaximumReasonLength: u32 = 16384;
}
impl pallet_treasury::Trait<DefaultInstance> for TestRuntime {
	type ModuleId = TreasuryModuleId;
	type Currency = pallet_balances::Module<TestRuntime>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type DataDepositPerByte = DataDepositPerByte;
	// type Event = Event;
	type Event = ();
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type SpendPeriod = SpendPeriod;
	type Burn = Burn;
	type MaximumReasonLength = MaximumReasonLength;
	type BurnDestination = ();  // Just gets burned.
	type WeightInfo = ();
}
parameter_types! {
	pub const TipCountdown: u64 = 1;
	pub const TipFindersFee: Percent = Percent::from_percent(20);
	pub const TipReportDepositBase: u64 = 1;
}
impl Trait for TestRuntime {
	type Tippers = TenToFourteen;
	type TipCountdown = TipCountdown;
	type TipFindersFee = TipFindersFee;
	type TipReportDepositBase = TipReportDepositBase;
	// type Event = Event;
	type Event = ();
	type TipsWeightInfo = ();
}
type System = frame_system::Module<TestRuntime>;
type Balances = pallet_balances::Module<TestRuntime>;
type Treasury = pallet_treasury::Module<TestRuntime, DefaultInstance>;
type TipsModTestInst = Module<TestRuntime>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<TestRuntime>().unwrap();
	pallet_balances::GenesisConfig::<TestRuntime>{
		// Total issuance will be 200 with treasury account initialized at ED.
		balances: vec![(0, 100), (1, 98), (2, 1)],
	}.assimilate_storage(&mut t).unwrap();
	pallet_treasury::GenesisConfig::default().assimilate_storage::<TestRuntime, _>(&mut t).unwrap();
	t.into()
}

// fn last_event() -> RawEvent<u64, u128, H256, DefaultInstance> {
// 	System::events().into_iter().map(|r| r.event)
// 		.filter_map(|e| {
// 			if let Event::treasury(inner) = e { Some(inner) } else { None }
// 		})
// 		.last()
// 		.unwrap()
// }

#[test]
fn genesis_config_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Treasury::pot(), 0);
		assert_eq!(Treasury::proposal_count(), 0);
	});
}

fn tip_hash() -> H256 {
	BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 3u128))
}

#[test]
fn tip_new_cannot_be_used_twice() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		assert_noop!(
			TipsModTestInst::tip_new(Origin::signed(11), b"awesome.dot".to_vec(), 3, 10),
			Error::<TestRuntime, _>::AlreadyKnown
		);
	});
}

#[test]
fn report_awesome_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);

		// other reports don't count.
		assert_noop!(
			TipsModTestInst::report_awesome(Origin::signed(1), b"awesome.dot".to_vec(), 3),
			Error::<TestRuntime, _>::AlreadyKnown
		);

		let h = tip_hash();
		assert_ok!(TipsModTestInst::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(TipsModTestInst::tip(Origin::signed(9), h.clone(), 10), BadOrigin);
		System::set_block_number(2);
		assert_ok!(TipsModTestInst::close_tip(Origin::signed(100), h.into()));
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 102);
		assert_eq!(Balances::free_balance(3), 8);
	});
}

#[test]
fn report_awesome_from_beneficiary_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 0));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);
		let h = BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 0u128));
		assert_ok!(TipsModTestInst::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(TipsModTestInst::close_tip(Origin::signed(100), h.into()));
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 110);
	});
}

#[test]
fn close_tip_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!(TipsModTestInst::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));

		let h = tip_hash();

		// TODO :: re-visit
		// assert_eq!(last_event(), RawEvent::NewTip(h));

		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));

		assert_noop!(TipsModTestInst::close_tip(Origin::signed(0), h.into()), Error::<TestRuntime, _>::StillOpen);

		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10));

		// TODO :: re-visit
		// assert_eq!(last_event(), RawEvent::TipClosing(h));

		assert_noop!(TipsModTestInst::close_tip(Origin::signed(0), h.into()), Error::<TestRuntime, _>::Premature);

		System::set_block_number(2);
		assert_noop!(TipsModTestInst::close_tip(Origin::none(), h.into()), BadOrigin);
		assert_ok!(TipsModTestInst::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);

		// TODO :: re-visit
		// assert_eq!(last_event(), RawEvent::TipClosed(h, 3, 10));

		assert_noop!(TipsModTestInst::close_tip(Origin::signed(100), h.into()), Error::<TestRuntime, _>::UnknownTip);
	});
}

#[test]
fn retract_tip_works() {
	new_test_ext().execute_with(|| {
		// with report awesome
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		let h = tip_hash();
		assert_ok!(TipsModTestInst::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(TipsModTestInst::retract_tip(Origin::signed(10), h.clone()), Error::<TestRuntime, _>::NotFinder);
		assert_ok!(TipsModTestInst::retract_tip(Origin::signed(0), h.clone()));
		System::set_block_number(2);
		assert_noop!(TipsModTestInst::close_tip(Origin::signed(0), h.into()), Error::<TestRuntime, _>::UnknownTip);

		// with tip new
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		let h = tip_hash();
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(TipsModTestInst::retract_tip(Origin::signed(0), h.clone()), Error::<TestRuntime, _>::NotFinder);
		assert_ok!(TipsModTestInst::retract_tip(Origin::signed(10), h.clone()));
		System::set_block_number(2);
		assert_noop!(TipsModTestInst::close_tip(Origin::signed(10), h.into()), Error::<TestRuntime, _>::UnknownTip);
	});
}

#[test]
fn tip_median_calculation_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 0));
		let h = tip_hash();
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 1000000));
		System::set_block_number(2);
		assert_ok!(TipsModTestInst::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn tip_changing_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(TipsModTestInst::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10000));
		let h = tip_hash();
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 10000));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 10000));
		assert_ok!(TipsModTestInst::tip(Origin::signed(13), h.clone(), 0));
		assert_ok!(TipsModTestInst::tip(Origin::signed(14), h.clone(), 0));
		assert_ok!(TipsModTestInst::tip(Origin::signed(12), h.clone(), 1000));
		assert_ok!(TipsModTestInst::tip(Origin::signed(11), h.clone(), 100));
		assert_ok!(TipsModTestInst::tip(Origin::signed(10), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(TipsModTestInst::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn test_last_reward_migration() {
	use sp_storage::Storage;

	let mut s = Storage::default();

	#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
	pub struct OldOpenTip<
		AccountId: Parameter,
		Balance: Parameter,
		BlockNumber: Parameter,
		Hash: Parameter,
	> {
		/// The hash of the reason for the tip. The reason should be a human-readable UTF-8 encoded string. A URL would be
		/// sensible.
		reason: Hash,
		/// The account to be tipped.
		who: AccountId,
		/// The account who began this tip and the amount held on deposit.
		finder: Option<(AccountId, Balance)>,
		/// The block number at which this tip will close if `Some`. If `None`, then no closing is
		/// scheduled.
		closes: Option<BlockNumber>,
		/// The members who have voted for this tip. Sorted by AccountId.
		tips: Vec<(AccountId, Balance)>,
	}

	let reason1 = BlakeTwo256::hash(b"reason1");
	let hash1 = BlakeTwo256::hash_of(&(reason1, 10u64));

	let old_tip_finder = OldOpenTip::<u128, u64, u64, H256> {
		reason: reason1,
		who: 10,
		finder: Some((20, 30)),
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)]
	};

	let reason2 = BlakeTwo256::hash(b"reason2");
	let hash2 = BlakeTwo256::hash_of(&(reason2, 20u64));

	let old_tip_no_finder = OldOpenTip::<u128, u64, u64, H256> {
		reason: reason2,
		who: 20,
		finder: None,
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)]
	};

	let data = vec![
		(
			TipsMap::<TestRuntime>::hashed_key_for(hash1),
			old_tip_finder.encode().to_vec()
		),
		(
			TipsMap::<TestRuntime>::hashed_key_for(hash2),
			old_tip_no_finder.encode().to_vec()
		),
	];

	s.top = data.into_iter().collect();
	sp_io::TestExternalities::new(s).execute_with(|| {
		TipsModTestInst::migrate_retract_tip_for_tip_new();

		// Test w/ finder
		assert_eq!(
			TipsMap::<TestRuntime>::get(hash1),
			Some(OpenTip {
				reason: reason1,
				who: 10,
				finder: 20,
				deposit: 30,
				closes: Some(13),
				tips: vec![(40, 50), (60, 70)],
				finders_fee: true,
			})
		);

		// Test w/o finder
		assert_eq!(
			TipsMap::<TestRuntime>::get(hash2),
			Some(OpenTip {
				reason: reason2,
				who: 20,
				finder: Default::default(),
				deposit: 0,
				closes: Some(13),
				tips: vec![(40, 50), (60, 70)],
				finders_fee: false,
			})
		);
	});
}

#[test]
fn genesis_funding_works() {
	let mut t = frame_system::GenesisConfig::default().build_storage::<TestRuntime>().unwrap();
	let initial_funding = 100;
	pallet_balances::GenesisConfig::<TestRuntime>{
		// Total issuance will be 200 with treasury account initialized with 100.
		balances: vec![(0, 100), (Treasury::account_id(), initial_funding)],
	}.assimilate_storage(&mut t).unwrap();
	pallet_treasury::GenesisConfig::default().assimilate_storage::<TestRuntime, _>(&mut t).unwrap();
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), initial_funding);
		assert_eq!(Treasury::pot(), initial_funding - Balances::minimum_balance());
	});
}
