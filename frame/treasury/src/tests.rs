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
	pub enum Origin for Test where system = frame_system {}
}


mod treasury {
	// Re-export needed for `impl_outer_event!`.
	pub use super::super::*;
}

impl_outer_event! {
	pub enum Event for Test {
		system<T>,
		pallet_balances<T>,
		treasury<T>,
	}
}


#[derive(Clone, Eq, PartialEq)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type AvailableBlockRatio = AvailableBlockRatio;
	type MaximumBlockLength = MaximumBlockLength;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
thread_local! {
	static TEN_TO_FOURTEEN: RefCell<Vec<u64>> = RefCell::new(vec![10,11,12,13,14]);
}
pub struct TenToFourteen;
impl Contains<u64> for TenToFourteen {
	fn sorted_members() -> Vec<u64> {
		TEN_TO_FOURTEEN.with(|v| {
			v.borrow().clone()
		})
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(new: &u64) {
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
	pub const TipCountdown: u64 = 1;
	pub const TipFindersFee: Percent = Percent::from_percent(20);
	pub const TipReportDepositBase: u64 = 1;
	pub const TipReportDepositPerByte: u64 = 1;
	pub const TreasuryModuleId: ModuleId = ModuleId(*b"py/trsry");
}
impl Trait for Test {
	type ModuleId = TreasuryModuleId;
	type Currency = pallet_balances::Module<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u64>;
	type RejectOrigin = frame_system::EnsureRoot<u64>;
	type Tippers = TenToFourteen;
	type TipCountdown = TipCountdown;
	type TipFindersFee = TipFindersFee;
	type TipReportDepositBase = TipReportDepositBase;
	type TipReportDepositPerByte = TipReportDepositPerByte;
	type Event = Event;
	type ProposalRejection = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type SpendPeriod = SpendPeriod;
	type Burn = Burn;
	type BurnDestination = ();  // Just gets burned.
	type WeightInfo = ();
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Treasury = Module<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		// Total issuance will be 200 with treasury account initialized at ED.
		balances: vec![(0, 100), (1, 98), (2, 1)],
	}.assimilate_storage(&mut t).unwrap();
	GenesisConfig::default().assimilate_storage::<Test>(&mut t).unwrap();
	t.into()
}

#[test]
fn genesis_config_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Treasury::pot(), 0);
		assert_eq!(Treasury::proposal_count(), 0);
	});
}

fn tip_hash() -> H256 {
	BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 3u64))
}

#[test]
fn tip_new_cannot_be_used_twice() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		assert_noop!(
			Treasury::tip_new(Origin::signed(11), b"awesome.dot".to_vec(), 3, 10),
			Error::<Test>::AlreadyKnown
		);
	});
}

#[test]
fn report_awesome_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);

		// other reports don't count.
		assert_noop!(
			Treasury::report_awesome(Origin::signed(1), b"awesome.dot".to_vec(), 3),
			Error::<Test>::AlreadyKnown
		);

		let h = tip_hash();
		assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Treasury::tip(Origin::signed(9), h.clone(), 10), BadOrigin);
		System::set_block_number(2);
		assert_ok!(Treasury::close_tip(Origin::signed(100), h.into()));
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 102);
		assert_eq!(Balances::free_balance(3), 8);
	});
}

#[test]
fn report_awesome_from_beneficiary_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 0));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);
		let h = BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 0u64));
		assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(Treasury::close_tip(Origin::signed(100), h.into()));
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

		assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));

		let h = tip_hash();

		assert_eq!(
			System::events().into_iter().map(|r| r.event)
				.filter_map(|e| {
					if let Event::treasury(inner) = e { Some(inner) } else { None }
				})
				.last()
				.unwrap(),
			RawEvent::NewTip(h),
		);

		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));

		assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::StillOpen);

		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));

		assert_eq!(
			System::events().into_iter().map(|r| r.event)
				.filter_map(|e| {
					if let Event::treasury(inner) = e { Some(inner) } else { None }
				})
				.last()
				.unwrap(),
			RawEvent::TipClosing(h),
		);

		assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::Premature);

		System::set_block_number(2);
		assert_noop!(Treasury::close_tip(Origin::none(), h.into()), BadOrigin);
		assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);

		assert_eq!(
			System::events().into_iter().map(|r| r.event)
				.filter_map(|e| {
					if let Event::treasury(inner) = e { Some(inner) } else { None }
				})
				.last()
				.unwrap(),
			RawEvent::TipClosed(h, 3, 10),
		);

		assert_noop!(Treasury::close_tip(Origin::signed(100), h.into()), Error::<Test>::UnknownTip);
	});
}

#[test]
fn retract_tip_works() {
	new_test_ext().execute_with(|| {
		// with report awesome
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		let h = tip_hash();
		assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Treasury::retract_tip(Origin::signed(10), h.clone()), Error::<Test>::NotFinder);
		assert_ok!(Treasury::retract_tip(Origin::signed(0), h.clone()));
		System::set_block_number(2);
		assert_noop!(Treasury::close_tip(Origin::signed(0), h.into()), Error::<Test>::UnknownTip);

		// with tip new
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		let h = tip_hash();
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Treasury::retract_tip(Origin::signed(0), h.clone()), Error::<Test>::NotFinder);
		assert_ok!(Treasury::retract_tip(Origin::signed(10), h.clone()));
		System::set_block_number(2);
		assert_noop!(Treasury::close_tip(Origin::signed(10), h.into()), Error::<Test>::UnknownTip);
	});
}

#[test]
fn tip_median_calculation_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 0));
		let h = tip_hash();
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 1000000));
		System::set_block_number(2);
		assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn tip_changing_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Treasury::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10000));
		let h = tip_hash();
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 10000));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 10000));
		assert_ok!(Treasury::tip(Origin::signed(13), h.clone(), 0));
		assert_ok!(Treasury::tip(Origin::signed(14), h.clone(), 0));
		assert_ok!(Treasury::tip(Origin::signed(12), h.clone(), 1000));
		assert_ok!(Treasury::tip(Origin::signed(11), h.clone(), 100));
		assert_ok!(Treasury::tip(Origin::signed(10), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(Treasury::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn minting_works() {
	new_test_ext().execute_with(|| {
		// Check that accumulate works when we have Some value in Dummy already.
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);
	});
}

#[test]
fn spend_proposal_takes_min_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
		assert_eq!(Balances::free_balance(0), 99);
		assert_eq!(Balances::reserved_balance(0), 1);
	});
}

#[test]
fn spend_proposal_takes_proportional_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 5);
	});
}

#[test]
fn spend_proposal_fails_when_proposer_poor() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Treasury::propose_spend(Origin::signed(2), 100, 3),
			Error::<Test>::InsufficientProposersBalance,
		);
	});
}

#[test]
fn accepted_spend_proposal_ignored_outside_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 0));

		<Treasury as OnInitialize<u64>>::on_initialize(1);
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Treasury::pot(), 100);
	});
}

#[test]
fn unused_pot_should_diminish() {
	new_test_ext().execute_with(|| {
		let init_total_issuance = Balances::total_issuance();
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Balances::total_issuance(), init_total_issuance + 100);

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 50);
		assert_eq!(Balances::total_issuance(), init_total_issuance + 50);
	});
}

#[test]
fn rejected_spend_proposal_ignored_on_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::reject_proposal(Origin::root(), 0));

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Treasury::pot(), 50);
	});
}

#[test]
fn reject_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::reject_proposal(Origin::root(), 0));
		assert_noop!(Treasury::reject_proposal(Origin::root(), 0), Error::<Test>::InvalidProposalIndex);
	});
}

#[test]
fn reject_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(Treasury::reject_proposal(Origin::root(), 0), Error::<Test>::InvalidProposalIndex);
	});
}

#[test]
fn accept_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(Treasury::approve_proposal(Origin::root(), 0), Error::<Test>::InvalidProposalIndex);
	});
}

#[test]
fn accept_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::reject_proposal(Origin::root(), 0));
		assert_noop!(Treasury::approve_proposal(Origin::root(), 0), Error::<Test>::InvalidProposalIndex);
	});
}

#[test]
fn accepted_spend_proposal_enacted_on_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 0));

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(3), 100);
		assert_eq!(Treasury::pot(), 0);
	});
}

#[test]
fn pot_underflow_should_not_diminish() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 150, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 0));

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		let _ = Balances::deposit_into_existing(&Treasury::account_id(), 100).unwrap();
		<Treasury as OnInitialize<u64>>::on_initialize(4);
		assert_eq!(Balances::free_balance(3), 150); // Fund has been spent
		assert_eq!(Treasury::pot(), 25); // Pot has finally changed
	});
}

// Treasury account doesn't get deleted if amount approved to spend is all its free balance.
// i.e. pot should not include existential deposit needed for account survival.
#[test]
fn treasury_account_doesnt_get_deleted() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);
		let treasury_balance = Balances::free_balance(&Treasury::account_id());

		assert_ok!(Treasury::propose_spend(Origin::signed(0), treasury_balance, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 0));

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		assert_ok!(Treasury::propose_spend(Origin::signed(0), Treasury::pot(), 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 1));

		<Treasury as OnInitialize<u64>>::on_initialize(4);
		assert_eq!(Treasury::pot(), 0); // Pot is emptied
		assert_eq!(Balances::free_balance(Treasury::account_id()), 1); // but the account is still there
	});
}

// In case treasury account is not existing then it works fine.
// This is useful for chain that will just update runtime.
#[test]
fn inexistent_account_works() {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		balances: vec![(0, 100), (1, 99), (2, 1)],
	}.assimilate_storage(&mut t).unwrap();
	// Treasury genesis config is not build thus treasury account does not exist
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), 0); // Account does not exist
		assert_eq!(Treasury::pot(), 0); // Pot is empty

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 99, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 0));
		assert_ok!(Treasury::propose_spend(Origin::signed(0), 1, 3));
		assert_ok!(Treasury::approve_proposal(Origin::root(), 1));
		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 0); // Pot hasn't changed
		assert_eq!(Balances::free_balance(3), 0); // Balance of `3` hasn't changed

		Balances::make_free_balance_be(&Treasury::account_id(), 100);
		assert_eq!(Treasury::pot(), 99); // Pot now contains funds
		assert_eq!(Balances::free_balance(Treasury::account_id()), 100); // Account does exist

		<Treasury as OnInitialize<u64>>::on_initialize(4);

		assert_eq!(Treasury::pot(), 0); // Pot has changed
		assert_eq!(Balances::free_balance(3), 99); // Balance of `3` has changed
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

	let old_tip_finder = OldOpenTip::<u64, u64, u64, H256> {
		reason: reason1,
		who: 10,
		finder: Some((20, 30)),
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)]
	};

	let reason2 = BlakeTwo256::hash(b"reason2");
	let hash2 = BlakeTwo256::hash_of(&(reason2, 20u64));

	let old_tip_no_finder = OldOpenTip::<u64, u64, u64, H256> {
		reason: reason2,
		who: 20,
		finder: None,
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)]
	};

	let data = vec![
		(
			Tips::<Test>::hashed_key_for(hash1),
			old_tip_finder.encode().to_vec()
		),
		(
			Tips::<Test>::hashed_key_for(hash2),
			old_tip_no_finder.encode().to_vec()
		),
	];

	s.top = data.into_iter().collect();
	sp_io::TestExternalities::new(s).execute_with(|| {
		Treasury::migrate_retract_tip_for_tip_new();

		// Test w/ finder
		assert_eq!(
			Tips::<Test>::get(hash1),
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
			Tips::<Test>::get(hash2),
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
