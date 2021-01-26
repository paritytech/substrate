// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! bounties pallet tests.

#![cfg(test)]

use super::*;
use std::cell::RefCell;

use frame_support::{
	assert_noop, assert_ok, impl_outer_origin, parameter_types, weights::Weight,
	impl_outer_event, traits::{OnInitialize}
};

use sp_core::H256;
use sp_runtime::{
	Perbill, ModuleId,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, BadOrigin},
	DispatchError,
};

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

mod bounties {
	// Re-export needed for `impl_outer_event!`.
	pub use crate::*;
}

impl_outer_event! {
	pub enum Event for Test {
		system<T>,
		pallet_balances<T>,
		pallet_treasury<T>,
		bounties<T>,
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
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
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
	type SS58Prefix = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
thread_local! {
	static TEN_TO_FOURTEEN: RefCell<Vec<u128>> = RefCell::new(vec![10,11,12,13,14]);
}
parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const ProposalBondMinimum: u64 = 1;
	pub const SpendPeriod: u64 = 2;
	pub const Burn: Permill = Permill::from_percent(50);
	pub const DataDepositPerByte: u64 = 1;
	pub const TreasuryModuleId: ModuleId = ModuleId(*b"py/trsry");
}
// impl pallet_treasury::Config for Test {
impl pallet_treasury::Config for Test {
	type ModuleId = TreasuryModuleId;
	type Currency = pallet_balances::Module<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type Event = Event;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type SpendPeriod = SpendPeriod;
	type Burn = Burn;
	type BurnDestination = ();  // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = Bounties;
}
parameter_types! {
	pub const BountyDepositBase: u64 = 80;
	pub const BountyDepositPayoutDelay: u64 = 3;
	pub const BountyUpdatePeriod: u32 = 20;
	pub const BountyCuratorDeposit: Permill = Permill::from_percent(50);
	pub const BountyValueMinimum: u64 = 1;
	pub const MaximumReasonLength: u32 = 16384;
	pub const MaxSubBountyCount: u32 = 3;
}
impl Config for Test {
	type Event = Event;
	type BountyDepositBase = BountyDepositBase;
	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;
	type BountyUpdatePeriod = BountyUpdatePeriod;
	type BountyCuratorDeposit = BountyCuratorDeposit;
	type BountyValueMinimum = BountyValueMinimum;
	type DataDepositPerByte = DataDepositPerByte;
	type MaximumReasonLength = MaximumReasonLength;
	type MaxSubBountyCount = MaxSubBountyCount;
	type WeightInfo = ();
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type Treasury = pallet_treasury::Module<Test>;
type Bounties = Module<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test>{
		// Total issuance will be 200 with treasury account initialized at ED.
		balances: vec![(0, 100), (1, 98), (2, 1)],
	}.assimilate_storage(&mut t).unwrap();
	pallet_treasury::GenesisConfig::default().assimilate_storage::<Test, _>(&mut t).unwrap();
	t.into()
}

fn last_event() -> RawEvent<u64, u128> {
	System::events().into_iter().map(|r| r.event)
		.filter_map(|e| {
			if let Event::bounties(inner) = e { Some(inner) } else { None }
		})
		.last()
		.unwrap()
}

#[test]
fn genesis_config_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Treasury::pot(), 0);
		assert_eq!(Treasury::proposal_count(), 0);
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
		assert_noop!(Treasury::reject_proposal(Origin::root(), 0), Error::<Test>::InvalidIndex);
	});
}

#[test]
fn reject_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(Treasury::reject_proposal(Origin::root(), 0), Error::<Test>::InvalidIndex);
	});
}

#[test]
fn accept_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(Treasury::approve_proposal(Origin::root(), 0), Error::<Test>::InvalidIndex);
	});
}

#[test]
fn accept_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Treasury::propose_spend(Origin::signed(0), 100, 3));
		assert_ok!(Treasury::reject_proposal(Origin::root(), 0));
		assert_noop!(Treasury::approve_proposal(Origin::root(), 0), Error::<Test>::InvalidIndex);
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
fn propose_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 10, b"1234567890".to_vec()));

		assert_eq!(last_event(), RawEvent::BountyProposed(0));

		let deposit: u64 = 85 + 5;
		assert_eq!(Balances::reserved_balance(0), deposit);
		assert_eq!(Balances::free_balance(0), 100 - deposit);

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 0,
			curator_deposit: 0,
			value: 10,
			bond: deposit,
			status: BountyStatus::Proposed,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Bounties::bounty_descriptions(0).unwrap(), b"1234567890".to_vec());

		assert_eq!(Bounties::bounty_count(), 1);
	});
}

#[test]
fn propose_bounty_validation_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_noop!(
			Bounties::propose_bounty(Origin::signed(1), 0, [0; 17_000].to_vec()),
			Error::<Test>::ReasonTooBig
		);

		assert_noop!(
			Bounties::propose_bounty(Origin::signed(1), 10, b"12345678901234567890".to_vec()),
			Error::<Test>::InsufficientProposersBalance
		);

		assert_noop!(
			Bounties::propose_bounty(Origin::signed(1), 0, b"12345678901234567890".to_vec()),
			Error::<Test>::InvalidValue
		);
	});
}

#[test]
fn close_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_noop!(Bounties::close_bounty(Origin::root(), 0), Error::<Test>::InvalidIndex);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 10, b"12345".to_vec()));

		assert_ok!(Bounties::close_bounty(Origin::root(), 0));

		let deposit: u64 = 80 + 5;

		assert_eq!(last_event(), RawEvent::BountyRejected(0, deposit));

		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 100 - deposit);

		assert_eq!(Bounties::bounties(0), None);
		assert!(!pallet_treasury::Proposals::<Test>::contains_key(0));

		assert_eq!(Bounties::bounty_descriptions(0), None);
	});
}

#[test]
fn approve_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_noop!(Bounties::approve_bounty(Origin::root(), 0), Error::<Test>::InvalidIndex);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		let deposit: u64 = 80 + 5;

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 0,
			value: 50,
			curator_deposit: 0,
			bond: deposit,
			status: BountyStatus::Approved,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});
		assert_eq!(Bounties::bounty_approvals(), vec![0]);

		assert_noop!(Bounties::close_bounty(Origin::root(), 0), Error::<Test>::UnexpectedStatus);

		// deposit not returned yet
		assert_eq!(Balances::reserved_balance(0), deposit);
		assert_eq!(Balances::free_balance(0), 100 - deposit);

		<Treasury as OnInitialize<u64>>::on_initialize(2);

		// return deposit
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 100);

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 0,
			curator_deposit: 0,
			value: 50,
			bond: deposit,
			status: BountyStatus::Funded,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Treasury::pot(), 100 - 50 - 25); // burn 25
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 50);
	});
}

#[test]
fn assign_curator_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_noop!(Bounties::propose_curator(Origin::root(), 0, 4, 4), Error::<Test>::InvalidIndex);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_noop!(Bounties::propose_curator(Origin::root(), 0, 4, 50), Error::<Test>::InvalidFee);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::CuratorProposed {
				curator: 4,
			},
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_noop!(Bounties::accept_curator(Origin::signed(1), 0), Error::<Test>::RequireCurator);
		assert_noop!(Bounties::accept_curator(Origin::signed(4), 0), pallet_balances::Error::<Test, _>::InsufficientBalance);

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 2,
			value: 50,
			bond: 85,
			status: BountyStatus::Active {
				curator: 4,
				update_due: 22,
			},
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Balances::free_balance(&4), 8);
		assert_eq!(Balances::reserved_balance(&4), 2);
	});
}

#[test]
fn unassign_curator_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		assert_noop!(Bounties::unassign_curator(Origin::signed(1), 0), BadOrigin);

		assert_ok!(Bounties::unassign_curator(Origin::signed(4), 0));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::Funded,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_ok!(Bounties::unassign_curator(Origin::root(), 0));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::Funded,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Balances::free_balance(&4), 8);
		assert_eq!(Balances::reserved_balance(&4), 0); // slashed 2
	});
}


#[test]
fn award_and_claim_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&4, 10);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));
		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_eq!(Balances::free_balance(4), 8); // inital 10 - 2 deposit

		assert_noop!(Bounties::award_bounty(Origin::signed(1), 0, 3), Error::<Test>::RequireCurator);

		assert_ok!(Bounties::award_bounty(Origin::signed(4), 0, 3));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 2,
			value: 50,
			bond: 85,
			status: BountyStatus::PendingPayout {
				curator: 4,
				beneficiary: 3,
				unlock_at: 5
			},
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_noop!(Bounties::claim_bounty(Origin::signed(1), 0), Error::<Test>::Premature);

		System::set_block_number(5);
		<Treasury as OnInitialize<u64>>::on_initialize(5);

		assert_ok!(Balances::transfer(Origin::signed(0), Bounties::bounty_account_id(0), 10));

		assert_ok!(Bounties::claim_bounty(Origin::signed(1), 0));

		assert_eq!(last_event(), RawEvent::BountyClaimed(0, 56, 3));

		assert_eq!(Balances::free_balance(4), 14); // initial 10 + fee 4

		assert_eq!(Balances::free_balance(3), 56);
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 0);

		assert_eq!(Bounties::bounties(0), None);
		assert_eq!(Bounties::bounty_descriptions(0), None);
	});
}

#[test]
fn claim_handles_high_fee() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&4, 30);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 49));
		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_ok!(Bounties::award_bounty(Origin::signed(4), 0, 3));

		System::set_block_number(5);
		<Treasury as OnInitialize<u64>>::on_initialize(5);

		// make fee > balance
		let _ = Balances::slash(&Bounties::bounty_account_id(0), 10);

		assert_ok!(Bounties::claim_bounty(Origin::signed(1), 0));

		assert_eq!(last_event(), RawEvent::BountyClaimed(0, 0, 3));

		assert_eq!(Balances::free_balance(4), 70); // 30 + 50 - 10
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 0);

		assert_eq!(Bounties::bounties(0), None);
		assert_eq!(Bounties::bounty_descriptions(0), None);
	});
}

#[test]
fn cancel_and_refund() {
	new_test_ext().execute_with(|| {

		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Balances::transfer(Origin::signed(0), Bounties::bounty_account_id(0), 10));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 0,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::Funded,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 60);

		assert_noop!(Bounties::close_bounty(Origin::signed(0), 0), BadOrigin);

		assert_ok!(Bounties::close_bounty(Origin::root(), 0));

		assert_eq!(Treasury::pot(), 85); // - 25 + 10

	});

}

#[test]
fn award_and_cancel() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 0, 10));
		assert_ok!(Bounties::accept_curator(Origin::signed(0), 0));

		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 5);

		assert_ok!(Bounties::award_bounty(Origin::signed(0), 0, 3));

		// Cannot close bounty directly when payout is happening...
		assert_noop!(Bounties::close_bounty(Origin::root(), 0), Error::<Test>::PendingPayout);

		// Instead unassign the curator to slash them and then close.
		assert_ok!(Bounties::unassign_curator(Origin::root(), 0));
		assert_ok!(Bounties::close_bounty(Origin::root(), 0));

		assert_eq!(last_event(), RawEvent::BountyCanceled(0));

		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 0);

		// Slashed.
		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 0);

		assert_eq!(Bounties::bounties(0), None);
		assert_eq!(Bounties::bounty_descriptions(0), None);
	});
}

#[test]
fn expire_and_unassign() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 1, 10));
		assert_ok!(Bounties::accept_curator(Origin::signed(1), 0));

		assert_eq!(Balances::free_balance(1), 93);
		assert_eq!(Balances::reserved_balance(1), 5);

		System::set_block_number(22);
		<Treasury as OnInitialize<u64>>::on_initialize(22);

		// assert_noop!(Bounties::unassign_curator(Origin::signed(0), 0), Error::<Test>::Premature);
		let unwrapped_error = Bounties::unassign_curator(Origin::signed(0), 0).unwrap_err();
		matches!(
			unwrapped_error,
			DispatchError::Module {
				index: 0,
				error: 8,
				message: Some(
					"Premature",
				),
			}
		);

		System::set_block_number(23);
		<Treasury as OnInitialize<u64>>::on_initialize(23);

		assert_ok!(Bounties::unassign_curator(Origin::signed(0), 0));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 10,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::Funded,
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Balances::free_balance(1), 93);
		assert_eq!(Balances::reserved_balance(1), 0); // slashed

	});
}

#[test]
fn extend_expiry() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&4, 10);
		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		assert_noop!(Bounties::extend_bounty_expiry(Origin::signed(1), 0, Vec::new()), Error::<Test>::UnexpectedStatus);

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 10));
		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_eq!(Balances::free_balance(4), 5);
		assert_eq!(Balances::reserved_balance(4), 5);

		System::set_block_number(10);
		<Treasury as OnInitialize<u64>>::on_initialize(10);

		assert_noop!(Bounties::extend_bounty_expiry(Origin::signed(0), 0, Vec::new()), Error::<Test>::RequireCurator);
		assert_ok!(Bounties::extend_bounty_expiry(Origin::signed(4), 0, Vec::new()));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 10,
			curator_deposit: 5,
			value: 50,
			bond: 85,
			status: BountyStatus::Active { curator: 4, update_due: 30 },
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_ok!(Bounties::extend_bounty_expiry(Origin::signed(4), 0, Vec::new()));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 10,
			curator_deposit: 5,
			value: 50,
			bond: 85,
			status: BountyStatus::Active { curator: 4, update_due: 30 }, // still the same
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		System::set_block_number(25);
		<Treasury as OnInitialize<u64>>::on_initialize(25);

		// assert_noop!(Bounties::unassign_curator(Origin::signed(0), 0), Error::<Test>::Premature);
		let unwrapped_error = Bounties::unassign_curator(Origin::signed(0), 0).unwrap_err();
		matches!(
			unwrapped_error,
			DispatchError::Module {
				index: 0,
				error: 8,
				message: Some(
					"Premature",
				),
			}
		);
		assert_ok!(Bounties::unassign_curator(Origin::signed(4), 0));

		assert_eq!(Balances::free_balance(4), 10); // not slashed
		assert_eq!(Balances::reserved_balance(4), 0);
	});
}

#[test]
fn genesis_funding_works() {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let initial_funding = 100;
	pallet_balances::GenesisConfig::<Test>{
		// Total issuance will be 200 with treasury account initialized with 100.
		balances: vec![(0, 100), (Treasury::account_id(), initial_funding)],
	}.assimilate_storage(&mut t).unwrap();
	pallet_treasury::GenesisConfig::default().assimilate_storage::<Test, _>(&mut t).unwrap();
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), initial_funding);
		assert_eq!(Treasury::pot(), initial_funding - Balances::minimum_balance());
	});
}

#[test]
fn add_subbounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 0,
			value: 50,
			bond: 85,
			status: BountyStatus::CuratorProposed {
				curator: 4,
			},
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			fee: 4,
			curator_deposit: 2,
			value: 50,
			bond: 85,
			status: BountyStatus::Active {
				curator: 4,
				update_due: 22,
			},
			subbountycount: 0u32.into(),
			activesubbounty: Default::default(),
		});

		assert_eq!(Balances::free_balance(&4), 8);
		assert_eq!(Balances::reserved_balance(&4), 2);

		assert_noop!(
			Bounties::add_subbounty(Origin::signed(0), 0, 50, b"12345-p1".to_vec()),
			Error::<Test>::RequireCurator,
		);

		assert_noop!(
			Bounties::add_subbounty(Origin::signed(4), 0, 50, b"12345-p1".to_vec()),
			Error::<Test>::InsufficientProposersBalance,
		);

		println!("FB-{:#?}/RB-{:#?}",
			Balances::free_balance(&4),
			Balances::reserved_balance(&4),
		);

		Balances::make_free_balance_be(&4, 101);

		println!("FB-{:#?}/RB-{:#?}",
			Balances::free_balance(&4),
			Balances::reserved_balance(&4),
		);

		assert_noop!(
			Bounties::add_subbounty(Origin::signed(4), 0, 50, b"12345-p1".to_vec()),
			Error::<Test>::InsufficientBountyBalance,
		);

		println!("FB-{:#?}/RB-{:#?}",
			Balances::free_balance(&4),
			Balances::reserved_balance(&4),
		);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-p1".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,1));

		println!("FB-{:#?}/RB-{:#?}",
			Balances::free_balance(&4),
			Balances::reserved_balance(&4),
		);

		assert_eq!(Bounties::bounties(0).unwrap(), Bounty {
			proposer: 0,
			value: 50,
			fee: 4,
			curator_deposit: 2,
			bond: 85,
			status: BountyStatus::Active {
				curator: 4,
				update_due: 22,
			},
			subbountycount: 1,
			activesubbounty: [
				1,
			].to_vec(),
		});

		assert_eq!(Bounties::subbounties(0,1).unwrap(), SubBounty {
			proposer: 4,
			value: 10,
			fee: 0,
			curator_deposit: 0,
			bond: 88,
			status: BountyStatus::Approved,
		});

		assert_eq!(
			Bounties::subbounty_descriptions(0,1).unwrap(),
			b"12345-p1".to_vec(),
		);

		assert_eq!(Bounties::subbounty_approvals(),
			[(0,1)].to_vec()
		);

	});
}

#[test]
fn assign_subcurator_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		Balances::make_free_balance_be(&4, 101);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-p1".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,1));

		System::set_block_number(4);
		<Treasury as OnInitialize<u64>>::on_initialize(4);

		System::set_block_number(6);
		<Treasury as OnInitialize<u64>>::on_initialize(6);

		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,1,4,2)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap(), SubBounty {
			proposer: 4,
			value: 10,
			fee: 0,
			curator_deposit: 0,
			bond: 88,
			status: BountyStatus::CuratorProposed {
				curator: 4,
			},
		});

		assert_eq!(Balances::free_balance(4), 101);
		assert_eq!(Balances::reserved_balance(4), 2);

		assert_noop!(
			Bounties::accept_subcurator(Origin::signed(3),0,1),
			Error::<Test>::RequireCurator,
		);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(4),0,1)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap(), SubBounty {
				proposer: 4,
				value: 10,
				fee: 0,
				curator_deposit: 0,
				bond: 88,
				status: BountyStatus::Active {
					curator: 4,
					update_due: 26,
				},
			}
		);

		// no deposit for subcurator who is also curator of parnet bounty
		assert_eq!(Balances::free_balance(4), 101);
		assert_eq!(Balances::reserved_balance(4), 2);

	});
}

#[test]
fn cfg_max_subbounty_count_works() {
	new_test_ext().execute_with(|| {

		// ===Pre-steps :: Make the bounty or parent bounty===
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 34, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		// ===Pre-steps :: Add Max number of subbounty===
		// Acc-4 is the master curator & make sure enough
		// balance for subbounty deposit.
		Balances::make_free_balance_be(&4, 301);

		assert_eq!(Balances::free_balance(4), 301);
		assert_eq!(Balances::reserved_balance(4), 2);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb01".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,1));

		assert_eq!(Balances::free_balance(4), 211);
		assert_eq!(Balances::reserved_balance(4), 92);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb02".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,2));

		assert_eq!(Balances::free_balance(4), 121);
		assert_eq!(Balances::reserved_balance(4), 182);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb03".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,3));

		assert_eq!(Balances::free_balance(4), 31);
		assert_eq!(Balances::reserved_balance(4), 272);

		// Test runtime supports Max of 3 Subbounties
		assert_noop!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb04".to_vec()),
			Error::<Test>::SubBountyMaxOverflow,
		);

		assert_eq!(Balances::free_balance(4), 31);
		assert_eq!(Balances::reserved_balance(4), 272);

		// Move the subbounties to "Funded State"
		System::set_block_number(4);
		<Treasury as OnInitialize<u64>>::on_initialize(4);

		System::set_block_number(6);
		<Treasury as OnInitialize<u64>>::on_initialize(6);

		// Test for the last funded subbounty
		assert_eq!(last_event(), RawEvent::SubBountyFunded(0,3));

		// ===XXX_subcurator() api test===
		// test propose_subcurator() with invalid curator.
		assert_noop!(
			Bounties::propose_subcurator(Origin::signed(4),0,0,5,2),
			Error::<Test>::InvalidIndex,
		);

		// propose subcurator for all added 3 subbounties.
		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,1,5,2)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap().status,
			BountyStatus::CuratorProposed {
				curator: 5,
			},
		);

		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,2,6,2)
		);

		assert_eq!(Bounties::subbounties(0,2).unwrap().status,
			BountyStatus::CuratorProposed {
				curator: 6,
			},
		);

		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,3,7,2)
		);

		assert_eq!(Bounties::subbounties(0,3).unwrap().status,
			BountyStatus::CuratorProposed {
				curator: 7,
			},
		);

		// Test for curator balance, ensure all reserved deposits are reverted
		assert_eq!(Balances::free_balance(4), 301);
		assert_eq!(Balances::reserved_balance(4), 2);

		// ===Test accept_subcurator() for invalid curator===
		assert_noop!(
			Bounties::accept_subcurator(Origin::signed(3),0,1),
			Error::<Test>::RequireCurator,
		);

		// ===Test accept_subcurator() for invalid curator deposit balance===
		assert_noop!(
			Bounties::accept_subcurator(Origin::signed(5),0,1),
			pallet_balances::Error::<Test, _>::InsufficientBalance,
		);

		// ===Acc-5 accepts role of subcurator===
		Balances::make_free_balance_be(&5, 10);

		assert_eq!(Balances::free_balance(5), 10);
		assert_eq!(Balances::reserved_balance(5), 0);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(5),0,1)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap().status,
			BountyStatus::Active {
				curator: 5,
				update_due: 26,
			},
		);

		assert_eq!(Balances::free_balance(5), 9);
		assert_eq!(Balances::reserved_balance(5), 1);

		// ===Acc-6 accepts role of subcurator===
		Balances::make_free_balance_be(&6, 10);

		assert_eq!(Balances::free_balance(6), 10);
		assert_eq!(Balances::reserved_balance(6), 0);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(6),0,2)
		);

		assert_eq!(Bounties::subbounties(0,2).unwrap().status,
			BountyStatus::Active {
				curator: 6,
				update_due: 26,
			},
		);

		assert_eq!(Balances::free_balance(6), 9);
		assert_eq!(Balances::reserved_balance(6), 1);

		// ===Acc-7 accepts role of subcurator===
		Balances::make_free_balance_be(&7, 10);

		assert_eq!(Balances::free_balance(7), 10);
		assert_eq!(Balances::reserved_balance(7), 0);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(7),0,3)
		);

		assert_eq!(Bounties::subbounties(0,3).unwrap().status,
			BountyStatus::Active {
				curator: 7,
				update_due: 26,
			},
		);

		assert_eq!(Balances::free_balance(7), 9);
		assert_eq!(Balances::reserved_balance(7), 1);

	});
}

#[test]
fn award_claim_subbounty_works() {
	new_test_ext().execute_with(|| {

		// TestProcedure
		// 1, Create bounty & move to active state with enough fund & master-curator.
		// 2, Master-curator adds two subbounties & propose sub-curator.
		// 3, Sub-curator accepts & award bounties.
		// 5, Ensure parent bounty is not closed after two subbounties are closed/claimed.
		// 6. Award the parent pounty and master-curator fee.

		// ===Pre-steps :: Make the bounty or parent bounty===
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		// Bouty curator initial balance
		Balances::make_free_balance_be(&4, 201);
		assert_eq!(Balances::free_balance(4), 201);
		assert_eq!(Balances::reserved_balance(4), 0);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 25, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		assert_eq!(Balances::free_balance(Treasury::account_id()), 101);
		assert_eq!(Balances::reserved_balance(Treasury::account_id()), 0);

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_eq!(Balances::free_balance(Treasury::account_id()), 39);
		assert_eq!(Balances::reserved_balance(Treasury::account_id()), 0);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		// bounty & treasury account balance
		assert_eq!(Balances::free_balance(Treasury::account_id()), 39);
		assert_eq!(Balances::reserved_balance(Treasury::account_id()), 0);

		// amount 4 is reserved for curator fee
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 21);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 4);

		// ===Pre-steps :: Add two subbounty===
		// Acc-4 is the master curator & make sure enough
		assert_eq!(Balances::free_balance(4), 199);
		assert_eq!(Balances::reserved_balance(4), 2);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb01".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,1));

		assert_eq!(Balances::free_balance(4), 109);
		assert_eq!(Balances::reserved_balance(4), 92);

		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 11);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 14);

		assert_ok!(
			Bounties::add_subbounty(Origin::signed(4), 0, 10, b"12345-sb02".to_vec())
		);

		assert_eq!(last_event(), RawEvent::SubBountyApproved(0,2));

		assert_eq!(Balances::free_balance(4), 19);
		assert_eq!(Balances::reserved_balance(4), 182);

		// reserved for two subbounties & master currator fee
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 1);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 24);

		// Move the subbounties to "Funded State"
		System::set_block_number(4);
		<Treasury as OnInitialize<u64>>::on_initialize(4);

		System::set_block_number(6);
		<Treasury as OnInitialize<u64>>::on_initialize(6);

		// Test for the last funded subbounty
		assert_eq!(last_event(), RawEvent::SubBountyFunded(0,2));

		// ===XXX_subcurator() api test===
		// propose subcurator for all added 2 subbounties.
		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,1,5,2)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap().status,
			BountyStatus::CuratorProposed {
				curator: 5,
			},
		);

		assert_ok!(
			Bounties::propose_subcurator(Origin::signed(4),0,2,6,2)
		);

		assert_eq!(Bounties::subbounties(0,2).unwrap().status,
			BountyStatus::CuratorProposed {
				curator: 6,
			},
		);

		// Test for curator balance, ensure all reserved deposits are reverted
		assert_eq!(Balances::free_balance(4), 199);
		assert_eq!(Balances::reserved_balance(4), 2);

		// ===Test accept_subcurator() for invalid curator===

		// ===Acc-5 accepts role of subcurator===
		Balances::make_free_balance_be(&5, 10);

		assert_eq!(Balances::free_balance(5), 10);
		assert_eq!(Balances::reserved_balance(5), 0);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(5),0,1)
		);

		assert_eq!(Bounties::subbounties(0,1).unwrap().status,
			BountyStatus::Active {
				curator: 5,
				update_due: 26,
			},
		);

		assert_eq!(Balances::free_balance(5), 9);
		assert_eq!(Balances::reserved_balance(5), 1);

		// ===Acc-6 accepts role of subcurator===
		Balances::make_free_balance_be(&6, 10);

		assert_eq!(Balances::free_balance(6), 10);
		assert_eq!(Balances::reserved_balance(6), 0);

		assert_ok!(
			Bounties::accept_subcurator(Origin::signed(6),0,2)
		);

		assert_eq!(Bounties::subbounties(0,2).unwrap().status,
			BountyStatus::Active {
				curator: 6,
				update_due: 26,
			},
		);

		assert_eq!(Balances::free_balance(6), 9);
		assert_eq!(Balances::reserved_balance(6), 1);

		// ===Award subbounties===
		// Test for invalid arguments
		assert_noop!(
			Bounties::award_subbounty(Origin::signed(3),0,1,7),
			Error::<Test>::RequireCurator,
		);

		// TODO :: Have to recheck
		// Master curator should be able to award bounty.
		assert_noop!(
			Bounties::award_subbounty(Origin::signed(3),0,1,7),
			Error::<Test>::RequireCurator,
		);

		// subbounty-1
		assert_ok!(Bounties::award_subbounty(Origin::signed(5),0,1,7));

		assert_eq!(Bounties::subbounties(0,1).unwrap().status,
			BountyStatus::PendingPayout {
				curator: 5,
				beneficiary: 7,
				unlock_at: 9
			},
		);

		// subbounty-2
		assert_ok!(Bounties::award_subbounty(Origin::signed(6),0,2,8));

		assert_eq!(Bounties::subbounties(0,2).unwrap().status,
			BountyStatus::PendingPayout {
				curator: 6,
				beneficiary: 8,
				unlock_at: 9
			},
		);

		// ===Claim subbounties===
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 1);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 24);

		assert_eq!(Balances::free_balance(5), 9);
		assert_eq!(Balances::reserved_balance(5), 1);

		Balances::make_free_balance_be(&7, 10);
		Balances::make_free_balance_be(&8, 10);

		assert_eq!(Balances::free_balance(7), 10);
		assert_eq!(Balances::reserved_balance(7), 0);

		assert_eq!(Balances::free_balance(8), 10);
		assert_eq!(Balances::reserved_balance(8), 0);

		// Test for Premature conditions
		assert_noop!(
			Bounties::claim_subbounty(Origin::signed(7),0,1),
			Error::<Test>::Premature,
		);

		System::set_block_number(9);
		// <Treasury as OnInitialize<u64>>::on_initialize(9);

		assert_ok!(Bounties::claim_subbounty(Origin::signed(7),0,1));

		// Ensure subcurator is paid with curator fee & deposit refund
		assert_eq!(Balances::free_balance(5), 12);
		assert_eq!(Balances::reserved_balance(5), 0);

		// Ensure executor is paid with beneficiory amount.
		assert_eq!(Balances::free_balance(7), 18);
		assert_eq!(Balances::reserved_balance(7), 0);

		assert_ok!(Bounties::claim_subbounty(Origin::signed(7),0,2));

		// Ensure subcurator is paid with curator fee & deposit refund
		assert_eq!(Balances::free_balance(6), 12);
		assert_eq!(Balances::reserved_balance(6), 0);

		assert_eq!(Balances::free_balance(8), 18);
		assert_eq!(Balances::reserved_balance(8), 0);

		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 1);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 4);

		// ===award parent pounty===
		// ensure state of parent bounty is active
		assert_eq!(Bounties::bounties(0).unwrap().status,
			BountyStatus::Active {
				curator: 4,
				update_due: 22,
			},
		);

		// call award bounty
		assert_ok!(Bounties::award_bounty(Origin::signed(4), 0, 4));
		assert_eq!(Bounties::bounties(0).unwrap().status,
			BountyStatus::PendingPayout {
				curator: 4,
				beneficiary: 4,
				unlock_at: 12
			},
		);

		assert_noop!(
			Bounties::claim_bounty(Origin::signed(4), 0),
			Error::<Test>::Premature,
		);

		System::set_block_number(12);

		// Trust & Bounty balance before Claim
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 1);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 4);

		assert_eq!(Balances::free_balance(Treasury::account_id()), 11);
		assert_eq!(Balances::reserved_balance(Treasury::account_id()), 0);

		assert_ok!(Bounties::claim_bounty(Origin::signed(4), 0));

		// 205 = Initial balance(201) + master curator fee(4)
		assert_eq!(Balances::free_balance(4), 205);
		assert_eq!(Balances::reserved_balance(4), 0);

		// bounty account free & reserved is zero
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 0);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 0);

		// final treasury balance :: 12 = 11 + 1(from bounty free balance)
		assert_eq!(Balances::free_balance(Treasury::account_id()), 12);
		assert_eq!(Balances::reserved_balance(Treasury::account_id()), 0);
	});
}
