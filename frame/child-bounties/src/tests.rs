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

//! Child-bounties pallet tests.

#![cfg(test)]

use super::*;
use crate as pallet_child_bounties;
use std::cell::RefCell;

use frame_support::{
	assert_noop, assert_ok, pallet_prelude::GenesisBuild, parameter_types, traits::OnInitialize,
	weights::Weight, PalletId,
};

use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	Perbill, Storage, Permill,
};

use super::Event as ChildBountiesEvent;
use pallet_bounties::{Event as BountiesEvent, Bounty, BountyStatus};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;
type BountiesError = pallet_bounties::Error<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Bounties: pallet_bounties::{Pallet, Call, Storage, Event<T>},
		Treasury: pallet_treasury::{Pallet, Call, Storage, Config, Event<T>},
        ChildBounties: pallet_child_bounties::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u128;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
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
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const MaxApprovals: u32 = 100;
}

impl pallet_treasury::Config for Test {
	type PalletId = TreasuryPalletId;
	type Currency = pallet_balances::Pallet<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type Event = Event;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type SpendPeriod = SpendPeriod;
	type Burn = Burn;
	type BurnDestination = ();
	type WeightInfo = ();
	type SpendFunds = Bounties;
	type MaxApprovals = MaxApprovals;
}
parameter_types! {
	pub const BountyDepositBase: u64 = 80;
	pub const BountyDepositPayoutDelay: u64 = 3;
	pub const BountyUpdatePeriod: u32 = 20;
	pub const BountyCuratorDeposit: Permill = Permill::from_percent(50);
	pub const BountyValueMinimum: u64 = 5;
	pub const MaximumReasonLength: u32 = 16384;
}
impl pallet_bounties::Config for Test {
	type Event = Event;
	type BountyDepositBase = BountyDepositBase;
	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;
	type BountyUpdatePeriod = BountyUpdatePeriod;
	type BountyCuratorDeposit = BountyCuratorDeposit;
	type BountyValueMinimum = BountyValueMinimum;
	type DataDepositPerByte = DataDepositPerByte;
	type MaximumReasonLength = MaximumReasonLength;
	type WeightInfo = ();
    type ChildBountyManager = ChildBounties;
}
parameter_types! {
    pub const MaxActiveChildBountyCount: u32 = 2;
	pub const ChildBountyValueMinimum: u64 = 1;
}
impl pallet_child_bounties::Config for Test {
    type Event = Event;
	type MaxActiveChildBountyCount = MaxActiveChildBountyCount;
	type ChildBountyValueMinimum = ChildBountyValueMinimum;
}

type TreasuryError = pallet_treasury::Error<Test>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		// Total issuance will be 200 with treasury account initialized at ED.
		balances: vec![(0, 100), (1, 98), (2, 1)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	GenesisBuild::<Test>::assimilate_storage(&pallet_treasury::GenesisConfig, &mut t).unwrap();
	t.into()
}

fn last_event() -> ChildBountiesEvent<Test> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::ChildBounties(inner) = e { Some(inner) } else { None })
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
fn add_child_bounty_works() {
	new_test_ext().execute_with(|| {
		// TestProcedure.
		// 1, Create bounty & move to active state with enough bounty fund & master-curator.
		// 2, Master-curator adds child-bounty child-bounty-1, test for error like RequireCurator
		//    ,InsufficientProposersBalance, InsufficientBountyBalance with invalid arguments.
		// 3, Master-curator adds child-bounty child-bounty-1, moves to "Approved" state &
		//    test for the event ChildBountyAdded.
		// 4, Test for DB state of `Bounties` & `ChildBounties`.
		// 5, Observe fund transaction moment between Bounty, Child-bounty,
		//    Curator, child-bounty curator & beneficiary.

		// ===Pre-steps :: Make the bounty or parent bounty===
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!(Bounties::propose_bounty(Origin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(Origin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(Origin::root(), 0, 4, 4));

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(Origin::signed(4), 0));

		assert_eq!(Balances::free_balance(&4), 8);
		assert_eq!(Balances::reserved_balance(&4), 2);

		// ===Pre-steps :: Add child-bounty===
		// Acc-4 is the master curator.
		// Call from invalid origin & check for error "RequireCurator".
		assert_noop!(
			ChildBounties::add_child_bounty(Origin::signed(0), 0, 10, b"12345-p1".to_vec()),
			BountiesError::RequireCurator,
		);

		// Update the master curator balance.
		Balances::make_free_balance_be(&4, 101);

		// Master curator fee is reserved on parent bounty account.
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 50);
		assert_eq!(Balances::reserved_balance(Bounties::bounty_account_id(0)), 0);

		assert_noop!(
			ChildBounties::add_child_bounty(Origin::signed(4), 0, 50, b"12345-p1".to_vec()),
			Error::<Test>::InsufficientBountyBalance,
		);

		// Add child-bounty with valid value, which can be funded by parent bounty.
		assert_ok!(ChildBounties::add_child_bounty(Origin::signed(4), 0, 10, b"12345-p1".to_vec()));

		// Check for the event child-bounty added.
		assert_eq!(last_event(), ChildBountiesEvent::ChildBountyAdded(0, 0));

		assert_eq!(Balances::free_balance(4), 101);
		assert_eq!(Balances::reserved_balance(4), 2);

		// DB check.
		// Check the child-bounty status.
		assert_eq!(
			ChildBounties::child_bounties(0, 0).unwrap(),
			ChildBounty {
				parent_bounty: 0,
				fee: 0,
				curator_deposit: 0,
				status: ChildBountyStatus::Added,
			}
		);

		// Check the child-bounty count.
		assert_eq!(
			ChildBounties::parent_child_bounties(0),
			1
		);

		// Check the child-bounty description status.
		assert_eq!(ChildBounties::child_bounty_descriptions(0).unwrap(), b"12345-p1".to_vec(),);
	});
}
