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

//! bounties pallet tests.

#![cfg(test)]

use super::*;
use crate as pallet_bounties;

use frame_support::{
	assert_noop, assert_ok, parameter_types,
	traits::{ConstU32, ConstU64, OnInitialize},
	PalletId,
};

use sp_core::H256;
use sp_runtime::{
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	BuildStorage, Perbill, Storage,
};

use super::Event as BountiesEvent;

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Bounties: pallet_bounties::{Pallet, Call, Storage, Event<T>},
		Bounties1: pallet_bounties::<Instance1>::{Pallet, Call, Storage, Event<T>},
		Treasury: pallet_treasury::{Pallet, Call, Storage, Config<T>, Event<T>},
		Treasury1: pallet_treasury::<Instance1>::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
);

parameter_types! {
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}

type Balance = u64;

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}
parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub static Burn: Permill = Permill::from_percent(50);
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const TreasuryPalletId2: PalletId = PalletId(*b"py/trsr2");
	pub static SpendLimit: Balance = u64::MAX;
	pub static SpendLimit1: Balance = u64::MAX;
}

impl pallet_treasury::Config for Test {
	type PalletId = TreasuryPalletId;
	type Currency = pallet_balances::Pallet<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type RuntimeEvent = RuntimeEvent;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ConstU64<1>;
	type ProposalBondMaximum = ();
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = Bounties;
	type MaxApprovals = ConstU32<100>;
	type SpendOrigin = frame_system::EnsureRootWithSuccess<Self::AccountId, SpendLimit>;
}

impl pallet_treasury::Config<Instance1> for Test {
	type PalletId = TreasuryPalletId2;
	type Currency = pallet_balances::Pallet<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type RuntimeEvent = RuntimeEvent;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ConstU64<1>;
	type ProposalBondMaximum = ();
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = Bounties1;
	type MaxApprovals = ConstU32<100>;
	type SpendOrigin = frame_system::EnsureRootWithSuccess<Self::AccountId, SpendLimit1>;
}

parameter_types! {
	// This will be 50% of the bounty fee.
	pub const CuratorDepositMultiplier: Permill = Permill::from_percent(50);
	pub const CuratorDepositMax: Balance = 1_000;
	pub const CuratorDepositMin: Balance = 3;

}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type BountyDepositBase = ConstU64<80>;
	type BountyDepositPayoutDelay = ConstU64<3>;
	type BountyUpdatePeriod = ConstU64<20>;
	type CuratorDepositMultiplier = CuratorDepositMultiplier;
	type CuratorDepositMax = CuratorDepositMax;
	type CuratorDepositMin = CuratorDepositMin;
	type BountyValueMinimum = ConstU64<1>;
	type DataDepositPerByte = ConstU64<1>;
	type MaximumReasonLength = ConstU32<16384>;
	type WeightInfo = ();
	type ChildBountyManager = ();
}

impl Config<Instance1> for Test {
	type RuntimeEvent = RuntimeEvent;
	type BountyDepositBase = ConstU64<80>;
	type BountyDepositPayoutDelay = ConstU64<3>;
	type BountyUpdatePeriod = ConstU64<20>;
	type CuratorDepositMultiplier = CuratorDepositMultiplier;
	type CuratorDepositMax = CuratorDepositMax;
	type CuratorDepositMin = CuratorDepositMin;
	type BountyValueMinimum = ConstU64<1>;
	type DataDepositPerByte = ConstU64<1>;
	type MaximumReasonLength = ConstU32<16384>;
	type WeightInfo = ();
	type ChildBountyManager = ();
}

type TreasuryError = pallet_treasury::Error<Test>;
type TreasuryError1 = pallet_treasury::Error<Test, Instance1>;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut ext: sp_io::TestExternalities = RuntimeGenesisConfig {
		system: frame_system::GenesisConfig::default(),
		balances: pallet_balances::GenesisConfig { balances: vec![(0, 100), (1, 98), (2, 1)] },
		treasury: Default::default(),
		treasury_1: Default::default(),
	}
	.build_storage()
	.unwrap()
	.into();
	ext.execute_with(|| System::set_block_number(1));
	ext
}

fn last_event() -> BountiesEvent<Test> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let RuntimeEvent::Bounties(inner) = e { Some(inner) } else { None })
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
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 1, 3)
		});
		assert_eq!(Balances::free_balance(0), 99);
		assert_eq!(Balances::reserved_balance(0), 1);
	});
}

#[test]
fn spend_proposal_takes_proportional_deposit() {
	new_test_ext().execute_with(|| {
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 5);
	});
}

#[test]
fn spend_proposal_fails_when_proposer_poor() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::propose_spend(RuntimeOrigin::signed(2), 100, 3)
			},
			TreasuryError::InsufficientProposersBalance,
		);
	});
}

#[test]
fn accepted_spend_proposal_ignored_outside_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

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

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Balances::free_balance(3), 0);
		assert_eq!(Treasury::pot(), 50);
	});
}

#[test]
fn reject_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::reject_proposal(RuntimeOrigin::root(), 0)
			},
			TreasuryError::InvalidIndex
		);
	});
}

#[test]
fn reject_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::reject_proposal(RuntimeOrigin::root(), 0)
			},
			pallet_treasury::Error::<Test>::InvalidIndex
		);
	});
}

#[test]
fn accept_non_existent_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			},
			TreasuryError::InvalidIndex
		);
	});
}

#[test]
fn accept_already_rejected_spend_proposal_fails() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::reject_proposal(RuntimeOrigin::root(), 0)
		});
		assert_noop!(
			{
				#[allow(deprecated)]
				Treasury::approve_proposal(RuntimeOrigin::root(), 0)
			},
			TreasuryError::InvalidIndex
		);
	});
}

#[test]
fn accepted_spend_proposal_enacted_on_spend_period() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 100, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

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

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 150, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		assert_ok!(Balances::deposit_into_existing(&Treasury::account_id(), 100));
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

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), treasury_balance, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(2);
		assert_eq!(Treasury::pot(), 100); // Pot hasn't changed

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), Treasury::pot(), 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 1)
		});

		<Treasury as OnInitialize<u64>>::on_initialize(4);
		assert_eq!(Treasury::pot(), 0); // Pot is emptied
		assert_eq!(Balances::free_balance(Treasury::account_id()), 1); // but the account is still there
	});
}

// In case treasury account is not existing then it works fine.
// This is useful for chain that will just update runtime.
#[test]
fn inexistent_account_works() {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Test> { balances: vec![(0, 100), (1, 99), (2, 1)] }
		.assimilate_storage(&mut t)
		.unwrap();
	// Treasury genesis config is not build thus treasury account does not exist
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), 0); // Account does not exist
		assert_eq!(Treasury::pot(), 0); // Pot is empty

		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 99, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 0)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::propose_spend(RuntimeOrigin::signed(0), 1, 3)
		});
		assert_ok!({
			#[allow(deprecated)]
			Treasury::approve_proposal(RuntimeOrigin::root(), 1)
		});
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

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 10, b"1234567890".to_vec()));

		assert_eq!(last_event(), BountiesEvent::BountyProposed { index: 0 });

		let deposit: u64 = 85 + 5;
		assert_eq!(Balances::reserved_balance(0), deposit);
		assert_eq!(Balances::free_balance(0), 100 - deposit);

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 0,
				curator_deposit: 0,
				value: 10,
				bond: deposit,
				status: BountyStatus::Proposed,
			}
		);

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
			Bounties::propose_bounty(RuntimeOrigin::signed(1), 0, [0; 17_000].to_vec()),
			Error::<Test>::ReasonTooBig
		);

		assert_noop!(
			Bounties::propose_bounty(
				RuntimeOrigin::signed(1),
				10,
				b"12345678901234567890".to_vec()
			),
			Error::<Test>::InsufficientProposersBalance
		);

		assert_noop!(
			Bounties::propose_bounty(RuntimeOrigin::signed(1), 0, b"12345678901234567890".to_vec()),
			Error::<Test>::InvalidValue
		);
	});
}

#[test]
fn close_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_noop!(Bounties::close_bounty(RuntimeOrigin::root(), 0), Error::<Test>::InvalidIndex);

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 10, b"12345".to_vec()));

		assert_ok!(Bounties::close_bounty(RuntimeOrigin::root(), 0));

		let deposit: u64 = 80 + 5;

		assert_eq!(last_event(), BountiesEvent::BountyRejected { index: 0, bond: deposit });

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
		assert_noop!(
			Bounties::approve_bounty(RuntimeOrigin::root(), 0),
			Error::<Test>::InvalidIndex
		);

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		let deposit: u64 = 80 + 5;

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 0,
				value: 50,
				curator_deposit: 0,
				bond: deposit,
				status: BountyStatus::Approved,
			}
		);
		assert_eq!(Bounties::bounty_approvals(), vec![0]);

		assert_noop!(
			Bounties::close_bounty(RuntimeOrigin::root(), 0),
			Error::<Test>::UnexpectedStatus
		);

		// deposit not returned yet
		assert_eq!(Balances::reserved_balance(0), deposit);
		assert_eq!(Balances::free_balance(0), 100 - deposit);

		<Treasury as OnInitialize<u64>>::on_initialize(2);

		// return deposit
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 100);

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 0,
				curator_deposit: 0,
				value: 50,
				bond: deposit,
				status: BountyStatus::Funded,
			}
		);

		assert_eq!(Treasury::pot(), 100 - 50 - 25); // burn 25
		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 50);
	});
}

#[test]
fn assign_curator_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		assert_noop!(
			Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, 4),
			Error::<Test>::InvalidIndex
		);

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_noop!(
			Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, 50),
			Error::<Test>::InvalidFee
		);

		let fee = 4;
		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, fee));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::CuratorProposed { curator: 4 },
			}
		);

		assert_noop!(
			Bounties::accept_curator(RuntimeOrigin::signed(1), 0),
			Error::<Test>::RequireCurator
		);
		assert_noop!(
			Bounties::accept_curator(RuntimeOrigin::signed(4), 0),
			pallet_balances::Error::<Test, _>::InsufficientBalance
		);

		Balances::make_free_balance_be(&4, 10);

		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(4), 0));

		let expected_deposit = Bounties::calculate_curator_deposit(&fee);

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee,
				curator_deposit: expected_deposit,
				value: 50,
				bond: 85,
				status: BountyStatus::Active { curator: 4, update_due: 22 },
			}
		);

		assert_eq!(Balances::free_balance(&4), 10 - expected_deposit);
		assert_eq!(Balances::reserved_balance(&4), expected_deposit);
	});
}

#[test]
fn unassign_curator_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		let fee = 4;

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, fee));
		assert_noop!(Bounties::unassign_curator(RuntimeOrigin::signed(1), 0), BadOrigin);
		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::signed(4), 0));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::Funded,
			}
		);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, fee));
		Balances::make_free_balance_be(&4, 10);
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(4), 0));
		let expected_deposit = Bounties::calculate_curator_deposit(&fee);
		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::root(), 0));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::Funded,
			}
		);

		assert_eq!(Balances::free_balance(&4), 10 - expected_deposit);
		assert_eq!(Balances::reserved_balance(&4), 0); // slashed curator deposit
	});
}

#[test]
fn award_and_claim_bounty_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&4, 10);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		let fee = 4;
		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, fee));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(4), 0));

		let expected_deposit = Bounties::calculate_curator_deposit(&fee);
		assert_eq!(Balances::free_balance(4), 10 - expected_deposit);

		assert_noop!(
			Bounties::award_bounty(RuntimeOrigin::signed(1), 0, 3),
			Error::<Test>::RequireCurator
		);

		assert_ok!(Bounties::award_bounty(RuntimeOrigin::signed(4), 0, 3));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee,
				curator_deposit: expected_deposit,
				value: 50,
				bond: 85,
				status: BountyStatus::PendingPayout { curator: 4, beneficiary: 3, unlock_at: 5 },
			}
		);

		assert_noop!(Bounties::claim_bounty(RuntimeOrigin::signed(1), 0), Error::<Test>::Premature);

		System::set_block_number(5);
		<Treasury as OnInitialize<u64>>::on_initialize(5);

		assert_ok!(Balances::transfer_allow_death(
			RuntimeOrigin::signed(0),
			Bounties::bounty_account_id(0),
			10
		));

		assert_ok!(Bounties::claim_bounty(RuntimeOrigin::signed(1), 0));

		assert_eq!(
			last_event(),
			BountiesEvent::BountyClaimed { index: 0, payout: 56, beneficiary: 3 }
		);

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
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, 49));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(4), 0));

		assert_ok!(Bounties::award_bounty(RuntimeOrigin::signed(4), 0, 3));

		System::set_block_number(5);
		<Treasury as OnInitialize<u64>>::on_initialize(5);

		// make fee > balance
		let res = Balances::slash(&Bounties::bounty_account_id(0), 10);
		assert_eq!(res.0.peek(), 10);

		assert_ok!(Bounties::claim_bounty(RuntimeOrigin::signed(1), 0));

		assert_eq!(
			last_event(),
			BountiesEvent::BountyClaimed { index: 0, payout: 0, beneficiary: 3 }
		);

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

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Balances::transfer_allow_death(
			RuntimeOrigin::signed(0),
			Bounties::bounty_account_id(0),
			10
		));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 0,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::Funded,
			}
		);

		assert_eq!(Balances::free_balance(Bounties::bounty_account_id(0)), 60);

		assert_noop!(Bounties::close_bounty(RuntimeOrigin::signed(0), 0), BadOrigin);

		assert_ok!(Bounties::close_bounty(RuntimeOrigin::root(), 0));

		// `- 25 + 10`
		assert_eq!(Treasury::pot(), 85);
	});
}

#[test]
fn award_and_cancel() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 0, 10));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(0), 0));

		assert_eq!(Balances::free_balance(0), 95);
		assert_eq!(Balances::reserved_balance(0), 5);

		assert_ok!(Bounties::award_bounty(RuntimeOrigin::signed(0), 0, 3));

		// Cannot close bounty directly when payout is happening...
		assert_noop!(
			Bounties::close_bounty(RuntimeOrigin::root(), 0),
			Error::<Test>::PendingPayout
		);

		// Instead unassign the curator to slash them and then close.
		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::root(), 0));
		assert_ok!(Bounties::close_bounty(RuntimeOrigin::root(), 0));

		assert_eq!(last_event(), BountiesEvent::BountyCanceled { index: 0 });

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
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 1, 10));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(1), 0));

		assert_eq!(Balances::free_balance(1), 93);
		assert_eq!(Balances::reserved_balance(1), 5);

		System::set_block_number(22);
		<Treasury as OnInitialize<u64>>::on_initialize(22);

		assert_noop!(
			Bounties::unassign_curator(RuntimeOrigin::signed(0), 0),
			Error::<Test>::Premature
		);

		System::set_block_number(23);
		<Treasury as OnInitialize<u64>>::on_initialize(23);

		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::signed(0), 0));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 10,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::Funded,
			}
		);

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
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));

		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		assert_noop!(
			Bounties::extend_bounty_expiry(RuntimeOrigin::signed(1), 0, Vec::new()),
			Error::<Test>::UnexpectedStatus
		);

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 4, 10));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(4), 0));

		assert_eq!(Balances::free_balance(4), 5);
		assert_eq!(Balances::reserved_balance(4), 5);

		System::set_block_number(10);
		<Treasury as OnInitialize<u64>>::on_initialize(10);

		assert_noop!(
			Bounties::extend_bounty_expiry(RuntimeOrigin::signed(0), 0, Vec::new()),
			Error::<Test>::RequireCurator
		);
		assert_ok!(Bounties::extend_bounty_expiry(RuntimeOrigin::signed(4), 0, Vec::new()));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 10,
				curator_deposit: 5,
				value: 50,
				bond: 85,
				status: BountyStatus::Active { curator: 4, update_due: 30 },
			}
		);

		assert_ok!(Bounties::extend_bounty_expiry(RuntimeOrigin::signed(4), 0, Vec::new()));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 10,
				curator_deposit: 5,
				value: 50,
				bond: 85,
				status: BountyStatus::Active { curator: 4, update_due: 30 }, // still the same
			}
		);

		System::set_block_number(25);
		<Treasury as OnInitialize<u64>>::on_initialize(25);

		assert_noop!(
			Bounties::unassign_curator(RuntimeOrigin::signed(0), 0),
			Error::<Test>::Premature
		);
		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::signed(4), 0));

		assert_eq!(Balances::free_balance(4), 10); // not slashed
		assert_eq!(Balances::reserved_balance(4), 0);
	});
}

#[test]
fn test_migration_v4() {
	let mut s = Storage::default();

	let index: u32 = 10;

	let bounty = Bounty::<u128, u64, u64> {
		proposer: 0,
		value: 20,
		fee: 20,
		curator_deposit: 20,
		bond: 50,
		status: BountyStatus::<u128, u64>::Proposed,
	};

	let data = vec![
		(pallet_bounties::BountyCount::<Test>::hashed_key().to_vec(), 10.encode().to_vec()),
		(pallet_bounties::Bounties::<Test>::hashed_key_for(index), bounty.encode().to_vec()),
		(pallet_bounties::BountyDescriptions::<Test>::hashed_key_for(index), vec![0, 0]),
		(
			pallet_bounties::BountyApprovals::<Test>::hashed_key().to_vec(),
			vec![10 as u32].encode().to_vec(),
		),
	];

	s.top = data.into_iter().collect();

	sp_io::TestExternalities::new(s).execute_with(|| {
		use frame_support::traits::PalletInfo;
		let old_pallet_name = <Test as frame_system::Config>::PalletInfo::name::<Bounties>()
			.expect("Bounties is part of runtime, so it has a name; qed");
		let new_pallet_name = "NewBounties";

		crate::migrations::v4::pre_migration::<Test, Bounties, _>(old_pallet_name, new_pallet_name);
		crate::migrations::v4::migrate::<Test, Bounties, _>(old_pallet_name, new_pallet_name);
		crate::migrations::v4::post_migration::<Test, Bounties, _>(
			old_pallet_name,
			new_pallet_name,
		);
	});
}

#[test]
fn genesis_funding_works() {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	let initial_funding = 100;
	pallet_balances::GenesisConfig::<Test> {
		// Total issuance will be 200 with treasury account initialized with 100.
		balances: vec![(0, 100), (Treasury::account_id(), initial_funding)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	pallet_treasury::GenesisConfig::<Test>::default()
		.assimilate_storage(&mut t)
		.unwrap();
	let mut t: sp_io::TestExternalities = t.into();

	t.execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury::account_id()), initial_funding);
		assert_eq!(Treasury::pot(), initial_funding - Balances::minimum_balance());
	});
}

#[test]
fn unassign_curator_self() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 50, b"12345".to_vec()));
		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), 0, 1, 10));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(1), 0));

		assert_eq!(Balances::free_balance(1), 93);
		assert_eq!(Balances::reserved_balance(1), 5);

		System::set_block_number(8);
		<Treasury as OnInitialize<u64>>::on_initialize(8);

		assert_ok!(Bounties::unassign_curator(RuntimeOrigin::signed(1), 0));

		assert_eq!(
			Bounties::bounties(0).unwrap(),
			Bounty {
				proposer: 0,
				fee: 10,
				curator_deposit: 0,
				value: 50,
				bond: 85,
				status: BountyStatus::Funded,
			}
		);

		assert_eq!(Balances::free_balance(1), 98);
		assert_eq!(Balances::reserved_balance(1), 0); // not slashed
	});
}

#[test]
fn accept_curator_handles_different_deposit_calculations() {
	// This test will verify that a bounty with and without a fee results
	// in a different curator deposit: one using the value, and one using the fee.
	new_test_ext().execute_with(|| {
		// Case 1: With a fee
		let user = 1;
		let bounty_index = 0;
		let value = 88;
		let fee = 42;

		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&user, 100);
		// Allow for a larger spend limit:
		SpendLimit::set(value);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), value, b"12345".to_vec()));
		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), bounty_index));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), bounty_index, user, fee));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(user), bounty_index));

		let expected_deposit = CuratorDepositMultiplier::get() * fee;
		assert_eq!(Balances::free_balance(&user), 100 - expected_deposit);
		assert_eq!(Balances::reserved_balance(&user), expected_deposit);

		// Case 2: Lower bound
		let user = 2;
		let bounty_index = 1;
		let value = 35;
		let fee = 0;

		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&user, 100);

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), value, b"12345".to_vec()));
		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), bounty_index));

		System::set_block_number(4);
		<Treasury as OnInitialize<u64>>::on_initialize(4);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), bounty_index, user, fee));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(user), bounty_index));

		let expected_deposit = CuratorDepositMin::get();
		assert_eq!(Balances::free_balance(&user), 100 - expected_deposit);
		assert_eq!(Balances::reserved_balance(&user), expected_deposit);

		// Case 3: Upper bound
		let user = 3;
		let bounty_index = 2;
		let value = 1_000_000;
		let fee = 50_000;
		let starting_balance = fee * 2;

		Balances::make_free_balance_be(&Treasury::account_id(), value * 2);
		Balances::make_free_balance_be(&user, starting_balance);
		Balances::make_free_balance_be(&0, starting_balance);

		// Allow for a larger spend limit:
		SpendLimit::set(value);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), value, b"12345".to_vec()));
		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), bounty_index));

		System::set_block_number(6);
		<Treasury as OnInitialize<u64>>::on_initialize(6);

		assert_ok!(Bounties::propose_curator(RuntimeOrigin::root(), bounty_index, user, fee));
		assert_ok!(Bounties::accept_curator(RuntimeOrigin::signed(user), bounty_index));

		let expected_deposit = CuratorDepositMax::get();
		assert_eq!(Balances::free_balance(&user), starting_balance - expected_deposit);
		assert_eq!(Balances::reserved_balance(&user), expected_deposit);
	});
}

#[test]
fn approve_bounty_works_second_instance() {
	new_test_ext().execute_with(|| {
		// Set burn to 0 to make tracking funds easier.
		Burn::set(Permill::from_percent(0));

		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		Balances::make_free_balance_be(&Treasury1::account_id(), 201);
		assert_eq!(Balances::free_balance(&Treasury::account_id()), 101);
		assert_eq!(Balances::free_balance(&Treasury1::account_id()), 201);

		assert_ok!(Bounties1::propose_bounty(RuntimeOrigin::signed(0), 10, b"12345".to_vec()));
		assert_ok!(Bounties1::approve_bounty(RuntimeOrigin::root(), 0));
		<Treasury as OnInitialize<u64>>::on_initialize(2);
		<Treasury1 as OnInitialize<u64>>::on_initialize(2);

		// Bounties 1 is funded... but from where?
		assert_eq!(Balances::free_balance(Bounties1::bounty_account_id(0)), 10);
		// Treasury 1 unchanged
		assert_eq!(Balances::free_balance(&Treasury::account_id()), 101);
		// Treasury 2 has funds removed
		assert_eq!(Balances::free_balance(&Treasury1::account_id()), 201 - 10);
	});
}

#[test]
fn approve_bounty_insufficient_spend_limit_errors() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury::account_id(), 101);
		assert_eq!(Treasury::pot(), 100);

		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 51, b"123".to_vec()));
		// 51 will not work since the limit is 50.
		SpendLimit::set(50);
		assert_noop!(
			Bounties::approve_bounty(RuntimeOrigin::root(), 0),
			TreasuryError::InsufficientPermission
		);
	});
}

#[test]
fn approve_bounty_instance1_insufficient_spend_limit_errors() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_eq!(Treasury1::pot(), 100);

		assert_ok!(Bounties1::propose_bounty(RuntimeOrigin::signed(0), 51, b"123".to_vec()));
		// 51 will not work since the limit is 50.
		SpendLimit1::set(50);
		assert_noop!(
			Bounties1::approve_bounty(RuntimeOrigin::root(), 0),
			TreasuryError1::InsufficientPermission
		);
	});
}

#[test]
fn propose_curator_insufficient_spend_limit_errors() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		// Temporarily set a larger spend limit;
		SpendLimit::set(51);
		assert_ok!(Bounties::propose_bounty(RuntimeOrigin::signed(0), 51, b"12345".to_vec()));
		assert_ok!(Bounties::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury as OnInitialize<u64>>::on_initialize(2);

		SpendLimit::set(50);
		// 51 will not work since the limit is 50.
		assert_noop!(
			Bounties::propose_curator(RuntimeOrigin::root(), 0, 0, 0),
			TreasuryError::InsufficientPermission
		);
	});
}

#[test]
fn propose_curator_instance1_insufficient_spend_limit_errors() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury::account_id(), 101);

		// Temporarily set a larger spend limit;
		SpendLimit1::set(11);
		assert_ok!(Bounties1::propose_bounty(RuntimeOrigin::signed(0), 11, b"12345".to_vec()));
		assert_ok!(Bounties1::approve_bounty(RuntimeOrigin::root(), 0));

		System::set_block_number(2);
		<Treasury1 as OnInitialize<u64>>::on_initialize(2);

		SpendLimit1::set(10);
		// 11 will not work since the limit is 10.
		assert_noop!(
			Bounties1::propose_curator(RuntimeOrigin::root(), 0, 0, 0),
			TreasuryError1::InsufficientPermission
		);
	});
}
