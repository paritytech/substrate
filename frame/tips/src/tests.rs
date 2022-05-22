// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use std::cell::RefCell;

use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	Perbill, Permill, BuildStorage,
};
use sp_storage::Storage;

use frame_support::{
	assert_noop, assert_ok,
	pallet_prelude::GenesisBuild,
	parameter_types,
	storage::StoragePrefixedMap,
	traits::{ConstU32, ConstU64, SortedMembers},
	PalletId,
};

use super::*;
use crate::{self as pallet_tips, Event as TipEvent};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
        Treasury: pallet_treasury::{Pallet, Call, Storage, Config, Event<T>},
		Treasury1: pallet_treasury::<Instance1>::{Pallet, Call, Storage, Config, Event<T>},
        Treasury2: pallet_treasury::<Instance2>::{Pallet, Call, Storage, Config, Event<T>},
        Tips: pallet_tips::{Pallet, Call, Storage, Event<T>},
        Tips1: pallet_tips::<Instance1>::{Pallet, Call, Storage, Event<T>},
        Tips2: pallet_tips::<Instance2>::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
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
	type AccountId = u128; // u64 is not enough to hold bytes used to generate bounty account
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}
thread_local! {
	static TEN_TO_FOURTEEN: RefCell<Vec<u128>> = RefCell::new(vec![10,11,12,13,14]);
}
pub struct TenToFourteen;
impl SortedMembers<u128> for TenToFourteen {
	fn sorted_members() -> Vec<u128> {
		TEN_TO_FOURTEEN.with(|v| v.borrow().clone())
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
	fn min_len() -> usize {
		0
	}
}
parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const Burn: Permill = Permill::from_percent(50);
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
}
impl pallet_treasury::Config for Test {
    type PalletId = TreasuryPalletId;
    type Currency = pallet_balances::Pallet<Test>;
    type ApproveOrigin = frame_system::EnsureRoot<u128>;
    type RejectOrigin = frame_system::EnsureRoot<u128>;
    type Event = Event;
    type OnSlash = ();
    type ProposalBond = ProposalBond;
    type ProposalBondMinimum = ConstU64<1>;
    type ProposalBondMaximum = ();
    type SpendPeriod = ConstU64<2>;
    type Burn = Burn;
    type BurnDestination = (); // Just gets burned.
    type WeightInfo = ();
    type SpendFunds = ();
    type MaxApprovals = ConstU32<100>;
}

impl pallet_treasury::Config<Instance1> for Test {
	type PalletId = TreasuryPalletId;
	type Currency = pallet_balances::Pallet<Test>;
	type ApproveOrigin = frame_system::EnsureRoot<u128>;
	type RejectOrigin = frame_system::EnsureRoot<u128>;
	type Event = Event;
	type OnSlash = ();
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ConstU64<1>;
	type ProposalBondMaximum = ();
	type SpendPeriod = ConstU64<2>;
	type Burn = Burn;
	type BurnDestination = (); // Just gets burned.
	type WeightInfo = ();
	type SpendFunds = ();
	type MaxApprovals = ConstU32<100>;
}

impl pallet_treasury::Config<Instance2> for Test {
    type PalletId = TreasuryPalletId;
    type Currency = pallet_balances::Pallet<Test>;
    type ApproveOrigin = frame_system::EnsureRoot<u128>;
    type RejectOrigin = frame_system::EnsureRoot<u128>;
    type Event = Event;
    type OnSlash = ();
    type ProposalBond = ProposalBond;
    type ProposalBondMinimum = ConstU64<1>;
    type ProposalBondMaximum = ();
    type SpendPeriod = ConstU64<2>;
    type Burn = Burn;
    type BurnDestination = (); // Just gets burned.
    type WeightInfo = ();
    type SpendFunds = ();
    type MaxApprovals = ConstU32<100>;
}

parameter_types! {
	pub const TipFindersFee: Percent = Percent::from_percent(20);
}
impl Config for Test {
    type MaximumReasonLength = ConstU32<16384>;
    type Tippers = TenToFourteen;
    type TipCountdown = ConstU64<1>;
    type TipFindersFee = TipFindersFee;
    type TipReportDepositBase = ConstU64<1>;
    type DataDepositPerByte = ConstU64<1>;
    type Event = Event;
    type WeightInfo = ();
}

impl Config<Instance1> for Test {
	type MaximumReasonLength = ConstU32<16384>;
	type Tippers = TenToFourteen;
	type TipCountdown = ConstU64<1>;
	type TipFindersFee = TipFindersFee;
	type TipReportDepositBase = ConstU64<1>;
	type DataDepositPerByte = ConstU64<1>;
	type Event = Event;
	type WeightInfo = ();
}

impl Config<Instance2> for Test {
    type MaximumReasonLength = ConstU32<16384>;
    type Tippers = TenToFourteen;
    type TipCountdown = ConstU64<1>;
    type TipFindersFee = TipFindersFee;
    type TipReportDepositBase = ConstU64<1>;
    type DataDepositPerByte = ConstU64<1>;
    type Event = Event;
    type WeightInfo = ();
}

pub const INITIAL_FUNDING: u64 = 150;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut ext: sp_io::TestExternalities = GenesisConfig {
        system: frame_system::GenesisConfig::default(),
        balances: pallet_balances::GenesisConfig {
            balances: vec![(0, 100), (1, 98), (2, 1)],
        },
        treasury: Default::default(),
        treasury_1: Default::default(),
        treasury_2: Default::default(),
	}
	.build_storage()
	.unwrap()
	.into();
	ext.execute_with(|| System::set_block_number(1));
	ext
}

pub fn genesis_test_ext() -> sp_io::TestExternalities {
    let mut ext: sp_io::TestExternalities = GenesisConfig {
        system: frame_system::GenesisConfig::default(),
        balances: pallet_balances::GenesisConfig {
            balances: vec![(0, 100), (Treasury::account_id(), INITIAL_FUNDING)],
        },
        treasury: Default::default(),
        treasury_1: Default::default(),
        treasury_2: Default::default(),
    }
    .build_storage()
    .unwrap()
    .into();
    ext.execute_with(|| System::set_block_number(1));
    ext
}

fn last_event() -> TipEvent<Test, Instance1> {
	System::events()
		.into_iter()
		.map(|r| r.event)
		.filter_map(|e| if let Event::Tips1(inner) = e { Some(inner) } else { None })
		.last()
		.unwrap()
}

#[test]
fn genesis_config_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Treasury1::pot(), 0);
		assert_eq!(Treasury1::proposal_count(), 0);

        assert_eq!(Treasury2::pot(), 0);
        assert_eq!(Treasury2::proposal_count(), 0);
	});
}

fn tip_hash() -> H256 {
	BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 3u128))
}

#[test]
fn tip_new_cannot_be_used_twice() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
        assert_eq!(Balances::free_balance(&Treasury1::account_id()), 101);
		assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		assert_noop!(
			Tips1::tip_new(Origin::signed(11), b"awesome.dot".to_vec(), 3, 10),
			Error::<Test, Instance1>::AlreadyKnown
		);

        Balances::make_free_balance_be(&Treasury2::account_id(), 202);
        assert_eq!(Balances::free_balance(&Treasury2::account_id()), 202);
        assert_ok!(Tips2::tip_new(Origin::signed(12), b"awesome.dot".to_vec(), 3, 10));
        assert_noop!(Tips2::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10), Error::<Test, Instance2>::AlreadyKnown);
	});
}

#[test]
fn report_awesome_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);

		// other reports don't count.
		assert_noop!(
			Tips1::report_awesome(Origin::signed(1), b"awesome.dot".to_vec(), 3),
			Error::<Test, Instance1>::AlreadyKnown
		);

		let h = tip_hash();
		assert_ok!(Tips1::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Tips1::tip(Origin::signed(9), h.clone(), 10), BadOrigin);
		System::set_block_number(2);
		assert_ok!(Tips1::close_tip(Origin::signed(100), h.into()));
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 102);
		assert_eq!(Balances::free_balance(3), 8);

        Balances::make_free_balance_be(&Treasury2::account_id(), 111);
        assert_ok!(Tips2::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
        assert_eq!(Balances::reserved_balance(0), 12);
        assert_eq!(Balances::free_balance(0), 90);

        // other reports don't count.
        assert_noop!(
            Tips2::report_awesome(Origin::signed(1), b"awesome.dot".to_vec(), 3),
            Error::<Test, Instance2>::AlreadyKnown
        );

        let h = tip_hash();
        assert_ok!(Tips2::tip(Origin::signed(10), h.clone(), 10));
        assert_ok!(Tips2::tip(Origin::signed(11), h.clone(), 10));
        assert_ok!(Tips2::tip(Origin::signed(12), h.clone(), 10));
        assert_noop!(Tips2::tip(Origin::signed(9), h.clone(), 10), BadOrigin);
        System::set_block_number(3);
        assert_ok!(Tips2::close_tip(Origin::signed(100), h.into()));
        assert_eq!(Balances::reserved_balance(0), 0);
        assert_eq!(Balances::free_balance(0), 104);
        assert_eq!(Balances::free_balance(3), 16);
	});
}

#[test]
fn report_awesome_from_beneficiary_and_tip_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 0));
		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);
		let h = BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 0u128));
		assert_ok!(Tips1::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(Tips1::close_tip(Origin::signed(100), h.into()));
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 110);

        Balances::make_free_balance_be(&Treasury2::account_id(), 111);
        assert_ok!(Tips2::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 0));
        assert_eq!(Balances::reserved_balance(0), 12);
        assert_eq!(Balances::free_balance(0), 98);
        let h = BlakeTwo256::hash_of(&(BlakeTwo256::hash(b"awesome.dot"), 0u128));
        assert_ok!(Tips2::tip(Origin::signed(10), h.clone(), 10));
        assert_ok!(Tips2::tip(Origin::signed(11), h.clone(), 10));
        assert_ok!(Tips2::tip(Origin::signed(12), h.clone(), 10));
        System::set_block_number(3);
        assert_ok!(Tips2::close_tip(Origin::signed(100), h.into()));
        assert_eq!(Balances::reserved_balance(0), 0);
        assert_eq!(Balances::free_balance(0), 120);
	});
}

#[test]
fn close_tip_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_eq!(Treasury1::pot(), 100);

		assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));

		let h = tip_hash();

		assert_eq!(last_event(), TipEvent::NewTip { tip_hash: h });

		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));

		assert_noop!(Tips1::close_tip(Origin::signed(0), h.into()), Error::<Test, Instance1>::StillOpen);

		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10));

		assert_eq!(last_event(), TipEvent::TipClosing { tip_hash: h });

		assert_noop!(Tips1::close_tip(Origin::signed(0), h.into()), Error::<Test, Instance1>::Premature);

		System::set_block_number(2);
		assert_noop!(Tips1::close_tip(Origin::none(), h.into()), BadOrigin);
		assert_ok!(Tips1::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);

		assert_eq!(last_event(), TipEvent::TipClosed { tip_hash: h, who: 3, payout: 10 });

		assert_noop!(Tips1::close_tip(Origin::signed(100), h.into()), Error::<Test, Instance1>::UnknownTip);

        Balances::make_free_balance_be(&Treasury1::account_id(), 201);
        assert_eq!(Treasury1::pot(), 200);

        assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));


	});
}

#[test]
fn slash_tip_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_eq!(Treasury1::pot(), 100);

		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 100);

		assert_ok!(Tips1::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));

		assert_eq!(Balances::reserved_balance(0), 12);
		assert_eq!(Balances::free_balance(0), 88);

		let h = tip_hash();
		assert_eq!(last_event(), TipEvent::NewTip { tip_hash: h });

		// can't remove from any origin
		assert_noop!(Tips1::slash_tip(Origin::signed(0), h.clone()), BadOrigin);

		// can remove from root.
		assert_ok!(Tips1::slash_tip(Origin::root(), h.clone()));
		assert_eq!(last_event(), TipEvent::TipSlashed { tip_hash: h, finder: 0, deposit: 12 });

		// tipper slashed
		assert_eq!(Balances::reserved_balance(0), 0);
		assert_eq!(Balances::free_balance(0), 88);
	});
}

#[test]
fn retract_tip_works() {
	new_test_ext().execute_with(|| {
		// with report awesome
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::report_awesome(Origin::signed(0), b"awesome.dot".to_vec(), 3));
		let h = tip_hash();
		assert_ok!(Tips1::tip(Origin::signed(10), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Tips1::retract_tip(Origin::signed(10), h.clone()), Error::<Test, Instance1>::NotFinder);
		assert_ok!(Tips1::retract_tip(Origin::signed(0), h.clone()));
		System::set_block_number(2);
		assert_noop!(Tips1::close_tip(Origin::signed(0), h.into()), Error::<Test, Instance1>::UnknownTip);

		// with tip new
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10));
		let h = tip_hash();
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10));
		assert_noop!(Tips1::retract_tip(Origin::signed(0), h.clone()), Error::<Test, Instance1>::NotFinder);
		assert_ok!(Tips1::retract_tip(Origin::signed(10), h.clone()));
		System::set_block_number(2);
		assert_noop!(Tips1::close_tip(Origin::signed(10), h.into()), Error::<Test, Instance1>::UnknownTip);
	});
}

#[test]
fn tip_median_calculation_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 0));
		let h = tip_hash();
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 1000000));
		System::set_block_number(2);
		assert_ok!(Tips1::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn tip_changing_works() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&Treasury1::account_id(), 101);
		assert_ok!(Tips1::tip_new(Origin::signed(10), b"awesome.dot".to_vec(), 3, 10000));
		let h = tip_hash();
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 10000));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 10000));
		assert_ok!(Tips1::tip(Origin::signed(13), h.clone(), 0));
		assert_ok!(Tips1::tip(Origin::signed(14), h.clone(), 0));
		assert_ok!(Tips1::tip(Origin::signed(12), h.clone(), 1000));
		assert_ok!(Tips1::tip(Origin::signed(11), h.clone(), 100));
		assert_ok!(Tips1::tip(Origin::signed(10), h.clone(), 10));
		System::set_block_number(2);
		assert_ok!(Tips1::close_tip(Origin::signed(0), h.into()));
		assert_eq!(Balances::free_balance(3), 10);
	});
}

#[test]
fn test_last_reward_migration() {
	let mut s = Storage::default();

	#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
	pub struct OldOpenTip<
		AccountId: Parameter,
		Balance: Parameter,
		BlockNumber: Parameter,
		Hash: Parameter,
	> {
		/// The hash of the reason for the tip. The reason should be a human-readable UTF-8 encoded
		/// string. A URL would be sensible.
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
		tips: vec![(40, 50), (60, 70)],
	};

	let reason2 = BlakeTwo256::hash(b"reason2");
	let hash2 = BlakeTwo256::hash_of(&(reason2, 20u64));

	let old_tip_no_finder = OldOpenTip::<u128, u64, u64, H256> {
		reason: reason2,
		who: 20,
		finder: None,
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)],
	};

	let data = vec![
		(pallet_tips::Tips::<Test, Instance1>::hashed_key_for(hash1), old_tip_finder.encode().to_vec()),
		(pallet_tips::Tips::<Test, Instance1>::hashed_key_for(hash2), old_tip_no_finder.encode().to_vec()),
	];

	s.top = data.into_iter().collect();

	sp_io::TestExternalities::new(s).execute_with(|| {
		let module = pallet_tips::Tips::<Test, Instance1>::module_prefix();
		let item = pallet_tips::Tips::<Test, Instance1>::storage_prefix();
		Tips1::migrate_retract_tip_for_tip_new(module, item);

		// Test w/ finder
		assert_eq!(
			pallet_tips::Tips::<Test, Instance1>::get(hash1),
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
			pallet_tips::Tips::<Test, Instance1>::get(hash2),
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
fn test_migration_v4() {
	let reason1 = BlakeTwo256::hash(b"reason1");
	let hash1 = BlakeTwo256::hash_of(&(reason1, 10u64));

	let tip = OpenTip::<u128, u64, u64, H256> {
		reason: reason1,
		who: 10,
		finder: 20,
		deposit: 30,
		closes: Some(13),
		tips: vec![(40, 50), (60, 70)],
		finders_fee: true,
	};

	let data = vec![
		(pallet_tips::Reasons::<Test, Instance1>::hashed_key_for(hash1), reason1.encode().to_vec()),
		(pallet_tips::Tips::<Test, Instance1>::hashed_key_for(hash1), tip.encode().to_vec()),
	];

	let mut s = Storage::default();
	s.top = data.into_iter().collect();

	sp_io::TestExternalities::new(s).execute_with(|| {
		use frame_support::traits::PalletInfoAccess;

		let old_pallet = "Treasury1";
		let new_pallet = <Tips1 as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<Tips1>();

		crate::migrations::v4::pre_migrate::<Test, Tips1, _>(old_pallet);
		crate::migrations::v4::migrate::<Test, Tips1, _>(old_pallet);
		crate::migrations::v4::post_migrate::<Test, Tips1, _>(old_pallet);
	});

	sp_io::TestExternalities::new(Storage::default()).execute_with(|| {
		use frame_support::traits::PalletInfoAccess;

		let old_pallet = "Treasury1";
		let new_pallet = <Tips1 as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<Tips1>();

		crate::migrations::v4::pre_migrate::<Test, Tips1, _>(old_pallet);
		crate::migrations::v4::migrate::<Test, Tips1, _>(old_pallet);
		crate::migrations::v4::post_migrate::<Test, Tips1, _>(old_pallet);
	});
}

#[test]
fn genesis_funding_works() {
	genesis_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(Treasury1::account_id()), 150);
		assert_eq!(Treasury1::pot(), INITIAL_FUNDING - Balances::minimum_balance());

        assert_eq!(Balances::free_balance(Treasury2::account_id()), 150);
        assert_eq!(Treasury2::pot(), INITIAL_FUNDING - Balances::minimum_balance());
	});
}
