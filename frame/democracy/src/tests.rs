// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use super::*;
use crate as pallet_democracy;
use codec::Encode;
use frame_support::{
	assert_noop, assert_ok, ord_parameter_types, parameter_types,
	traits::{
		ConstU32, ConstU64, Contains, EqualPrivilegeOnly, GenesisBuild, OnInitialize, SortedMembers,
	},
	weights::Weight,
};
use frame_system::{EnsureRoot, EnsureSignedBy};
use pallet_balances::{BalanceLock, Error as BalancesError};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BadOrigin, BlakeTwo256, IdentityLookup},
	Perbill,
};

mod cancellation;
mod decoders;
mod delegation;
mod external_proposing;
mod fast_tracking;
mod lock_voting;
mod preimage;
mod public_proposals;
mod scheduling;
mod voting;

const AYE: Vote = Vote { aye: true, conviction: Conviction::None };
const NAY: Vote = Vote { aye: false, conviction: Conviction::None };
const BIG_AYE: Vote = Vote { aye: true, conviction: Conviction::Locked1x };
const BIG_NAY: Vote = Vote { aye: false, conviction: Conviction::Locked1x };

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
		Scheduler: pallet_scheduler::{Pallet, Call, Storage, Config, Event<T>},
		Democracy: pallet_democracy::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
);

// Test that a fitlered call can be dispatched.
pub struct BaseFilter;
impl Contains<Call> for BaseFilter {
	fn contains(call: &Call) -> bool {
		!matches!(call, &Call::Balances(pallet_balances::Call::set_balance { .. }))
	}
}

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1_000_000);
}
impl frame_system::Config for Test {
	type BaseCallFilter = BaseFilter;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
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
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}
parameter_types! {
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) * BlockWeights::get().max_block;
}
impl pallet_scheduler::Config for Test {
	type Event = Event;
	type Origin = Origin;
	type PalletsOrigin = OriginCaller;
	type Call = Call;
	type MaximumWeight = MaximumSchedulerWeight;
	type ScheduleOrigin = EnsureRoot<u64>;
	type MaxScheduledPerBlock = ();
	type WeightInfo = ();
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
	type PreimageProvider = ();
	type NoPreimagePostponement = ();
}

impl pallet_balances::Config for Test {
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type MaxLocks = ConstU32<10>;
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub static PreimageByteDeposit: u64 = 0;
	pub static InstantAllowed: bool = false;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
	pub const Three: u64 = 3;
	pub const Four: u64 = 4;
	pub const Five: u64 = 5;
	pub const Six: u64 = 6;
}
pub struct OneToFive;
impl SortedMembers<u64> for OneToFive {
	fn sorted_members() -> Vec<u64> {
		vec![1, 2, 3, 4, 5]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}

impl Config for Test {
	type Proposal = Call;
	type Event = Event;
	type Currency = pallet_balances::Pallet<Self>;
	type EnactmentPeriod = ConstU64<2>;
	type LaunchPeriod = ConstU64<2>;
	type VotingPeriod = ConstU64<2>;
	type VoteLockingPeriod = ConstU64<3>;
	type FastTrackVotingPeriod = ConstU64<2>;
	type MinimumDeposit = ConstU64<1>;
	type ExternalOrigin = EnsureSignedBy<Two, u64>;
	type ExternalMajorityOrigin = EnsureSignedBy<Three, u64>;
	type ExternalDefaultOrigin = EnsureSignedBy<One, u64>;
	type FastTrackOrigin = EnsureSignedBy<Five, u64>;
	type CancellationOrigin = EnsureSignedBy<Four, u64>;
	type BlacklistOrigin = EnsureRoot<u64>;
	type CancelProposalOrigin = EnsureRoot<u64>;
	type VetoOrigin = EnsureSignedBy<OneToFive, u64>;
	type CooloffPeriod = ConstU64<2>;
	type PreimageByteDeposit = PreimageByteDeposit;
	type Slash = ();
	type InstantOrigin = EnsureSignedBy<Six, u64>;
	type InstantAllowed = InstantAllowed;
	type Scheduler = Scheduler;
	type MaxVotes = ConstU32<100>;
	type OperationalPreimageOrigin = EnsureSignedBy<Six, u64>;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = ();
	type MaxProposals = ConstU32<100>;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	pallet_democracy::GenesisConfig::<Test>::default()
		.assimilate_storage(&mut t)
		.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

/// Execute the function two times, with `true` and with `false`.
pub fn new_test_ext_execute_with_cond(execute: impl FnOnce(bool) -> () + Clone) {
	new_test_ext().execute_with(|| (execute.clone())(false));
	new_test_ext().execute_with(|| execute(true));
}

#[test]
fn params_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Democracy::referendum_count(), 0);
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);
	});
}

fn set_balance_proposal(value: u64) -> Vec<u8> {
	Call::Balances(pallet_balances::Call::set_balance { who: 42, new_free: value, new_reserved: 0 })
		.encode()
}

#[test]
fn set_balance_proposal_is_correctly_filtered_out() {
	for i in 0..10 {
		let call = Call::decode(&mut &set_balance_proposal(i)[..]).unwrap();
		assert!(!<Test as frame_system::Config>::BaseCallFilter::contains(&call));
	}
}

fn set_balance_proposal_hash(value: u64) -> H256 {
	BlakeTwo256::hash(&set_balance_proposal(value)[..])
}

fn set_balance_proposal_hash_and_note(value: u64) -> H256 {
	let p = set_balance_proposal(value);
	let h = BlakeTwo256::hash(&p[..]);
	match Democracy::note_preimage(Origin::signed(6), p) {
		Ok(_) => (),
		Err(x) if x == Error::<Test>::DuplicatePreimage.into() => (),
		Err(x) => panic!("{:?}", x),
	}
	h
}

fn propose_set_balance(who: u64, value: u64, delay: u64) -> DispatchResult {
	Democracy::propose(Origin::signed(who), set_balance_proposal_hash(value), delay)
}

fn propose_set_balance_and_note(who: u64, value: u64, delay: u64) -> DispatchResult {
	Democracy::propose(Origin::signed(who), set_balance_proposal_hash_and_note(value), delay)
}

fn next_block() {
	System::set_block_number(System::block_number() + 1);
	Scheduler::on_initialize(System::block_number());
	Democracy::begin_block(System::block_number());
}

fn fast_forward_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

fn begin_referendum() -> ReferendumIndex {
	System::set_block_number(0);
	assert_ok!(propose_set_balance_and_note(1, 2, 1));
	fast_forward_to(2);
	0
}

fn aye(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: AYE, balance: Balances::free_balance(&who) }
}

fn nay(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: NAY, balance: Balances::free_balance(&who) }
}

fn big_aye(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: BIG_AYE, balance: Balances::free_balance(&who) }
}

fn big_nay(who: u64) -> AccountVote<u64> {
	AccountVote::Standard { vote: BIG_NAY, balance: Balances::free_balance(&who) }
}

fn tally(r: ReferendumIndex) -> Tally<u64> {
	Democracy::referendum_status(r).unwrap().tally
}
