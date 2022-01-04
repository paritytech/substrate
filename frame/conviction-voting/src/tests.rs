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

use std::collections::BTreeMap;

use super::*;
use crate as pallet_conviction_voting;
use frame_support::{
	ord_parameter_types, parameter_types, assert_ok,
	traits::{ConstU32, Contains, SortedMembers},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

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
		Voting: pallet_conviction_voting::{Pallet, Call, Storage, Event<T>},
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
	pub const BlockHashCount: u64 = 250;
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
	type BlockHashCount = BlockHashCount;
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
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub const MaxLocks: u32 = 10;
}
impl pallet_balances::Config for Test {
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type MaxLocks = MaxLocks;
	type Balance = u64;
	type Event = Event;
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub const LaunchPeriod: u64 = 2;
	pub const VotingPeriod: u64 = 2;
	pub const FastTrackVotingPeriod: u64 = 2;
	pub const MinimumDeposit: u64 = 1;
	pub const EnactmentPeriod: u64 = 2;
	pub const VoteLockingPeriod: u64 = 3;
	pub const CooloffPeriod: u64 = 2;
	pub const MaxVotes: u32 = 100;
	pub const MaxProposals: u32 = 100;
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

pub struct TotalIssuanceOf<C: Currency<A>, A>(sp_std::marker::PhantomData<(C, A)>);
impl<C: Currency<A>, A> Get<C::Balance> for TotalIssuanceOf<C, A> {
	fn get() -> C::Balance {
		C::total_issuance()
	}
}

#[derive(Clone)]
pub enum TestPollState {
	Ongoing(TallyOf<Test>, u8),
	Completed(u64, bool),
}
use TestPollState::*;

parameter_types! {
	pub static Polls: BTreeMap<u8, TestPollState> = vec![
		(1, Completed(1, true)),
		(2, Completed(2, false)),
		(3, Ongoing(Tally::from_parts(0, 0, 0), 0)),
	].into_iter().collect();
}

pub struct TestReferenda;
impl frame_support::traits::Polls<TallyOf<Test>> for TestReferenda {
	type Index = u8;
	type Votes = u64;
	type Moment = u64;
	type Class = u8;
	fn classes() -> Vec<u8> { vec![0, 1, 2] }
	fn as_ongoing(index: u8) -> Option<(TallyOf<Test>, Self::Class)> {
		Polls::get().remove(&index)
			.and_then(|x| if let TestPollState::Ongoing(t, c) = x { Some((t, c)) } else { None })
	}
	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut TallyOf<Test>, u64, u8>) -> R,
	) -> R {
		let mut polls = Polls::get();
		let entry = polls.get_mut(&index);
		let r = match entry {
			Some(Ongoing(ref mut tally_mut_ref, class)) => {
				f(PollStatus::Ongoing(tally_mut_ref, *class))
			},
			Some(Completed(when, succeeded)) => {
				f(PollStatus::Completed(*when, *succeeded))
			},
			None => {
				f(PollStatus::None)
			}
		};
		Polls::set(polls);
		r
	}
	fn try_access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut TallyOf<Test>, u64, u8>) -> Result<R, DispatchError>,
	) -> Result<R, DispatchError> {
		let mut polls = Polls::get();
		let entry = polls.get_mut(&index);
		let r = match entry {
			Some(Ongoing(ref mut tally_mut_ref, class)) => {
				f(PollStatus::Ongoing(tally_mut_ref, *class))
			},
			Some(Completed(when, succeeded)) => {
				f(PollStatus::Completed(*when, *succeeded))
			},
			None => {
				f(PollStatus::None)
			}
		}?;
		Polls::set(polls);
		Ok(r)
	}
}

impl Config for Test {
	type Event = Event;
	type Currency = pallet_balances::Pallet<Self>;
	type VoteLockingPeriod = VoteLockingPeriod;
	type MaxVotes = MaxVotes;
	type WeightInfo = ();
	type MaxTurnout = TotalIssuanceOf<Balances, Self::AccountId>;
	type Referenda = TestReferenda;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (6, 60)],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

#[test]
fn params_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);
	});
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

fn aye(amount: u64, conviction: u8) -> AccountVote<u64> {
	let vote = Vote { aye: true, conviction: conviction.try_into().unwrap() };
	AccountVote::Standard { vote, balance: amount }
}

fn nay(amount: u64, conviction: u8) -> AccountVote<u64> {
	let vote = Vote { aye: false, conviction: conviction.try_into().unwrap() };
	AccountVote::Standard { vote, balance: amount }
}

fn tally(index: u8) -> TallyOf<Test> {
	<TestReferenda as frame_support::traits::Polls<TallyOf<Test>>>::as_ongoing(index)
		.expect("No poll")
		.0
}

fn class(index: u8) -> u8 {
	<TestReferenda as frame_support::traits::Polls<TallyOf<Test>>>::as_ongoing(index)
		.expect("No poll")
		.1
}

#[test]
#[ignore]
#[should_panic(expected = "No poll")]
fn unknown_poll_should_panic() {
	let _ = tally(0);
}

#[test]
#[ignore]
#[should_panic(expected = "No poll")]
fn completed_poll_should_panic() {
	let _ = tally(1);
}

#[test]
fn basic_stuff() {
	new_test_ext().execute_with(|| {
		assert_eq!(tally(3), Tally::from_parts(0, 0, 0));
	});
}

#[test]
fn basic_voting_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(2, 5)));
		assert_eq!(tally(3), Tally::from_parts(10, 0, 2));
		assert_ok!(Voting::vote(Origin::signed(1), 3, nay(2, 5)));
		assert_eq!(tally(3), Tally::from_parts(0, 10, 2));
		assert_eq!(Balances::usable_balance(1), 8);

		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(5, 1)));
		assert_eq!(tally(3), Tally::from_parts(5, 0, 5));
		assert_ok!(Voting::vote(Origin::signed(1), 3, nay(5, 1)));
		assert_eq!(tally(3), Tally::from_parts(0, 5, 5));
		assert_eq!(Balances::usable_balance(1), 5);

		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(10, 0)));
		assert_eq!(tally(3), Tally::from_parts(1, 0, 10));
		assert_ok!(Voting::vote(Origin::signed(1), 3, nay(10, 0)));
		assert_eq!(tally(3), Tally::from_parts(0, 1, 10));
		assert_eq!(Balances::usable_balance(1), 0);

		assert_ok!(Voting::remove_vote(Origin::signed(1), None, 3));
		assert_eq!(tally(3), Tally::from_parts(0, 0, 0));

		assert_ok!(Voting::unlock(Origin::signed(1), class(3), 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}
