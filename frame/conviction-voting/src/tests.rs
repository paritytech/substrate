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
	assert_noop, assert_ok, parameter_types,
	traits::{ConstU32, ConstU64, Contains, Polling},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

use super::*;
use crate as pallet_conviction_voting;

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
	type MaxConsumers = ConstU32<16>;
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

#[derive(Clone, PartialEq, Eq, Debug)]
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

pub struct TestPolls;
impl Polling<TallyOf<Test>> for TestPolls {
	type Index = u8;
	type Votes = u64;
	type Moment = u64;
	type Class = u8;
	fn classes() -> Vec<u8> {
		vec![0, 1, 2]
	}
	fn as_ongoing(index: u8) -> Option<(TallyOf<Test>, Self::Class)> {
		Polls::get().remove(&index).and_then(|x| {
			if let TestPollState::Ongoing(t, c) = x {
				Some((t, c))
			} else {
				None
			}
		})
	}
	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut TallyOf<Test>, u64, u8>) -> R,
	) -> R {
		let mut polls = Polls::get();
		let entry = polls.get_mut(&index);
		let r = match entry {
			Some(Ongoing(ref mut tally_mut_ref, class)) =>
				f(PollStatus::Ongoing(tally_mut_ref, *class)),
			Some(Completed(when, succeeded)) => f(PollStatus::Completed(*when, *succeeded)),
			None => f(PollStatus::None),
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
			Some(Ongoing(ref mut tally_mut_ref, class)) =>
				f(PollStatus::Ongoing(tally_mut_ref, *class)),
			Some(Completed(when, succeeded)) => f(PollStatus::Completed(*when, *succeeded)),
			None => f(PollStatus::None),
		}?;
		Polls::set(polls);
		Ok(r)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn create_ongoing(class: Self::Class) -> Result<Self::Index, ()> {
		let mut polls = Polls::get();
		let i = polls.keys().rev().next().map_or(0, |x| x + 1);
		polls.insert(i, Ongoing(Tally::default(), class));
		Polls::set(polls);
		Ok(i)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn end_ongoing(index: Self::Index, approved: bool) -> Result<(), ()> {
		let mut polls = Polls::get();
		match polls.get(&index) {
			Some(Ongoing(..)) => {},
			_ => return Err(()),
		}
		let now = frame_system::Pallet::<Test>::block_number();
		polls.insert(index, Completed(now, approved));
		Polls::set(polls);
		Ok(())
	}
}

impl Config for Test {
	type Event = Event;
	type Currency = pallet_balances::Pallet<Self>;
	type VoteLockingPeriod = ConstU64<3>;
	type MaxVotes = ConstU32<3>;
	type WeightInfo = ();
	type MaxTurnout = frame_support::traits::TotalIssuanceOf<Balances, Self::AccountId>;
	type Polls = TestPolls;
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
	<TestPolls as Polling<TallyOf<Test>>>::as_ongoing(index).expect("No poll").0
}

fn class(index: u8) -> u8 {
	<TestPolls as Polling<TallyOf<Test>>>::as_ongoing(index).expect("No poll").1
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

#[test]
fn voting_balance_gets_locked() {
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

#[test]
fn successful_but_zero_conviction_vote_balance_can_be_unlocked() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(1, 1)));
		assert_ok!(Voting::vote(Origin::signed(2), 3, nay(20, 0)));
		let c = class(3);
		Polls::set(vec![(3, Completed(3, false))].into_iter().collect());
		assert_ok!(Voting::remove_vote(Origin::signed(2), Some(c), 3));
		assert_ok!(Voting::unlock(Origin::signed(2), c, 2));
		assert_eq!(Balances::usable_balance(2), 20);
	});
}

#[test]
fn unsuccessful_conviction_vote_balance_can_be_unlocked() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(1, 1)));
		assert_ok!(Voting::vote(Origin::signed(2), 3, nay(20, 0)));
		let c = class(3);
		Polls::set(vec![(3, Completed(3, false))].into_iter().collect());
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(c), 3));
		assert_ok!(Voting::unlock(Origin::signed(1), c, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn successful_conviction_vote_balance_stays_locked_for_correct_time() {
	new_test_ext().execute_with(|| {
		for i in 1..=5 {
			assert_ok!(Voting::vote(Origin::signed(i), 3, aye(10, i as u8)));
		}
		let c = class(3);
		Polls::set(vec![(3, Completed(3, true))].into_iter().collect());
		for i in 1..=5 {
			assert_ok!(Voting::remove_vote(Origin::signed(i), Some(c), 3));
		}
		for block in 1..=(3 + 5 * 3) {
			run_to(block);
			for i in 1..=5 {
				assert_ok!(Voting::unlock(Origin::signed(i), c, i));
				let expired = block >= (3 << (i - 1)) + 3;
				assert_eq!(Balances::usable_balance(i), i * 10 - if expired { 0 } else { 10 });
			}
		}
	});
}

#[test]
fn classwise_delegation_works() {
	new_test_ext().execute_with(|| {
		Polls::set(
			vec![
				(0, Ongoing(Tally::default(), 0)),
				(1, Ongoing(Tally::default(), 1)),
				(2, Ongoing(Tally::default(), 2)),
				(3, Ongoing(Tally::default(), 2)),
			]
			.into_iter()
			.collect(),
		);
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 5));
		assert_ok!(Voting::delegate(Origin::signed(1), 1, 3, Conviction::Locked1x, 5));
		assert_ok!(Voting::delegate(Origin::signed(1), 2, 4, Conviction::Locked1x, 5));
		assert_eq!(Balances::usable_balance(1), 5);

		assert_ok!(Voting::vote(Origin::signed(2), 0, aye(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(2), 1, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(2), 2, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(3), 0, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(3), 1, aye(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(3), 2, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(4), 0, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(4), 1, nay(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(4), 2, aye(10, 0)));
		// 4 hasn't voted yet

		assert_eq!(
			Polls::get(),
			vec![
				(0, Ongoing(Tally::from_parts(6, 2, 35), 0)),
				(1, Ongoing(Tally::from_parts(6, 2, 35), 1)),
				(2, Ongoing(Tally::from_parts(6, 2, 35), 2)),
				(3, Ongoing(Tally::from_parts(0, 0, 0), 2)),
			]
			.into_iter()
			.collect()
		);

		// 4 votes nay to 3.
		assert_ok!(Voting::vote(Origin::signed(4), 3, nay(10, 0)));
		assert_eq!(
			Polls::get(),
			vec![
				(0, Ongoing(Tally::from_parts(6, 2, 35), 0)),
				(1, Ongoing(Tally::from_parts(6, 2, 35), 1)),
				(2, Ongoing(Tally::from_parts(6, 2, 35), 2)),
				(3, Ongoing(Tally::from_parts(0, 6, 15), 2)),
			]
			.into_iter()
			.collect()
		);

		// Redelegate for class 2 to account 3.
		assert_ok!(Voting::undelegate(Origin::signed(1), 2));
		assert_ok!(Voting::delegate(Origin::signed(1), 2, 3, Conviction::Locked1x, 5));
		assert_eq!(
			Polls::get(),
			vec![
				(0, Ongoing(Tally::from_parts(6, 2, 35), 0)),
				(1, Ongoing(Tally::from_parts(6, 2, 35), 1)),
				(2, Ongoing(Tally::from_parts(1, 7, 35), 2)),
				(3, Ongoing(Tally::from_parts(0, 1, 10), 2)),
			]
			.into_iter()
			.collect()
		);

		// Redelegating with a lower lock does not forget previous lock and updates correctly.
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::undelegate(Origin::signed(1), 1));
		assert_ok!(Voting::undelegate(Origin::signed(1), 2));
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 3));
		assert_ok!(Voting::delegate(Origin::signed(1), 1, 3, Conviction::Locked1x, 3));
		assert_ok!(Voting::delegate(Origin::signed(1), 2, 4, Conviction::Locked1x, 3));
		assert_eq!(
			Polls::get(),
			vec![
				(0, Ongoing(Tally::from_parts(4, 2, 33), 0)),
				(1, Ongoing(Tally::from_parts(4, 2, 33), 1)),
				(2, Ongoing(Tally::from_parts(4, 2, 33), 2)),
				(3, Ongoing(Tally::from_parts(0, 4, 13), 2)),
			]
			.into_iter()
			.collect()
		);
		assert_eq!(Balances::usable_balance(1), 5);

		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		// unlock does nothing since the delegation already took place.
		assert_eq!(Balances::usable_balance(1), 5);

		// Redelegating with higher amount extends previous lock.
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 6));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 4);
		assert_ok!(Voting::undelegate(Origin::signed(1), 1));
		assert_ok!(Voting::delegate(Origin::signed(1), 1, 3, Conviction::Locked1x, 7));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_eq!(Balances::usable_balance(1), 3);
		assert_ok!(Voting::undelegate(Origin::signed(1), 2));
		assert_ok!(Voting::delegate(Origin::signed(1), 2, 4, Conviction::Locked1x, 8));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 2);
		assert_eq!(
			Polls::get(),
			vec![
				(0, Ongoing(Tally::from_parts(7, 2, 36), 0)),
				(1, Ongoing(Tally::from_parts(8, 2, 37), 1)),
				(2, Ongoing(Tally::from_parts(9, 2, 38), 2)),
				(3, Ongoing(Tally::from_parts(0, 9, 18), 2)),
			]
			.into_iter()
			.collect()
		);
	});
}

#[test]
fn redelegation_after_vote_ending_should_keep_lock() {
	new_test_ext().execute_with(|| {
		Polls::set(vec![(0, Ongoing(Tally::default(), 0))].into_iter().collect());
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 5));
		assert_ok!(Voting::vote(Origin::signed(2), 0, aye(10, 1)));
		Polls::set(vec![(0, Completed(1, true))].into_iter().collect());
		assert_eq!(Balances::usable_balance(1), 5);
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 3, Conviction::Locked1x, 3));
		assert_eq!(Balances::usable_balance(1), 5);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 5);
	});
}

#[test]
fn lock_amalgamation_valid_with_multiple_removed_votes() {
	new_test_ext().execute_with(|| {
		Polls::set(
			vec![
				(0, Ongoing(Tally::default(), 0)),
				(1, Ongoing(Tally::default(), 0)),
				(2, Ongoing(Tally::default(), 0)),
			]
			.into_iter()
			.collect(),
		);
		assert_ok!(Voting::vote(Origin::signed(1), 0, aye(5, 1)));
		assert_ok!(Voting::vote(Origin::signed(1), 1, aye(10, 1)));
		assert_ok!(Voting::vote(Origin::signed(1), 2, aye(5, 2)));
		assert_eq!(Balances::usable_balance(1), 0);

		Polls::set(
			vec![(0, Completed(1, true)), (1, Completed(1, true)), (2, Completed(1, true))]
				.into_iter()
				.collect(),
		);
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 0));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 2));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert!(Balances::usable_balance(1) <= 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn lock_amalgamation_valid_with_multiple_delegations() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 5));
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 10));
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked2x, 5));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert!(Balances::usable_balance(1) <= 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn lock_amalgamation_valid_with_move_roundtrip_to_delegation() {
	new_test_ext().execute_with(|| {
		Polls::set(vec![(0, Ongoing(Tally::default(), 0))].into_iter().collect());
		assert_ok!(Voting::vote(Origin::signed(1), 0, aye(5, 1)));
		Polls::set(vec![(0, Completed(1, true))].into_iter().collect());
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 0));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 5);

		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 10));
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		Polls::set(vec![(1, Ongoing(Tally::default(), 0))].into_iter().collect());
		assert_ok!(Voting::vote(Origin::signed(1), 1, aye(5, 2)));
		Polls::set(vec![(1, Completed(1, true))].into_iter().collect());
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 1));

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert!(Balances::usable_balance(1) <= 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn lock_amalgamation_valid_with_move_roundtrip_to_casting() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 5));
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));

		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 5);

		Polls::set(vec![(0, Ongoing(Tally::default(), 0))].into_iter().collect());
		assert_ok!(Voting::vote(Origin::signed(1), 0, aye(10, 1)));
		Polls::set(vec![(0, Completed(1, true))].into_iter().collect());
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 0));

		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked2x, 10));
		assert_ok!(Voting::undelegate(Origin::signed(1), 0));

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert!(Balances::usable_balance(1) <= 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn lock_aggregation_over_different_classes_with_delegation_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::Locked1x, 5));
		assert_ok!(Voting::delegate(Origin::signed(1), 1, 2, Conviction::Locked2x, 5));
		assert_ok!(Voting::delegate(Origin::signed(1), 2, 2, Conviction::Locked1x, 10));

		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		assert_ok!(Voting::undelegate(Origin::signed(1), 1));
		assert_ok!(Voting::undelegate(Origin::signed(1), 2));

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn lock_aggregation_over_different_classes_with_casting_works() {
	new_test_ext().execute_with(|| {
		Polls::set(
			vec![
				(0, Ongoing(Tally::default(), 0)),
				(1, Ongoing(Tally::default(), 1)),
				(2, Ongoing(Tally::default(), 2)),
			]
			.into_iter()
			.collect(),
		);
		assert_ok!(Voting::vote(Origin::signed(1), 0, aye(5, 1)));
		assert_ok!(Voting::vote(Origin::signed(1), 1, aye(10, 1)));
		assert_ok!(Voting::vote(Origin::signed(1), 2, aye(5, 2)));
		Polls::set(
			vec![(0, Completed(1, true)), (1, Completed(1, true)), (2, Completed(1, true))]
				.into_iter()
				.collect(),
		);
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(0), 0));
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(1), 1));
		assert_ok!(Voting::remove_vote(Origin::signed(1), Some(2), 2));

		run_to(3);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 0);

		run_to(6);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 5);

		run_to(7);
		assert_ok!(Voting::unlock(Origin::signed(1), 0, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 1, 1));
		assert_ok!(Voting::unlock(Origin::signed(1), 2, 1));
		assert_eq!(Balances::usable_balance(1), 10);
	});
}

#[test]
fn errors_with_vote_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(Voting::vote(Origin::signed(1), 0, aye(10, 0)), Error::<Test>::NotOngoing);
		assert_noop!(Voting::vote(Origin::signed(1), 1, aye(10, 0)), Error::<Test>::NotOngoing);
		assert_noop!(Voting::vote(Origin::signed(1), 2, aye(10, 0)), Error::<Test>::NotOngoing);
		assert_noop!(
			Voting::vote(Origin::signed(1), 3, aye(11, 0)),
			Error::<Test>::InsufficientFunds
		);

		assert_ok!(Voting::delegate(Origin::signed(1), 0, 2, Conviction::None, 10));
		assert_noop!(
			Voting::vote(Origin::signed(1), 3, aye(10, 0)),
			Error::<Test>::AlreadyDelegating
		);

		assert_ok!(Voting::undelegate(Origin::signed(1), 0));
		Polls::set(
			vec![
				(0, Ongoing(Tally::default(), 0)),
				(1, Ongoing(Tally::default(), 0)),
				(2, Ongoing(Tally::default(), 0)),
				(3, Ongoing(Tally::default(), 0)),
			]
			.into_iter()
			.collect(),
		);
		assert_ok!(Voting::vote(Origin::signed(1), 0, aye(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(1), 1, aye(10, 0)));
		assert_ok!(Voting::vote(Origin::signed(1), 2, aye(10, 0)));
		assert_noop!(
			Voting::vote(Origin::signed(1), 3, aye(10, 0)),
			Error::<Test>::MaxVotesReached
		);
	});
}

#[test]
fn errors_with_delegating_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Voting::delegate(Origin::signed(1), 0, 2, Conviction::None, 11),
			Error::<Test>::InsufficientFunds
		);
		assert_noop!(
			Voting::delegate(Origin::signed(1), 3, 2, Conviction::None, 10),
			Error::<Test>::BadClass
		);

		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(10, 0)));
		assert_noop!(
			Voting::delegate(Origin::signed(1), 0, 2, Conviction::None, 10),
			Error::<Test>::AlreadyVoting
		);

		assert_noop!(Voting::undelegate(Origin::signed(1), 0), Error::<Test>::NotDelegating);
	});
}

#[test]
fn remove_other_vote_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Voting::remove_other_vote(Origin::signed(2), 1, 0, 3),
			Error::<Test>::NotVoter
		);
		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(10, 2)));
		assert_noop!(
			Voting::remove_other_vote(Origin::signed(2), 1, 0, 3),
			Error::<Test>::NoPermission
		);
		Polls::set(vec![(3, Completed(1, true))].into_iter().collect());
		run_to(6);
		assert_noop!(
			Voting::remove_other_vote(Origin::signed(2), 1, 0, 3),
			Error::<Test>::NoPermissionYet
		);
		run_to(7);
		assert_ok!(Voting::remove_other_vote(Origin::signed(2), 1, 0, 3));
	});
}

#[test]
fn errors_with_remove_vote_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(Voting::remove_vote(Origin::signed(1), Some(0), 3), Error::<Test>::NotVoter);
		assert_ok!(Voting::vote(Origin::signed(1), 3, aye(10, 2)));
		Polls::set(vec![(3, Completed(1, true))].into_iter().collect());
		assert_noop!(Voting::remove_vote(Origin::signed(1), None, 3), Error::<Test>::ClassNeeded);
	});
}
