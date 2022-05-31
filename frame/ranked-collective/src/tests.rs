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
	traits::{ConstU32, ConstU64, Everything, Polling},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup, Identity},
};

use super::*;
use crate as pallet_ranked_collective;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Club: pallet_ranked_collective::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1_000_000);
}
impl frame_system::Config for Test {
	type BaseCallFilter = Everything;
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
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TestPollState {
	Ongoing(TallyOf<Test>, Rank),
	Completed(u64, bool),
}
use TestPollState::*;

parameter_types! {
	pub static Polls: BTreeMap<u8, TestPollState> = vec![
		(1, Completed(1, true)),
		(2, Completed(2, false)),
		(3, Ongoing(Tally::from_parts(0, 0, 0), 1)),
	].into_iter().collect();
}

pub struct TestPolls;
impl Polling<TallyOf<Test>> for TestPolls {
	type Index = u8;
	type Votes = Votes;
	type Moment = u64;
	type Class = Rank;
	fn classes() -> Vec<Self::Class> {
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
		f: impl FnOnce(PollStatus<&mut TallyOf<Test>, Self::Moment, Self::Class>) -> R,
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
		f: impl FnOnce(
			PollStatus<&mut TallyOf<Test>, Self::Moment, Self::Class>,
		) -> Result<R, DispatchError>,
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
		polls.insert(i, Ongoing(Tally::new(class), class));
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
	type WeightInfo = ();
	type Event = Event;
	type AdminOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type Polls = TestPolls;
	type MinRankOfClass = Identity;
	type VoteWeight = Geometric;
	type TestGetter = frame_support::storage::KeyLenOf<Voting<Test>>;
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

fn member_count(r: Rank) -> MemberIndex {
	MemberCount::<Test>::get(r)
}

#[allow(dead_code)]
fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}

fn tally(index: u8) -> TallyOf<Test> {
	<TestPolls as Polling<TallyOf<Test>>>::as_ongoing(index).expect("No poll").0
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
fn member_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_ok!(Club::promote_member(Origin::root(), 1));
		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 0);
		assert_eq!(member_count(1), 0);
	});
}

#[test]
fn add_remove_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Club::add_member(Origin::signed(1), 1), DispatchError::BadOrigin);
		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_eq!(member_count(0), 1);

		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 0);

		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_eq!(member_count(0), 1);

		assert_ok!(Club::add_member(Origin::root(), 2));
		assert_eq!(member_count(0), 2);

		assert_ok!(Club::add_member(Origin::root(), 3));
		assert_eq!(member_count(0), 3);

		assert_ok!(Club::demote_member(Origin::root(), 3));
		assert_eq!(member_count(0), 2);

		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 1);

		assert_ok!(Club::demote_member(Origin::root(), 2));
		assert_eq!(member_count(0), 0);
	});
}

#[test]
fn promote_demote_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Club::add_member(Origin::signed(1), 1), DispatchError::BadOrigin);
		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_eq!(member_count(0), 1);
		assert_eq!(member_count(1), 0);

		assert_ok!(Club::add_member(Origin::root(), 2));
		assert_eq!(member_count(0), 2);
		assert_eq!(member_count(1), 0);

		assert_ok!(Club::promote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 2);
		assert_eq!(member_count(1), 1);

		assert_ok!(Club::promote_member(Origin::root(), 2));
		assert_eq!(member_count(0), 2);
		assert_eq!(member_count(1), 2);

		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 2);
		assert_eq!(member_count(1), 1);

		assert_noop!(Club::demote_member(Origin::signed(1), 1), DispatchError::BadOrigin);
		assert_ok!(Club::demote_member(Origin::root(), 1));
		assert_eq!(member_count(0), 1);
		assert_eq!(member_count(1), 1);
	});
}

#[test]
fn voting_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Club::add_member(Origin::root(), 0));
		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_ok!(Club::promote_member(Origin::root(), 1));
		assert_ok!(Club::add_member(Origin::root(), 2));
		assert_ok!(Club::promote_member(Origin::root(), 2));
		assert_ok!(Club::promote_member(Origin::root(), 2));
		assert_ok!(Club::add_member(Origin::root(), 3));
		assert_ok!(Club::promote_member(Origin::root(), 3));
		assert_ok!(Club::promote_member(Origin::root(), 3));
		assert_ok!(Club::promote_member(Origin::root(), 3));

		assert_noop!(Club::vote(Origin::signed(0), 3, true), Error::<Test>::RankTooLow);
		assert_eq!(tally(3), Tally::from_parts(0, 0, 0));

		assert_ok!(Club::vote(Origin::signed(1), 3, true));
		assert_eq!(tally(3), Tally::from_parts(1, 1, 0));
		assert_ok!(Club::vote(Origin::signed(1), 3, false));
		assert_eq!(tally(3), Tally::from_parts(0, 0, 1));

		assert_ok!(Club::vote(Origin::signed(2), 3, true));
		assert_eq!(tally(3), Tally::from_parts(1, 3, 1));
		assert_ok!(Club::vote(Origin::signed(2), 3, false));
		assert_eq!(tally(3), Tally::from_parts(0, 0, 4));

		assert_ok!(Club::vote(Origin::signed(3), 3, true));
		assert_eq!(tally(3), Tally::from_parts(1, 6, 4));
		assert_ok!(Club::vote(Origin::signed(3), 3, false));
		assert_eq!(tally(3), Tally::from_parts(0, 0, 10));
	});
}

#[test]
fn cleanup_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Club::add_member(Origin::root(), 1));
		assert_ok!(Club::promote_member(Origin::root(), 1));
		assert_ok!(Club::add_member(Origin::root(), 2));
		assert_ok!(Club::promote_member(Origin::root(), 2));
		assert_ok!(Club::add_member(Origin::root(), 3));
		assert_ok!(Club::promote_member(Origin::root(), 3));

		assert_ok!(Club::vote(Origin::signed(1), 3, true));
		assert_ok!(Club::vote(Origin::signed(2), 3, false));
		assert_ok!(Club::vote(Origin::signed(3), 3, true));

		assert_noop!(Club::cleanup_poll(Origin::signed(4), 3, 10), Error::<Test>::Ongoing);
		Polls::set(
			vec![(1, Completed(1, true)), (2, Completed(2, false)), (3, Completed(3, true))]
				.into_iter()
				.collect(),
		);
		assert_ok!(Club::cleanup_poll(Origin::signed(4), 3, 10));
		// NOTE: This will fail until #10016 is merged.
		//		assert_noop!(Club::cleanup_poll(Origin::signed(4), 3, 10), Error::<Test>::NoneRemaining);
	});
}
