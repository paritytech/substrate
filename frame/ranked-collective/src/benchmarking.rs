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

//! Staking pallet benchmarking.

use super::*;
#[allow(unused_imports)]
use crate::Pallet as RankedCollective;

use frame_benchmarking::{account, benchmarks_instance_pallet, whitelisted_caller};
use frame_support::{assert_ok, dispatch::UnfilteredDispatchable};
use frame_system::RawOrigin as SystemOrigin;

const SEED: u32 = 0;

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn make_member<T: Config<I>, I: 'static>(rank: Rank) -> T::AccountId {
	let who = account::<T::AccountId>("member", MemberCount::<T, I>::get(0), SEED);
	assert_ok!(Pallet::<T, I>::add_member(T::AdminOrigin::successful_origin(), who.clone()));
	for _ in 0..rank {
		promote_member::<T, I>(&who);
	}
	who
}

fn promote_member<T: Config<I>, I: 'static>(who: &T::AccountId) {
	assert_ok!(Pallet::<T, I>::promote(T::AdminOrigin::successful_origin(), who.clone()));
}

benchmarks_instance_pallet! {
	add_member {
		let who = account::<T::AccountId>("member", 0, SEED);
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::add_member { who: who.clone() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(MemberCount::<T, I>::get(0), 1);
		assert_last_event::<T, I>(Event::MemberAdded { who }.into());
	}

	remove_member {
		let first = make_member::<T, I>(0);
		let who = make_member::<T, I>(0);
		let last = make_member::<T, I>(0);
		let last_index = Members::<T, I>::get(&last).unwrap().index;
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::remove_member { who: who.clone() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(MemberCount::<T, I>::get(0), 2);
		assert_ne!(last_index, Members::<T, I>::get(&last).unwrap().index);
		assert_last_event::<T, I>(Event::MemberRemoved { who }.into());
	}

	promote {
		let who = make_member::<T, I>(0);
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::promote { who: who.clone() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(Members::<T, I>::get(&who).unwrap().rank, 1);
		assert_last_event::<T, I>(Event::RankChanged { who, rank: 1 }.into());
	}

	demote {
		let who = make_member::<T, I>(1);
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::demote { who: who.clone() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(Members::<T, I>::get(&who).unwrap().rank, 0);
		assert_last_event::<T, I>(Event::RankChanged { who, rank: 0 }.into());
	}

	vote {
		let caller: T::AccountId = whitelisted_caller();
		assert_ok!(Pallet::<T, I>::add_member(T::AdminOrigin::successful_origin(), caller.clone()));
		// Create a poll
		let class = 0;
		let poll = T::Polls::create_ongoing(class).expect("Must always be able to create a poll for rank 0");

		// Vote once.
		assert_ok!(Pallet::<T, I>::vote(SystemOrigin::Signed(caller.clone()).into(), poll, true));
	}: _(SystemOrigin::Signed(caller.clone()), poll, false)
	verify {
		let tally = Tally::from_parts(0, 0, 1);
		let ev = Event::Voted { who: caller, poll, vote: VoteRecord::Nay(1), tally };
		assert_last_event::<T, I>(ev.into());
	}

	cleanup_poll {
		let n in 1 .. 100;

		// Create a poll
		let class = 0;
		let poll = T::Polls::create_ongoing(class).expect("Must always be able to create a poll");

		// Vote in the poll by each of `n` members
		for i in 0..n {
			let who = make_member::<T, I>(0);
			assert_ok!(Pallet::<T, I>::vote(SystemOrigin::Signed(who).into(), poll, true));
		}

		// End the poll.
		T::Polls::end_ongoing(poll, false).expect("Must always be able to end a poll");

		assert_eq!(Voting::<T, I>::iter_prefix(poll).count(), n as usize);
	}: _(SystemOrigin::Signed(whitelisted_caller()), poll, n)
	verify {
		assert_eq!(Voting::<T, I>::iter().count(), 0);
	}

	impl_benchmark_test_suite!(RankedCollective, crate::tests::new_test_ext(), crate::tests::Test);
}
