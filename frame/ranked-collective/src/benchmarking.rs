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
	let who = account::<T::AccountId>("member", MemberCount::<T, I>::get().0, SEED);
	assert_ok!(Pallet::<T, I>::add_member(T::AdminOrigin::successful_origin(), who.clone(), rank));
	who
}

benchmarks_instance_pallet! {
	add_member {
		let old = MemberCount::<T, I>::get().0;
		let who = account::<T::AccountId>("member", 0, SEED);
		let rank = 1;
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::add_member { who: who.clone(), rank };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(MemberCount::<T, I>::get().0, old + 1);
		assert_last_event::<T, I>(Event::MemberAdded { who, rank }.into());
	}

	remove_member {
		let rank = 1;
		let who = make_member::<T, I>(rank);
		let other = make_member::<T, I>(rank);
		let old = MemberCount::<T, I>::get().0;
		let other_index = Members::<T, I>::get(&other).unwrap().index;
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::remove_member { who: who.clone() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(MemberCount::<T, I>::get().0, old - 1);
		assert_ne!(other_index, Members::<T, I>::get(&other).unwrap().index);
		assert_last_event::<T, I>(Event::MemberRemoved { who }.into());
	}

	set_member_rank {
		let old_rank = 1;
		let rank = 2;
		let who = make_member::<T, I>(old_rank);
		let origin = T::AdminOrigin::successful_origin();
		let call = Call::<T, I>::set_member_rank { who: who.clone(), rank };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_eq!(Members::<T, I>::get(&who).unwrap().rank, rank);
		assert_last_event::<T, I>(Event::RankChanged { who, rank }.into());
	}

	vote {
		let rank = 1;
		let caller: T::AccountId = whitelisted_caller();
		assert_ok!(Pallet::<T, I>::add_member(T::AdminOrigin::successful_origin(), caller.clone(), rank));
		// Create a poll
		let class = T::Polls::classes().into_iter().next().expect("Must always be at least one class");
		let poll = T::Polls::create_ongoing(class).expect("Must always be able to create a poll");

		// Vote once.
		assert_ok!(Pallet::<T, I>::vote(SystemOrigin::Signed(caller.clone()).into(), poll, true));
	}: _(SystemOrigin::Signed(caller.clone()), poll, false)
	verify {
		let tally = Tally::from_parts(0, 1);
		let ev = Event::Voted { who: caller, poll, vote: VoteRecord::Nay(1), tally };
		assert_last_event::<T, I>(ev.into());
	}

	cleanup_poll {
		let rank = 1;
		let n in 1 .. 100;

		// Create a poll
		let class = T::Polls::classes().into_iter().next().expect("Must always be at least one class");
		let poll = T::Polls::create_ongoing(class).expect("Must always be able to create a poll");

		// Vote in the poll by each of `n` members
		for i in 0..n {
			let who = make_member::<T, I>(rank);
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
