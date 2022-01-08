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

//! ConvictionVoting pallet benchmarking.

use super::*;

use frame_benchmarking::{account, benchmarks, whitelist_account};
use frame_support::{
	assert_noop, assert_ok,
	codec::Decode,
	traits::{
		schedule::DispatchTime, Currency, EnsureOrigin, Get, OnInitialize, UnfilteredDispatchable,
	},
};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{BadOrigin, Bounded, One};

use crate::Pallet as ConvictionVoting;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

fn account_vote<T: Config>(b: BalanceOf<T>) -> AccountVote<BalanceOf<T>> {
	let v = Vote { aye: true, conviction: Conviction::Locked1x };

	AccountVote::Standard { vote: v, balance: b }
}

	/*
	vote_new {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		// We need to create existing direct votes
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");

		let referendum_index = add_referendum::<T>(r)?;
		whitelist_account!(caller);
	}: vote(RawOrigin::Signed(caller.clone()), referendum_index, account_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was not recorded.");
	}

	vote_existing {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		// We need to create existing direct votes
		for i in 0 ..=r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		// Change vote from aye to nay
		let nay = Vote { aye: false, conviction: Conviction::Locked1x };
		let new_vote = AccountVote::Standard { vote: nay, balance: 1000u32.into() };
		let referendum_index = ConvictionVoting::<T>::referendum_count() - 1;

		// This tests when a user changes a vote
		whitelist_account!(caller);
	}: vote(RawOrigin::Signed(caller.clone()), referendum_index, new_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was incorrectly added");
		let referendum_info = ConvictionVoting::<T>::referendum_info(referendum_index)
			.ok_or("referendum doesn't exist")?;
		let tally =  match referendum_info {
			PollInfo::Ongoing(r) => r.tally,
			_ => return Err("referendum not ongoing".into()),
		};
		assert_eq!(tally.nays, 1000u32.into(), "changed vote was not recorded");
	}

	delegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100u32.into();
		let delegated_balance: BalanceOf<T> = 1000u32.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will initially delegate to `old_delegate`
		let old_delegate: T::AccountId = funded_account::<T>("old_delegate", r);
		ConvictionVoting::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			old_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, old_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// Caller will now switch to `new_delegate`
		let new_delegate: T::AccountId = funded_account::<T>("new_delegate", r);
		let account_vote = account_vote::<T>(initial_balance);
		// We need to create existing direct votes for the `new_delegate`
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(new_delegate.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), new_delegate.clone(), Conviction::Locked1x, delegated_balance)
	verify {
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, new_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		let delegations = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { delegations, .. } => delegations,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(delegations.capital, delegated_balance, "delegation was not recorded.");
	}

	undelegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100u32.into();
		let delegated_balance: BalanceOf<T> = 1000u32.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will delegate
		let the_delegate: T::AccountId = funded_account::<T>("delegate", r);
		ConvictionVoting::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			the_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, the_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// We need to create votes direct votes for the `delegate`
		let account_vote = account_vote::<T>(initial_balance);
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(
				RawOrigin::Signed(the_delegate.clone()).into(),
				ref_idx,
				account_vote.clone()
			)?;
		}
		let votes = match VotingOf::<T>::get(&the_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		// Voting should now be direct
		match VotingOf::<T>::get(&caller) {
			Voting::Direct { .. } => (),
			_ => return Err("undelegation failed".into()),
		}
	}

	// Test when unlock will set a new value
	unlock {
		let r in 1 .. MAX_REFERENDUMS;

		let locker = funded_account::<T>("locker", 0);
		// Populate votes so things are locked
		let base_balance: BalanceOf<T> = 100u32.into();
		let small_vote = account_vote::<T>(base_balance);
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_idx, small_vote.clone())?;
		}

		// Create a big vote so lock increases
		let big_vote = account_vote::<T>(base_balance * 10u32.into());
		let referendum_index = add_referendum::<T>(r)?;
		ConvictionVoting::<T>::vote(RawOrigin::Signed(locker.clone()).into(), referendum_index, big_vote)?;

		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		let voting = VotingOf::<T>::get(&locker);
		assert_eq!(voting.locked_balance(), base_balance * 10u32.into());

		ConvictionVoting::<T>::remove_vote(RawOrigin::Signed(locker.clone()).into(), referendum_index)?;

		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: unlock(RawOrigin::Signed(caller), locker.clone())
	verify {
		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Vote was not removed");

		let voting = VotingOf::<T>::get(&locker);
		// Note that we may want to add a `get_lock` api to actually verify
		assert_eq!(voting.locked_balance(), base_balance);
	}

	remove_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let referendum_index = r - 1;
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), referendum_index)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	// Worst case is when target == caller and referendum is ongoing
	remove_other_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", r);
		let account_vote = account_vote::<T>(100u32.into());

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			ConvictionVoting::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let referendum_index = r - 1;
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), caller.clone(), referendum_index)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}*/
benchmarks! {
	unlock {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
		let class = <T as Config>::Polls::classes().into_iter().next().unwrap();
	}: _(RawOrigin::Signed(caller.clone()), class, caller.clone())

	impl_benchmark_test_suite!(
		ConvictionVoting,
		crate::tests::new_test_ext(),
		crate::tests::Test
	);
}
