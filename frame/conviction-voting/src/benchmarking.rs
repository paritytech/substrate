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

use assert_matches::assert_matches;
use frame_benchmarking::{account, benchmarks_instance_pallet, whitelist_account};
use frame_support::{
	dispatch::RawOrigin,
	traits::{Currency, Get},
};
use sp_runtime::traits::Bounded;
use sp_std::collections::btree_map::BTreeMap;

use crate::Pallet as ConvictionVoting;

const SEED: u32 = 0;

/// Fill all classes as much as possible up to `MaxVotes` and return the Class with the most votes
/// ongoing.
fn fill_voting<T: Config<I>, I: 'static>(
) -> (ClassOf<T, I>, BTreeMap<ClassOf<T, I>, Vec<IndexOf<T, I>>>) {
	let mut r = BTreeMap::<ClassOf<T, I>, Vec<IndexOf<T, I>>>::new();
	for class in T::Polls::classes().into_iter() {
		for _ in 0..T::MaxVotes::get() {
			match T::Polls::create_ongoing(class.clone()) {
				Ok(i) => r.entry(class.clone()).or_default().push(i),
				Err(()) => break,
			}
		}
	}
	let c = r.iter().max_by_key(|(_, v)| v.len()).unwrap().0.clone();
	(c, r)
}

fn funded_account<T: Config<I>, I: 'static>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
	caller
}

fn account_vote<T: Config<I>, I: 'static>(b: BalanceOf<T, I>) -> AccountVote<BalanceOf<T, I>> {
	let v = Vote { aye: true, conviction: Conviction::Locked1x };

	AccountVote::Standard { vote: v, balance: b }
}

benchmarks_instance_pallet! {
	where_clause {  where T::MaxVotes: core::fmt::Debug }

	vote_new {
		let caller = funded_account::<T, I>("caller", 0);
		whitelist_account!(caller);
		let account_vote = account_vote::<T, I>(100u32.into());

		let (class, all_polls) = fill_voting::<T, I>();
		let polls = &all_polls[&class];
		let r = polls.len() - 1;
		// We need to create existing votes
		for i in polls.iter().skip(1) {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(caller.clone()).into(), *i, account_vote)?;
		}
		let votes = match VotingFor::<T, I>::get(&caller, &class) {
			Voting::Casting(Casting { votes, .. }) => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");

		let index = polls[0];
	}: vote(RawOrigin::Signed(caller.clone()), index, account_vote)
	verify {
		assert_matches!(
			VotingFor::<T, I>::get(&caller, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == (r + 1) as usize
		);
	}

	vote_existing {
		let caller = funded_account::<T, I>("caller", 0);
		whitelist_account!(caller);
		let old_account_vote = account_vote::<T, I>(100u32.into());

		let (class, all_polls) = fill_voting::<T, I>();
		let polls = &all_polls[&class];
		let r = polls.len();
		// We need to create existing votes
		for i in polls.iter() {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(caller.clone()).into(), *i, old_account_vote)?;
		}
		let votes = match VotingFor::<T, I>::get(&caller, &class) {
			Voting::Casting(Casting { votes, .. }) => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r, "Votes were not recorded.");

		let new_account_vote = account_vote::<T, I>(200u32.into());
		let index = polls[0];
	}: vote(RawOrigin::Signed(caller.clone()), index, new_account_vote)
	verify {
		assert_matches!(
			VotingFor::<T, I>::get(&caller, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == r as usize
		);
	}

	remove_vote {
		let caller = funded_account::<T, I>("caller", 0);
		whitelist_account!(caller);
		let old_account_vote = account_vote::<T, I>(100u32.into());

		let (class, all_polls) = fill_voting::<T, I>();
		let polls = &all_polls[&class];
		let r = polls.len();
		// We need to create existing votes
		for i in polls.iter() {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(caller.clone()).into(), *i, old_account_vote)?;
		}
		let votes = match VotingFor::<T, I>::get(&caller, &class) {
			Voting::Casting(Casting { votes, .. }) => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r, "Votes were not recorded.");

		let index = polls[0];
	}: _(RawOrigin::Signed(caller.clone()), Some(class.clone()), index)
	verify {
		assert_matches!(
			VotingFor::<T, I>::get(&caller, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == (r - 1) as usize
		);
	}

	remove_other_vote {
		let caller = funded_account::<T, I>("caller", 0);
		let voter = funded_account::<T, I>("caller", 0);
		let voter_lookup = T::Lookup::unlookup(voter.clone());
		whitelist_account!(caller);
		let old_account_vote = account_vote::<T, I>(100u32.into());

		let (class, all_polls) = fill_voting::<T, I>();
		let polls = &all_polls[&class];
		let r = polls.len();
		// We need to create existing votes
		for i in polls.iter() {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(voter.clone()).into(), *i, old_account_vote)?;
		}
		let votes = match VotingFor::<T, I>::get(&caller, &class) {
			Voting::Casting(Casting { votes, .. }) => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r, "Votes were not recorded.");

		let index = polls[0];
		assert!(T::Polls::end_ongoing(index, false).is_ok());
	}: _(RawOrigin::Signed(caller.clone()), voter_lookup, class.clone(), index)
	verify {
		assert_matches!(
			VotingFor::<T, I>::get(&voter, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == (r - 1) as usize
		);
	}

	delegate {
		let r in 0 .. T::MaxVotes::get().min(T::Polls::max_ongoing().1);

		let all_polls = fill_voting::<T, I>().1;
		let class = T::Polls::max_ongoing().0;
		let polls = &all_polls[&class];
		let voter = funded_account::<T, I>("voter", 0);
		let voter_lookup = T::Lookup::unlookup(voter.clone());
		let caller = funded_account::<T, I>("caller", 0);
		whitelist_account!(caller);

		let delegated_balance: BalanceOf<T, I> = 1000u32.into();
		let delegate_vote = account_vote::<T, I>(delegated_balance);

		// We need to create existing delegations
		for i in polls.iter().take(r as usize) {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(voter.clone()).into(), *i, delegate_vote)?;
		}
		assert_matches!(
			VotingFor::<T, I>::get(&voter, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == r as usize
		);

	}: _(RawOrigin::Signed(caller.clone()), class.clone(), voter_lookup, Conviction::Locked1x, delegated_balance)
	verify {
		assert_matches!(VotingFor::<T, I>::get(&caller, &class), Voting::Delegating(_));
	}

	undelegate {
		let r in 0 .. T::MaxVotes::get().min(T::Polls::max_ongoing().1);

		let all_polls = fill_voting::<T, I>().1;
		let class = T::Polls::max_ongoing().0;
		let polls = &all_polls[&class];
		let voter = funded_account::<T, I>("voter", 0);
		let voter_lookup = T::Lookup::unlookup(voter.clone());
		let caller = funded_account::<T, I>("caller", 0);
		whitelist_account!(caller);

		let delegated_balance: BalanceOf<T, I> = 1000u32.into();
		let delegate_vote = account_vote::<T, I>(delegated_balance);

		ConvictionVoting::<T, I>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			class.clone(),
			voter_lookup,
			Conviction::Locked1x,
			delegated_balance,
		)?;

		// We need to create delegations
		for i in polls.iter().take(r as usize) {
			ConvictionVoting::<T, I>::vote(RawOrigin::Signed(voter.clone()).into(), *i, delegate_vote)?;
		}
		assert_matches!(
			VotingFor::<T, I>::get(&voter, &class),
			Voting::Casting(Casting { votes, .. }) if votes.len() == r as usize
		);
		assert_matches!(VotingFor::<T, I>::get(&caller, &class), Voting::Delegating(_));
	}: _(RawOrigin::Signed(caller.clone()), class.clone())
	verify {
		assert_matches!(VotingFor::<T, I>::get(&caller, &class), Voting::Casting(_));
	}

	unlock {
		let caller = funded_account::<T, I>("caller", 0);
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		whitelist_account!(caller);
		let normal_account_vote = account_vote::<T, I>(T::Currency::free_balance(&caller) - 100u32.into());
		let big_account_vote = account_vote::<T, I>(T::Currency::free_balance(&caller));

		// Fill everything up to the max by filling all classes with votes and voting on them all.
		let (class, all_polls) = fill_voting::<T, I>();
		assert!(all_polls.len() > 0);
		for (class, polls) in all_polls.iter() {
			assert!(polls.len() > 0);
			for i in polls.iter() {
				ConvictionVoting::<T, I>::vote(RawOrigin::Signed(caller.clone()).into(), *i, normal_account_vote)?;
			}
		}

		let orig_usable = <T::Currency as fungible::Inspect<T::AccountId>>::reducible_balance(&caller, false);
		let polls = &all_polls[&class];

		// Vote big on the class with the most ongoing votes of them to bump the lock and make it
		// hard to recompute when removed.
		ConvictionVoting::<T, I>::vote(RawOrigin::Signed(caller.clone()).into(), polls[0], big_account_vote)?;
		let now_usable = <T::Currency as fungible::Inspect<T::AccountId>>::reducible_balance(&caller, false);
		assert_eq!(orig_usable - now_usable, 100u32.into());

		// Remove the vote
		ConvictionVoting::<T, I>::remove_vote(RawOrigin::Signed(caller.clone()).into(), Some(class.clone()), polls[0])?;

		// We can now unlock on `class` from 200 to 100...
	}: _(RawOrigin::Signed(caller.clone()), class, caller_lookup)
	verify {
		assert_eq!(orig_usable, <T::Currency as fungible::Inspect<T::AccountId>>::reducible_balance(&caller, false));
	}

	impl_benchmark_test_suite!(
		ConvictionVoting,
		crate::tests::new_test_ext(),
		crate::tests::Test
	);
}
