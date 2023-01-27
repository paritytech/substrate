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

//! Elections-Phragmen pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::{account, benchmarks, whitelist, BenchmarkError, BenchmarkResult};
use frame_support::{dispatch::DispatchResultWithPostInfo, traits::OnInitialize};
use frame_system::RawOrigin;

use crate::Pallet as Elections;

const BALANCE_FACTOR: u32 = 250;

/// grab new account with infinite balance.
fn endowed_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let account: T::AccountId = account(name, index, 0);
	// Fund each account with at-least their stake but still a sane amount as to not mess up
	// the vote calculation.
	let amount = default_stake::<T>(T::MaxVoters::get()) * BalanceOf::<T>::from(BALANCE_FACTOR);
	let _ = T::Currency::make_free_balance_be(&account, amount);
	// important to increase the total issuance since T::CurrencyToVote will need it to be sane for
	// phragmen to work.
	T::Currency::issue(amount);

	account
}

/// Account to lookup type of system trait.
fn as_lookup<T: Config>(account: T::AccountId) -> AccountIdLookupOf<T> {
	T::Lookup::unlookup(account)
}

/// Get a reasonable amount of stake based on the execution trait's configuration
fn default_stake<T: Config>(num_votes: u32) -> BalanceOf<T> {
	let min = T::Currency::minimum_balance();
	Elections::<T>::deposit_of(num_votes as usize).max(min)
}

/// Get the current number of candidates.
fn candidate_count<T: Config>() -> u32 {
	<Candidates<T>>::decode_len().unwrap_or(0usize) as u32
}

/// Add `c` new candidates.
fn submit_candidates<T: Config>(
	c: u32,
	prefix: &'static str,
) -> Result<Vec<T::AccountId>, &'static str> {
	(0..c)
		.map(|i| {
			let account = endowed_account::<T>(prefix, i);
			<Elections<T>>::submit_candidacy(
				RawOrigin::Signed(account.clone()).into(),
				candidate_count::<T>(),
			)
			.map_err(|_| "failed to submit candidacy")?;
			Ok(account)
		})
		.collect::<Result<_, _>>()
}

/// Add `c` new candidates with self vote.
fn submit_candidates_with_self_vote<T: Config>(
	c: u32,
	prefix: &'static str,
) -> Result<Vec<T::AccountId>, &'static str> {
	let candidates = submit_candidates::<T>(c, prefix)?;
	let stake = default_stake::<T>(c);
	let _ = candidates
		.iter()
		.try_for_each(|c| submit_voter::<T>(c.clone(), vec![c.clone()], stake).map(|_| ()))?;
	Ok(candidates)
}

/// Submit one voter.
fn submit_voter<T: Config>(
	caller: T::AccountId,
	votes: Vec<T::AccountId>,
	stake: BalanceOf<T>,
) -> DispatchResultWithPostInfo {
	<Elections<T>>::vote(RawOrigin::Signed(caller).into(), votes, stake)
}

/// create `num_voter` voters who randomly vote for at most `votes` of `all_candidates` if
/// available.
fn distribute_voters<T: Config>(
	mut all_candidates: Vec<T::AccountId>,
	num_voters: u32,
	votes: usize,
) -> Result<(), &'static str> {
	let stake = default_stake::<T>(num_voters);
	for i in 0..num_voters {
		// to ensure that votes are different
		all_candidates.rotate_left(1);
		let votes = all_candidates.iter().cloned().take(votes).collect::<Vec<_>>();
		let voter = endowed_account::<T>("voter", i);
		submit_voter::<T>(voter, votes, stake)?;
	}
	Ok(())
}

/// Fill the seats of members and runners-up up until `m`. Note that this might include either only
/// members, or members and runners-up.
fn fill_seats_up_to<T: Config>(m: u32) -> Result<Vec<T::AccountId>, &'static str> {
	let _ = submit_candidates_with_self_vote::<T>(m, "fill_seats_up_to")?;
	assert_eq!(<Elections<T>>::candidates().len() as u32, m, "wrong number of candidates.");
	<Elections<T>>::do_phragmen();
	assert_eq!(<Elections<T>>::candidates().len(), 0, "some candidates remaining.");
	assert_eq!(
		<Elections<T>>::members().len() + <Elections<T>>::runners_up().len(),
		m as usize,
		"wrong number of members and runners-up",
	);
	Ok(<Elections<T>>::members()
		.into_iter()
		.map(|m| m.who)
		.chain(<Elections<T>>::runners_up().into_iter().map(|r| r.who))
		.collect())
}

/// removes all the storage items to reverse any genesis state.
fn clean<T: Config>() {
	<Members<T>>::kill();
	<Candidates<T>>::kill();
	<RunnersUp<T>>::kill();
	#[allow(deprecated)]
	<Voting<T>>::remove_all(None);
}

benchmarks! {
	// -- Signed ones
	vote_equal {
		let v in 1 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		let stake = default_stake::<T>(v);

		// original votes.
		let mut votes = all_candidates;
		submit_voter::<T>(caller.clone(), votes.clone(), stake)?;

		// new votes.
		votes.rotate_left(1);

		whitelist!(caller);
	}: vote(RawOrigin::Signed(caller), votes, stake)

	vote_more {
		let v in 2 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		// Multiply the stake with 10 since we want to be able to divide it by 10 again.
		let stake = default_stake::<T>(v) * BalanceOf::<T>::from(10u32);

		// original votes.
		let mut votes = all_candidates.iter().skip(1).cloned().collect::<Vec<_>>();
		submit_voter::<T>(caller.clone(), votes.clone(), stake / <BalanceOf<T>>::from(10u32))?;

		// new votes.
		votes = all_candidates;
		assert!(votes.len() > <Voting<T>>::get(caller.clone()).votes.len());

		whitelist!(caller);
	}: vote(RawOrigin::Signed(caller), votes, stake / <BalanceOf<T>>::from(10u32))

	vote_less {
		let v in 2 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		let stake = default_stake::<T>(v);

		// original votes.
		let mut votes = all_candidates;
		submit_voter::<T>(caller.clone(), votes.clone(), stake)?;

		// new votes.
		votes = votes.into_iter().skip(1).collect::<Vec<_>>();
		assert!(votes.len() < <Voting<T>>::get(caller.clone()).votes.len());

		whitelist!(caller);
	}: vote(RawOrigin::Signed(caller), votes, stake)

	remove_voter {
		// we fix the number of voted candidates to max
		let v = MAXIMUM_VOTE as u32;
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);

		let stake = default_stake::<T>(v);
		submit_voter::<T>(caller.clone(), all_candidates, stake)?;

		whitelist!(caller);
	}: _(RawOrigin::Signed(caller))

	submit_candidacy {
		// number of already existing candidates.
		let c in 1 .. T::MaxCandidates::get();
		// we fix the number of members to the number of desired members and runners-up. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();

		clean::<T>();
		let stake = default_stake::<T>(c);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create previous candidates;
		let _ = submit_candidates::<T>(c, "candidates")?;

		// we assume worse case that: extrinsic is successful and candidate is not duplicate.
		let candidate_account = endowed_account::<T>("caller", 0);
		whitelist!(candidate_account);
	}: _(RawOrigin::Signed(candidate_account.clone()), candidate_count::<T>())
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	renounce_candidacy_candidate {
		// this will check members, runners-up and candidate for removal. Members and runners-up are
		// limited by the runtime bound, nonetheless we fill them by `m`.
		// number of already existing candidates.
		let c in 1 .. T::MaxCandidates::get();
		// we fix the number of members to the number of desired members and runners-up. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();

		clean::<T>();

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;
		let all_candidates = submit_candidates::<T>(c, "caller")?;

		let bailing = all_candidates[0].clone(); // Should be ("caller", 0)
		let count = candidate_count::<T>();
		whitelist!(bailing);
	}: renounce_candidacy(RawOrigin::Signed(bailing), Renouncing::Candidate(count))
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	renounce_candidacy_members {
		// removing members and runners will be cheaper than a candidate.
		// we fix the number of members to when members and runners-up to the desired. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		// create m members and runners combined.
		let members_and_runners_up = fill_seats_up_to::<T>(m)?;

		let bailing = members_and_runners_up[0].clone();
		assert!(<Elections<T>>::is_member(&bailing));

		whitelist!(bailing);
	}: renounce_candidacy(RawOrigin::Signed(bailing.clone()), Renouncing::Member)
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	renounce_candidacy_runners_up {
		// removing members and runners will be cheaper than a candidate.
		// we fix the number of members to when members and runners-up to the desired. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		// create m members and runners combined.
		let members_and_runners_up = fill_seats_up_to::<T>(m)?;

		let bailing = members_and_runners_up[T::DesiredMembers::get() as usize + 1].clone();
		assert!(<Elections<T>>::is_runner_up(&bailing));

		whitelist!(bailing);
	}: renounce_candidacy(RawOrigin::Signed(bailing.clone()), Renouncing::RunnerUp)
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	// We use the max block weight for this extrinsic for now. See below.
	remove_member_without_replacement {}: {
		Err(BenchmarkError::Override(
			BenchmarkResult::from_weight(T::BlockWeights::get().max_block)
		))?;
	}

	remove_member_with_replacement {
		// easy case. We have a runner up. Nothing will have that much of an impact. m will be
		// number of members and runners. There is always at least one runner.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		let _ = fill_seats_up_to::<T>(m)?;
		let removing = as_lookup::<T>(<Elections<T>>::members_ids()[0].clone());
	}: remove_member(RawOrigin::Root, removing, true, false)
	verify {
		// must still have enough members.
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get());
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	clean_defunct_voters {
		// total number of voters.
		let v in (T::MaxVoters::get() / 2) .. T::MaxVoters::get();
		// those that are defunct and need removal.
		let d in 0 .. (T::MaxVoters::get() / 2);

		// remove any previous stuff.
		clean::<T>();

		let all_candidates = submit_candidates::<T>(T::MaxCandidates::get(), "candidates")?;
		distribute_voters::<T>(all_candidates, v, MAXIMUM_VOTE)?;

		// all candidates leave.
		<Candidates<T>>::kill();

		// now everyone is defunct
		assert!(<Voting<T>>::iter().all(|(_, v)| <Elections<T>>::is_defunct_voter(&v.votes)));
		assert_eq!(<Voting<T>>::iter().count() as u32, v);
		let root = RawOrigin::Root;
	}: _(root, v, d)
	verify {
		assert_eq!(<Voting<T>>::iter().count() as u32, 0);
	}

	election_phragmen {
		// This is just to focus on phragmen in the context of this module. We always select 20
		// members, this is hard-coded in the runtime and cannot be trivially changed at this stage.
		// Yet, change the number of voters, candidates and edge per voter to see the impact. Note
		// that we give all candidates a self vote to make sure they are all considered.
		let c in 1 .. T::MaxCandidates::get();
		let v in 1 .. T::MaxVoters::get();
		let e in (T::MaxVoters::get()) .. T::MaxVoters::get() as u32 * MAXIMUM_VOTE as u32;
		clean::<T>();

		// so we have a situation with v and e. we want e to basically always be in the range of `e
		// -> e * MAXIMUM_VOTE`, but we cannot express that now with the benchmarks. So what we do
		// is: when c is being iterated, v, and e are max and fine. when v is being iterated, e is
		// being set to max and this is a problem. In these cases, we cap e to a lower value, namely
		// v * MAXIMUM_VOTE. when e is being iterated, v is at max, and again fine. all in all,
		// votes_per_voter can never be more than MAXIMUM_VOTE. Note that this might cause `v` to be
		// an overestimate.
		let votes_per_voter = (e / v).min(MAXIMUM_VOTE as u32);

		let all_candidates = submit_candidates_with_self_vote::<T>(c, "candidates")?;
		let _ = distribute_voters::<T>(all_candidates, v.saturating_sub(c), votes_per_voter as usize)?;
	}: {
		<Elections<T>>::on_initialize(T::TermDuration::get());
	}
	verify {
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get().min(c));
		assert_eq!(
			<Elections<T>>::runners_up().len() as u32,
			T::DesiredRunnersUp::get().min(c.saturating_sub(T::DesiredMembers::get())),
		);

		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	#[extra]
	election_phragmen_c_e {
		let c in 1 .. T::MaxCandidates::get();
		let e in (T::MaxVoters::get()) .. T::MaxVoters::get() * MAXIMUM_VOTE as u32;
		let fixed_v = T::MaxVoters::get();
		clean::<T>();

		let votes_per_voter = e / fixed_v;

		let all_candidates = submit_candidates_with_self_vote::<T>(c, "candidates")?;
		let _ = distribute_voters::<T>(
			all_candidates,
			fixed_v - c,
			votes_per_voter as usize,
		)?;
	}: {
		<Elections<T>>::on_initialize(T::TermDuration::get());
	}
	verify {
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get().min(c));
		assert_eq!(
			<Elections<T>>::runners_up().len() as u32,
			T::DesiredRunnersUp::get().min(c.saturating_sub(T::DesiredMembers::get())),
		);

		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	#[extra]
	election_phragmen_v {
		let v in 4 .. 16;
		let fixed_c = T::MaxCandidates::get() / 10;
		let fixed_e = 64;
		clean::<T>();

		let votes_per_voter = fixed_e / v;

		let all_candidates = submit_candidates_with_self_vote::<T>(fixed_c, "candidates")?;
		let _ = distribute_voters::<T>(all_candidates, v, votes_per_voter as usize)?;
	}: {
		<Elections<T>>::on_initialize(T::TermDuration::get());
	}
	verify {
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get().min(fixed_c));
		assert_eq!(
			<Elections<T>>::runners_up().len() as u32,
			T::DesiredRunnersUp::get().min(fixed_c.saturating_sub(T::DesiredMembers::get())),
		);

		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	impl_benchmark_test_suite!(
		Elections,
		crate::tests::ExtBuilder::default().desired_members(13).desired_runners_up(7),
		crate::tests::Test,
		exec_name = build_and_execute,
	);
}
