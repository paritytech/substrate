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

//! Elections-Phragmen pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::OnInitialize;

use crate::Module as Elections;

const BALANCE_FACTOR: u32 = 250;
const MAX_VOTERS: u32 = 500;
const MAX_CANDIDATES: u32 = 200;

type Lookup<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

macro_rules! whitelist {
	($acc:ident) => {
		frame_benchmarking::benchmarking::add_to_whitelist(
			frame_system::Account::<T>::hashed_key_for(&$acc).into()
		);
	};
}

/// grab new account with infinite balance.
fn endowed_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let account: T::AccountId = account(name, index, 0);
	let amount = default_stake::<T>(BALANCE_FACTOR);
	let _ = T::Currency::make_free_balance_be(&account, amount);
	// important to increase the total issuance since T::CurrencyToVote will need it to be sane for
	// phragmen to work.
	T::Currency::issue(amount);

	account
}

/// Account to lookup type of system trait.
fn as_lookup<T: Config>(account: T::AccountId) -> Lookup<T> {
	T::Lookup::unlookup(account)
}

/// Get a reasonable amount of stake based on the execution trait's configuration
fn default_stake<T: Config>(factor: u32) -> BalanceOf<T> {
	let factor = BalanceOf::<T>::from(factor);
	T::Currency::minimum_balance() * factor
}

/// Get the current number of candidates.
fn candidate_count<T: Config>() -> u32 {
	<Candidates<T>>::decode_len().unwrap_or(0usize) as u32
}

/// Get the number of votes of a voter.
fn vote_count_of<T: Config>(who: &T::AccountId) -> u32 {
	<Voting<T>>::get(who).1.len() as u32
}

/// A `DefunctVoter` struct with correct value
fn defunct_for<T: Config>(who: T::AccountId) -> DefunctVoter<Lookup<T>> {
	DefunctVoter {
		who: as_lookup::<T>(who.clone()),
		candidate_count: candidate_count::<T>(),
		vote_count: vote_count_of::<T>(&who),
	}
}

/// Add `c` new candidates.
fn submit_candidates<T: Config>(c: u32, prefix: &'static str)
	-> Result<Vec<T::AccountId>, &'static str>
{
	(0..c).map(|i| {
		let account = endowed_account::<T>(prefix, i);
		<Elections<T>>::submit_candidacy(
			RawOrigin::Signed(account.clone()).into(),
			candidate_count::<T>(),
		).map_err(|_| "failed to submit candidacy")?;
		Ok(account)
	}).collect::<Result<_, _>>()
}

/// Add `c` new candidates with self vote.
fn submit_candidates_with_self_vote<T: Config>(c: u32, prefix: &'static str)
	-> Result<Vec<T::AccountId>, &'static str>
{
	let candidates = submit_candidates::<T>(c, prefix)?;
	let stake = default_stake::<T>(BALANCE_FACTOR);
	let _ = candidates.iter().map(|c|
		submit_voter::<T>(c.clone(), vec![c.clone()], stake)
	).collect::<Result<_, _>>()?;
	Ok(candidates)
}


/// Submit one voter.
fn submit_voter<T: Config>(caller: T::AccountId, votes: Vec<T::AccountId>, stake: BalanceOf<T>)
	-> Result<(), sp_runtime::DispatchError>
{
	<Elections<T>>::vote(RawOrigin::Signed(caller).into(), votes, stake)
}

/// create `num_voter` voters who randomly vote for at most `votes` of `all_candidates` if
/// available.
fn distribute_voters<T: Config>(mut all_candidates: Vec<T::AccountId>, num_voters: u32, votes: usize)
	-> Result<(), &'static str>
{
	let stake = default_stake::<T>(BALANCE_FACTOR);
	for i in 0..num_voters {
		// to ensure that votes are different
		all_candidates.rotate_left(1);
		let votes = all_candidates
			.iter()
			.cloned()
			.take(votes)
			.collect::<Vec<_>>();
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
	Ok(
		<Elections<T>>::members()
			.into_iter()
			.map(|(x, _)| x)
			.chain(<Elections<T>>::runners_up().into_iter().map(|(x, _)| x))
			.collect()
	)
}

/// removes all the storage items to reverse any genesis state.
fn clean<T: Config>() {
	<Members<T>>::kill();
	<Candidates<T>>::kill();
	<RunnersUp<T>>::kill();
	let _ = <Voting<T>>::drain();
}

benchmarks! {
	// -- Signed ones
	vote {
		let v in 1 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// vote for all of them.
		let votes = all_candidates;

		whitelist!(caller);
	}: _(RawOrigin::Signed(caller), votes, stake)

	vote_update {
		let v in 1 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// original votes.
		let mut votes = all_candidates;
		submit_voter::<T>(caller.clone(), votes.clone(), stake)?;

		// new votes.
		votes.rotate_left(1);

		whitelist!(caller);
	}: vote(RawOrigin::Signed(caller), votes, stake)

	remove_voter {
		// we fix the number of voted candidates to max
		let v = MAXIMUM_VOTE as u32;
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);

		let stake = default_stake::<T>(BALANCE_FACTOR);
		submit_voter::<T>(caller.clone(), all_candidates, stake)?;

		whitelist!(caller);
	}: _(RawOrigin::Signed(caller))

	report_defunct_voter_correct {
		// number of already existing candidates that may or may not be voted by the reported
		// account.
		let c in 1 .. MAX_CANDIDATES;
		// number of candidates that the reported voter voted for. The worse case of search here is
		// basically `c * v`.
		let v in 1 .. (MAXIMUM_VOTE as u32);
		// we fix the number of members to the number of desired members and runners-up. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();

		clean::<T>();
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create a bunch of candidates as well.
		let bailing_candidates = submit_candidates::<T>(v, "bailing_candidates")?;
		let all_candidates = submit_candidates::<T>(c, "all_candidates")?;

		// account 1 is the reporter and must be whitelisted, and a voter.
		let account_1 = endowed_account::<T>("caller", 0);
		submit_voter::<T>(
			account_1.clone(),
			all_candidates.iter().take(1).cloned().collect(),
			stake,
		)?;

		// account 2 votes for all of the mentioned candidates.
		let account_2 = endowed_account::<T>("caller_2", 1);
		submit_voter::<T>(
			account_2.clone(),
			bailing_candidates.clone(),
			stake,
		)?;

		// all the bailers go away. NOTE: we can simplify this. There's no need to create all these
		// candidates and remove them. The defunct voter can just vote for random accounts as long
		// as there are enough members (potential candidates).
		bailing_candidates.into_iter().for_each(|b| {
			let count = candidate_count::<T>();
			assert!(<Elections<T>>::renounce_candidacy(
				RawOrigin::Signed(b).into(),
				Renouncing::Candidate(count),
			).is_ok());
		});

		let defunct_info = defunct_for::<T>(account_2.clone());
		whitelist!(account_1);

		assert!(<Elections<T>>::is_voter(&account_2));
	}: report_defunct_voter(RawOrigin::Signed(account_1.clone()), defunct_info)
	verify {
		assert!(!<Elections<T>>::is_voter(&account_2));
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	report_defunct_voter_incorrect {
		// number of already existing candidates that may or may not be voted by the reported
		// account.
		let c in 1 .. MAX_CANDIDATES;
		// number of candidates that the reported voter voted for. The worse case of search here is
		// basically `c * v`.
		let v in 1 .. (MAXIMUM_VOTE as u32);
		// we fix the number of members to the number of desired members and runners-up. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();

		clean::<T>();
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create a bunch of candidates as well.
		let all_candidates = submit_candidates::<T>(c, "candidates")?;

		// account 1 is the reporter and need to be whitelisted, and a voter.
		let account_1 = endowed_account::<T>("caller", 0);
		submit_voter::<T>(
			account_1.clone(),
			all_candidates.iter().take(1).cloned().collect(),
			stake,
		)?;

		// account 2 votes for a bunch of crap, and finally a correct candidate.
		let account_2 = endowed_account::<T>("caller_2", 1);
		let mut invalid: Vec<T::AccountId> = (0..(v-1))
			.map(|seed| account::<T::AccountId>("invalid", 0, seed).clone())
			.collect();
		invalid.push(all_candidates.last().unwrap().clone());
		submit_voter::<T>(
			account_2.clone(),
			invalid,
			stake,
		)?;

		let defunct_info = defunct_for::<T>(account_2.clone());
		whitelist!(account_1);
	}: report_defunct_voter(RawOrigin::Signed(account_1.clone()), defunct_info)
	verify {
		// account 2 is still a voter.
		assert!(<Elections<T>>::is_voter(&account_2));
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	submit_candidacy {
		// number of already existing candidates.
		let c in 1 .. MAX_CANDIDATES;
		// we fix the number of members to the number of desired members and runners-up. We'll be in
		// this state almost always.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();

		clean::<T>();
		let stake = default_stake::<T>(BALANCE_FACTOR);

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
		let c in 1 .. MAX_CANDIDATES;
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

	// -- Root ones
	#[extra] // this calls into phragmen and consumes a full block for now.
	remove_member_without_replacement {
		// worse case is when we remove a member and we have no runner as a replacement. This
		// triggers phragmen again. The only parameter is how many candidates will compete for the
		// new slot.
		let c in 1 .. MAX_CANDIDATES;
		clean::<T>();

		// fill only desired members. no runners-up.
		let all_members = fill_seats_up_to::<T>(T::DesiredMembers::get())?;
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get());

		// submit a new one to compensate, with self-vote.
		let replacements = submit_candidates_with_self_vote::<T>(c, "new_candidate")?;

		// create some voters for these replacements.
		distribute_voters::<T>(replacements, MAX_VOTERS, MAXIMUM_VOTE)?;

		let to_remove = as_lookup::<T>(all_members[0].clone());
	}: remove_member(RawOrigin::Root, to_remove, false)
	verify {
		// must still have the desired number of members members.
		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get());
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	remove_member_with_replacement {
		// easy case. We have a runner up. Nothing will have that much of an impact. m will be
		// number of members and runners. There is always at least one runner.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		let _ = fill_seats_up_to::<T>(m)?;
		let removing = as_lookup::<T>(<Elections<T>>::members_ids()[0].clone());
	}: remove_member(RawOrigin::Root, removing, true)
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

	remove_member_wrong_refund {
		// The root call by mistake indicated that this will have no replacement, while it has!
		// this has now consumed a lot of weight and need to refund.
		let m = T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		let _ = fill_seats_up_to::<T>(m)?;
		let removing = as_lookup::<T>(<Elections<T>>::members_ids()[0].clone());
	}: {
		assert_eq!(
			<Elections<T>>::remove_member(RawOrigin::Root.into(), removing, false).unwrap_err().error,
			Error::<T>::InvalidReplacement.into(),
		);
	}
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

	#[extra]
	on_initialize {
		// if n % TermDuration is zero, then we run phragmen. The weight function must and should
		// check this as it is cheap to do so. TermDuration is not a storage item, it is a constant
		// encoded in the runtime.
		let c in 1 .. MAX_CANDIDATES;
		clean::<T>();

		// create c candidates.
		let all_candidates = submit_candidates_with_self_vote::<T>(c, "candidates")?;
		// create 500 voters, each voting the maximum 16
		distribute_voters::<T>(all_candidates, MAX_VOTERS, MAXIMUM_VOTE)?;
	}: {
		// elect
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
	phragmen {
		// This is just to focus on phragmen in the context of this module. We always select 20
		// members, this is hard-coded in the runtime and cannot be trivially changed at this stage.
		// Yet, change the number of voters, candidates and edge per voter to see the impact. Note
		// that we give all candidates a self vote to make sure they are all considered.
		let c in 1 .. MAX_CANDIDATES;
		let v in 1 .. MAX_VOTERS;
		let e in 1 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		let all_candidates = submit_candidates_with_self_vote::<T>(c, "candidates")?;
		let _ = distribute_voters::<T>(all_candidates, v, e as usize)?;
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
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks_elections_phragmen() {
		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_vote::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_remove_voter::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_report_defunct_voter_correct::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_report_defunct_voter_incorrect::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_submit_candidacy::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_renounce_candidacy_candidate::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_renounce_candidacy_runners_up::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_renounce_candidacy_members::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_remove_member_without_replacement::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_remove_member_with_replacement::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_on_initialize::<Test>());
		});

		ExtBuilder::default().desired_members(13).desired_runners_up(7).build_and_execute(|| {
			assert_ok!(test_benchmark_phragmen::<Test>());
		});
	}
}
