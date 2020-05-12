// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Elections-Phragmen pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::OnInitialize;

use crate::Module as Elections;

const SEED: u32 = 0;
const BALANCE_FACTOR: u32 = 250;
const MAX_LOCKS: u32 = 20;
const MAX_VOTERS: u32 = 500;
const MAX_CANDIDATES: u32 = 100;

type Lookup<T> = <<T as frame_system::Trait>::Lookup as StaticLookup>::Source;

/// grab new account with infinite balance.
fn endowed_account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let account: T::AccountId = account(name, index, SEED);
	let amount = default_stake::<T>(BALANCE_FACTOR);
	let _ = T::Currency::make_free_balance_be(&account, amount);
	// important to increase the total issuance since T::CurrencyToVote will need it to be sane for
	// phragmen to work.
	T::Currency::issue(amount);
	account
}

/// Account ot lookup type of system trait.
fn as_lookup<T: Trait>(account: T::AccountId) -> Lookup<T> {
	T::Lookup::unlookup(account)
}

/// Get a reasonable amount of stake based on the execution trait's configuration
fn default_stake<T: Trait>(factor: u32) -> BalanceOf<T> {
	let factor = BalanceOf::<T>::from(factor);
	T::Currency::minimum_balance() * factor
}

/// Add `c` new candidates.
fn submit_candidates<T: Trait>(c: u32, prefix: &'static str)
	-> Result<Vec<T::AccountId>, &'static str>
{
	(0..c).map(|i| {
		let account = endowed_account::<T>(prefix, i);
		<Elections<T>>::submit_candidacy(RawOrigin::Signed(account.clone()).into())
			.map_err(|_| "failed to submit candidacy")?;
		Ok(account)
	}).collect::<Result<_, _>>()
}

/// Add `c` new candidates with self vote.
fn submit_candidates_with_self_vote<T: Trait>(c: u32, prefix: &'static str)
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
fn submit_voter<T: Trait>(caller: T::AccountId, votes: Vec<T::AccountId>, stake: BalanceOf<T>)
	-> Result<(), &'static str>
{
	<Elections<T>>::vote(RawOrigin::Signed(caller).into(), votes, stake)
		.map_err(|_| "failed to submit vote")
}

/// add `n` locks to account `who`.
fn add_locks<T: Trait>(who: &T::AccountId, n: u8) {
	for id in 0..n {
		let lock_id = [id; 8];
		let locked = 100;
		let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
		T::Currency::set_lock(lock_id, who, locked.into(), reasons);
	}
}

/// create `num_voter` voters who randomly vote for at most `votes` of `all_candidates` if
/// available.
fn distribute_voters<T: Trait>(mut all_candidates: Vec<T::AccountId>, num_voters: u32, votes: usize)
	-> Result<(), &'static str>
{
	let stake = default_stake::<T>(BALANCE_FACTOR);
	let c = all_candidates.len() as u32;
	for i in 0..num_voters {
		// to ensure that votes are different,
		all_candidates.rotate_left((i % c) as usize);
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
fn fill_seats_up_to<T: Trait>(m: u32) -> Result<Vec<T::AccountId>, &'static str> {
	let candidates = submit_candidates_with_self_vote::<T>(m, "fill_seats_up_to")?;
	assert_eq!(<Elections<T>>::candidates().len() as u32, m, "wrong number of candidates.");
	<Elections<T>>::do_phragmen();
	assert_eq!(<Elections<T>>::candidates().len(), 0, "some candidates remaining.");
	assert_eq!(
		<Elections<T>>::members().len() + <Elections<T>>::runners_up().len(),
		m as usize,
		"wrong number of members and runners-up",
	);
	Ok(candidates)
}

/// removes all the storage items to reverse any genesis state.
fn clean<T: Trait>() {
	<Members<T>>::kill();
	<Candidates<T>>::kill();
	<RunnersUp<T>>::kill();
	let _ = <Voting<T>>::drain();
}

benchmarks! {
	_ {}

	// -- Signed ones
	vote {
		// range of candidates to vote for.
		let v in 1 .. (MAXIMUM_VOTE as u32);
		// range of locks that the caller already had. This extrinsic adds a lock.
		let l in 1 .. MAX_LOCKS;
		clean::<T>();

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(MAXIMUM_VOTE as u32, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		add_locks::<T>(&caller, l as u8);

		let stake = default_stake::<T>(BALANCE_FACTOR);

		// vote first `x` ones.
		let votes = all_candidates.into_iter().take(v as usize).collect();

	}: _(RawOrigin::Signed(caller), votes, stake)

	remove_voter {
		// range of candidates that we have voted for. This may or may have a significant impact on
		// the outcome.
		let v in 1 .. (MAXIMUM_VOTE as u32);
		// range of locks that the caller already had. This extrinsic removes a lock.
		let l in 1 .. MAX_LOCKS;
		clean::<T>();

		let votes_to_remove = (MAXIMUM_VOTE / 2) as u32;

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(v, "candidates")?;

		let caller = endowed_account::<T>("caller", 0);
		add_locks::<T>(&caller, l as u8);

		let stake = default_stake::<T>(BALANCE_FACTOR);
		submit_voter::<T>(caller.clone(), all_candidates, stake)?;

	}: _(RawOrigin::Signed(caller))

	report_defunct_voter_correct {
		// number fo already existing members or runners.
		let m in 1 .. T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		// number of already existing candidates that may or may not be voted by the reported
		// account.
		let c in 1 .. MAX_CANDIDATES;
		// number of candidates that the reported voter voted for. The worse case of search here is
		// basically `c * v`.
		let v in 1 .. (MAXIMUM_VOTE as u32);
		clean::<T>();

		let stake = default_stake::<T>(BALANCE_FACTOR);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create a bunch of candidates as well.
		let bailing_candidates = submit_candidates::<T>(v, "bailing_candidates")?;
		let all_candidates = submit_candidates::<T>(c, "all_candidates")?;

		// account 1 is the reporter and it doesn't matter how many it votes. But it has to be a
		// voter.
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

		let account_2_lookup = as_lookup::<T>(account_2.clone());

		// all the bailers go away.
		bailing_candidates.into_iter().for_each(|b| {
			assert!(<Elections<T>>::renounce_candidacy(RawOrigin::Signed(b).into()).is_ok());
		});
	}: report_defunct_voter(RawOrigin::Signed(account_1.clone()), account_2_lookup)
	verify {
		assert!(<Elections<T>>::is_voter(&account_1));
		assert!(!<Elections<T>>::is_voter(&account_2));
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	report_defunct_voter_incorrect {
		// number fo already existing members or runners.
		let m in 1 .. T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		// number of already existing candidates that may or may not be voted by the reported
		// account.
		let c in 1 .. MAX_CANDIDATES;
		// number of candidates that the reported voter voted for. The worse case of search here is
		// basically `c * v`.
		let v in 2 .. (MAXIMUM_VOTE as u32);

		clean::<T>();
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create a bunch of candidates as well.
		let all_candidates = submit_candidates::<T>(c, "candidates")?;

		// account 1 is the reporter and it doesn't matter how many it votes.
		let account_1 = endowed_account::<T>("caller", 0);
		submit_voter::<T>(
			account_1.clone(),
			all_candidates.iter().take(1).cloned().collect(),
			stake,
		)?;

		// account 2 votes for a bunch of crap, and finally a correct candidate.
		let account_2 = endowed_account::<T>("caller_2", 1);
		let mut invalid: Vec<T::AccountId> =
			(0..(v-1)).map(|seed| account::<T::AccountId>("invalid", 0, seed).clone()).collect();
		invalid.push(all_candidates.last().unwrap().clone());
		submit_voter::<T>(
			account_2.clone(),
			invalid,
			stake,
		)?;

		let account_2_lookup = as_lookup::<T>(account_2.clone());
		// no one bails out. account_1 is slashed and removed as voter now.
	}: report_defunct_voter(RawOrigin::Signed(account_1.clone()), account_2_lookup)
	verify {
		assert!(!<Elections<T>>::is_voter(&account_1));
		assert!(<Elections<T>>::is_voter(&account_2));
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	submit_candidacy {
		// number fo already existing members or runners. Because candidates cannot be duplicate
		// with members and previous candidates.
		let m in 1 .. T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		// number of already existing candidates.
		let c in 1 .. MAX_CANDIDATES;

		clean::<T>();
		let stake = default_stake::<T>(BALANCE_FACTOR);

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;

		// create previous candidates;
		let _ = submit_candidates::<T>(c, "candidates")?;

		// we assume worse case that: extrinsic is successful and candidate is not duplicate.
		let candidate_account = endowed_account::<T>("caller", 0);
	}: _(RawOrigin::Signed(candidate_account.clone()))
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
		// number of already existing members and runners-up.
		let m in 1 .. T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		// number of already existing candidates.
		let c in 1 .. MAX_CANDIDATES;

		clean::<T>();

		// create m members and runners combined.
		let _ = fill_seats_up_to::<T>(m)?;
		let all_candidates = submit_candidates::<T>(c, "caller")?;

		let bailing = all_candidates[0].clone(); // Should be ("caller", 0)
	}: renounce_candidacy(RawOrigin::Signed(bailing.clone()))
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	renounce_candidacy_member_runner_up {
		// removing members and runners will be cheaper most likely. The number of candidates will
		// have no impact.
		// number of already existing candidates.
		let c in 1 .. MAX_CANDIDATES;
		// number of already existing members and runners-up.
		let m in 1 .. T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		// create m members and runners combined.
		let members_and_runners_up = fill_seats_up_to::<T>(m)?;
		let _ = submit_candidates::<T>(c, "candidates")?;

		let bailing = members_and_runners_up[0].clone();
	}: renounce_candidacy(RawOrigin::Signed(bailing.clone()))
	verify {
		#[cfg(test)]
		{
			// reset members in between benchmark tests.
			use crate::tests::MEMBERS;
			MEMBERS.with(|m| *m.borrow_mut() = vec![]);
		}
	}

	// -- Root ones
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

		let to_remove = all_members[0].clone();
	}: remove_member(RawOrigin::Root, as_lookup::<T>(to_remove))
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
		let m in
			(T::DesiredMembers::get() + 1)
			..
			T::DesiredMembers::get() + T::DesiredRunnersUp::get();
		clean::<T>();

		let _ = fill_seats_up_to::<T>(m)?;
	}: remove_member(RawOrigin::Root, as_lookup::<T>(<Elections<T>>::members_ids()[0].clone()))
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
			assert_ok!(test_benchmark_renounce_candidacy_member_runner_up::<Test>());
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
