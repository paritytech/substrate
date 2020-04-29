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

use codec::{Encode, Decode};
use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use frame_benchmarking::benchmarks;
use sp_runtime::traits::Bounded;
use frame_support::assert_ok;

use crate::Module as Elections;

const SEED: u32 = 0;
const DEFAULT_STAKE: u32 = 1000;

type Lookup<T> = <<T as frame_system::Trait>::Lookup as StaticLookup>::Source;

fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let entropy = (name, index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

fn endowed_account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let account = account::<T>(name, index);
	let _ = T::Currency::make_free_balance_be(&account, BalanceOf::<T>::max_value());
	account
}

fn as_lookup<T: Trait>(account: T::AccountId) -> Lookup<T> {
	T::Lookup::unlookup(account)
}

/// Add `c` new candidates.
fn submit_candidates<T: Trait>(c: u32) -> Result<Vec<T::AccountId>, &'static str> {
	(0..c).map(|i| {
		let account = endowed_account::<T>("candidate", i);
		<Elections<T>>::submit_candidacy(RawOrigin::Signed(account.clone()).into())
			.map_err(|_| "failed to submit candidacy")?;
		Ok(account)
	}).collect::<Result<_, _>>()
}

/// Submit one voter.
fn submit_voter<T: Trait>(caller: T::AccountId, votes: Vec<T::AccountId>, stake: BalanceOf<T>)
	-> Result<(), &'static str>
{
		<Elections<T>>::vote(RawOrigin::Signed(caller).into(), votes, stake)
			.map_err(|_| "failed to submit vote")
}

benchmarks! {
	// TODO: is this needed? or is it just nice to be explicit that we don't have common stuff?
	_ {}

	// -- Signed ones
	vote {
		// range of candidates to vote for. Direct argument of the dispatchable.
		let x in 1 .. (MAXIMUM_VOTE as u32);

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(MAXIMUM_VOTE as u32)?;

		let caller = endowed_account::<T>("caller", SEED);
		let stake = BalanceOf::<T>::from(DEFAULT_STAKE);
		// vote first `x` ones.
		let votes = all_candidates.into_iter().take(x as usize).collect();
	}: _(RawOrigin::Signed(caller), votes, stake)

	remove_voter {
		// No complexity parameter. while we can vote for numerous candidates and then remove them
		// (and I think each can have slightly different performance), we cannot express this via
		// the parameters. Hence, we only check for the median, 8 votes to be removed. Only use
		// account seed as complexity parameter.
		// TODO: what should be the upper bound here? the first benchmark runs 16 iterations.. this one 1000?
		let s in 0 .. 1000;

		let votes_to_remove = (MAXIMUM_VOTE / 2) as u32;

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(votes_to_remove)?;

		let caller = endowed_account::<T>("caller", s);
		let stake = BalanceOf::<T>::from(DEFAULT_STAKE);
		submit_voter::<T>(caller.clone(), all_candidates, stake)?;
	}: _(RawOrigin::Signed(caller))

	report_defunct_voter {
		// has no complexity parameter. two voters exist. One only votes fro outdated candidates.
		// The other one can report the defunct one.
		let s in 0 .. 1000;

		// create a bunch of candidates.
		let candidate_count = (MAXIMUM_VOTE) as u32;
		let all_candidates = submit_candidates::<T>(candidate_count)?;

		let stake = BalanceOf::<T>::from(DEFAULT_STAKE);

		// account 1 votes for the first half
		let account_1 = endowed_account::<T>("caller_1", s);
		let bailing = all_candidates.iter().take(candidate_count as usize / 2).cloned().collect::<Vec<_>>();
		submit_voter::<T>(
			account_1.clone(),
			bailing.clone(),
			stake,
		)?;
		let account_1_lookup = as_lookup::<T>(account_1);

		// account 2 votes for the second half
		let account_2 = endowed_account::<T>("caller_2", s);
		submit_voter::<T>(
			account_2.clone(),
			all_candidates.iter().rev().take(candidate_count as usize / 2).cloned().collect(),
			stake,
		)?;

		// all the first chunk of candidates bail out
		bailing.into_iter().for_each(|b| {
			assert_ok!(<Elections<T>>::renounce_candidacy(RawOrigin::Signed(b).into()));
		});
	}: _(RawOrigin::Signed(account_2), account_1_lookup)

	submit_candidacy {
		// No complexity parameter. Use account seed to iterate.
		let s in 0 .. 1000;

		let candidate_account = endowed_account::<T>("candidate", s);
	}: _(RawOrigin::Signed(candidate_account.clone()))


	renounce_candidacy {
		// No complexity parameter. Use account seed to iterate.
		let s in 0 .. 1000;

		let candidate_account = endowed_account::<T>("candidate", s);
		<Elections<T>>::submit_candidacy(RawOrigin::Signed(candidate_account.clone()).into())
			.map_err(|_| "failed to submit candidacy")?;
	}: _(RawOrigin::Signed(candidate_account.clone()))

	// -- Root ones
	remove_member {
		// worse case is when we remove a member and we have no runner as a replacement. This
		// triggers phragmen again.

		// create only enough candidates for members.
		let candidate_count = T::DesiredMembers::get();
		let all_candidates = submit_candidates::<T>(candidate_count)?;
		<Elections<T>>::do_phragmen();

		assert_eq!(<Elections<T>>::members().len() as u32, T::DesiredMembers::get());
		assert_eq!(<Elections<T>>::runners_up().len(), 0);

		let to_remove = all_candidates[0].clone();
	}: _(RawOrigin::Root, as_lookup::<T>(to_remove))
	verify {
		println!("{:?}", <frame_system::Module<T>>::events());
		assert!(false);
	}

	on_initialize {}: {}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks_elections_phragmen() {
		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(test_benchmark_vote::<Test>());
			assert_ok!(test_benchmark_remove_voter::<Test>());
			assert_ok!(test_benchmark_report_defunct_voter::<Test>());
			assert_ok!(test_benchmark_submit_candidacy::<Test>());
			assert_ok!(test_benchmark_renounce_candidacy::<Test>());
			assert_ok!(test_benchmark_remove_member::<Test>());
		});
	}
}

