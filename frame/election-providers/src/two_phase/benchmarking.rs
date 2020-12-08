// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Two phase election pallet benchmarking.

use super::*;
use crate::two_phase::{Module as TwoPhase};

pub use frame_benchmarking::{account, benchmarks, whitelist_account, whitelisted_caller};
use frame_support::assert_ok;
use frame_system::RawOrigin;
use rand::{seq::SliceRandom, thread_rng};
use sp_npos_elections::ExtendedBalance;
use sp_runtime::InnerOf;
use sp_std::convert::TryInto;

const SEED: u32 = 0;

/// Creates a **valid** solution with exactly the given size.
///
/// The snapshot is also created internally.
///
/// The snapshot size must be bigger, otherwise this will panic.
fn solution_with_size<T: Config>(
	witness: WitnessData,
	active_voters_count: u32,
	winners_count: u32,
) -> RawSolution<CompactOf<T>>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
	<InnerOf<CompactAccuracyOf<T>> as sp_std::convert::TryFrom<usize>>::Error: sp_std::fmt::Debug,
{
	assert!(witness.targets >= winners_count, "must have enough targets");
	assert!(
		witness.voters >= active_voters_count,
		"must have enough voters"
	);
	assert!((<CompactOf<T>>::LIMIT as u32) < winners_count, "must have enough winners to give them votes.");

	let stake: u64 = 1000_000;

	// first generates random targets.
	let targets: Vec<T::AccountId> = (0..witness.targets)
		.map(|i| account("Targets", i, SEED))
		.collect();

	let mut rng = thread_rng();

	// decide who are the winners.
	let winners = targets
		.as_slice()
		.choose_multiple(&mut rng, winners_count as usize)
		.cloned()
		.collect::<Vec<_>>();

	// generate first active voters who must vote for a subset of winners.
	let active_voters = (0..active_voters_count)
		.map(|i| {
			// chose a random subset of winners.
			let winner_votes = winners
				.as_slice()
				.choose_multiple(&mut rng, <CompactOf<T>>::LIMIT)
				.cloned()
				.collect::<Vec<_>>();
			let voter = account::<T::AccountId>("Voter", i, SEED);
			(voter, stake, winner_votes)
		})
		.collect::<Vec<_>>();

	// rest of the voters. They can only vote for non-winners.
	let non_winners = targets
		.iter()
		.filter(|t| !winners.contains(t))
		.cloned()
		.collect::<Vec<T::AccountId>>();
	let rest_voters = (active_voters_count..witness.voters)
		.map(|i| {
			let votes = (&non_winners)
				.choose_multiple(&mut rng, <CompactOf<T>>::LIMIT)
				.cloned()
				.collect::<Vec<T::AccountId>>();
			let voter = account::<T::AccountId>("Voter", i, SEED);
			(voter, stake, votes)
		})
		.collect::<Vec<_>>();

	let mut all_voters = active_voters.clone();
	all_voters.extend(rest_voters);
	all_voters.shuffle(&mut rng);

	assert_eq!(active_voters.len() as u32, active_voters_count);
	assert_eq!(all_voters.len() as u32, witness.voters);
	assert_eq!(winners.len() as u32, winners_count);

	<Snapshot<T>>::put(RoundSnapshot {
		desired_targets: winners_count,
		voters: all_voters.clone(),
		targets: targets.clone(),
	});

	let stake_of = crate::stake_of_fn!(all_voters, T::AccountId);
	let voter_index = crate::voter_index_fn!(all_voters, T::AccountId, T);
	let voter_at = crate::voter_at_fn!(all_voters, T::AccountId, T);
	let target_at = crate::target_at_fn!(targets, T::AccountId, T);
	let target_index = crate::target_index_fn!(targets, T::AccountId, T);

	let assignments = active_voters
		.iter()
		.map(|(voter, _stake, votes)| {
			let percent_per_edge: InnerOf<CompactAccuracyOf<T>> =
				(100 / votes.len()).try_into().unwrap();
			Assignment {
				who: voter.clone(),
				distribution: votes
					.iter()
					.map(|t| (t.clone(), <CompactAccuracyOf<T>>::from_percent(percent_per_edge)))
					.collect::<Vec<_>>(),
			}
		})
		.collect::<Vec<_>>();

	let compact =
		<CompactOf<T>>::from_assignment(assignments, &voter_index, &target_index).unwrap();
	let score = compact
		.clone()
		.score(&winners, stake_of, voter_at, target_at)
		.unwrap();
	let round = <TwoPhase<T>>::round();
	RawSolution { compact, score, round }
}

benchmarks! {
	where_clause {
		where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		<InnerOf<CompactAccuracyOf<T>> as sp_std::convert::TryFrom<usize>>::Error: sp_std::fmt::Debug,
	}
	_{}

	submit {
		// number of votes in snapshot.
		let v in 2000 .. 3000;
		// number of targets in snapshot.
		let t in 500 .. 800;
		// number of assignments, i.e. compact.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in 500 .. 1500;
		// number of desired targets. Must be a subset of `t` component.
		let d in 200 .. 400;

		let witness = WitnessData { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d);

		assert!(<TwoPhase<T>>::signed_submissions().len() == 0);
		<CurrentPhase<T>>::put(Phase::Signed);

		let caller = frame_benchmarking::whitelisted_caller();
		T::Currency::make_free_balance_be(&caller,  T::Currency::minimum_balance() * 10u32.into());

	}: _(RawOrigin::Signed(caller), raw_solution)
	verify {
		assert!(<TwoPhase<T>>::signed_submissions().len() == 1);
	}

	submit_unsigned {
		// number of votes in snapshot.
		let v in 2000 .. 3000;
		// number of targets in snapshot.
		let t in 500 .. 800;
		// number of assignments, i.e. compact.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in 500 .. 1500;
		// number of desired targets. Must be a subset of `t` component.
		let d in 200 .. 400;

		let witness = WitnessData { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d);

		assert!(<TwoPhase<T>>::queued_solution().is_none());
		<CurrentPhase<T>>::put(Phase::Unsigned((true, 1u32.into())));
	}: _(RawOrigin::None, raw_solution, witness)
	verify {
		assert!(<TwoPhase<T>>::queued_solution().is_some());
	}

	open_signed_phase {}: {} verify {}
	close_signed_phase {}: {} verify {}

	// This is checking a valid solution. The worse case is indeed a valid solution.
	feasibility_check {
		// number of voters in snapshot.
		let v in 200 .. 300;
		// number of targets in snapshot.
		let t in 80 .. 140;
		// number of assignments, i.e. compact.voters_count(). This means the active nominators,
		// thus must be a subset of `v` component.
		let a in 80 .. 140;
		// number of desired targets. Must be a subset of `t` component.
		let d in 30 .. 60;

		let witness = WitnessData { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d);

		assert_eq!(raw_solution.compact.voters_count() as u32, a);
		assert_eq!(raw_solution.compact.unique_targets().len() as u32, d);
	}: {
		assert_ok!(<TwoPhase<T>>::feasibility_check(raw_solution, ElectionCompute::Unsigned));
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::two_phase::mock::*;

	#[test]
	fn test_benchmarks() {
		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(test_benchmark_feasibility_check::<Runtime>());
		});

		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(test_benchmark_submit_unsigned::<Runtime>());
		});

		ExtBuilder::default().build_and_execute(|| {
			assert_ok!(test_benchmark_submit::<Runtime>());
		});
	}
}
