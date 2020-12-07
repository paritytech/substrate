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
use crate::two_phase::{Module as TwoPhase, *};

pub use frame_benchmarking::{account, benchmarks, whitelist_account, whitelisted_caller};
use frame_support::assert_ok;
use rand::{seq::SliceRandom, thread_rng};
use sp_npos_elections::{ExtendedBalance, VoteWeight};
use sp_runtime::InnerOf;
use std::convert::TryInto;

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
	<InnerOf<CompactAccuracyOf<T>> as std::convert::TryFrom<usize>>::Error: std::fmt::Debug,
{
	assert!(witness.targets >= winners_count, "must have enough targets");
	assert!(
		witness.voters >= active_voters_count,
		"must have enough voters"
	);

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
	// TODO: this could lead to an underestimate, the active voters should only vote for winners to
	// maximize all the iterations.
	let active_voters = (0..active_voters_count)
		.map(|i| {
			// chose a random number of votes to give to the winners, and whatever is left is given
			// to everyone.
			let votes_to_winners = rand::random::<usize>() % <CompactOf<T>>::LIMIT + 1;
			let votes_to_everyone = <CompactOf<T>>::LIMIT - votes_to_winners;

			let winner_votes = winners
				.as_slice()
				.choose_multiple(&mut rng, votes_to_winners)
				.cloned();
			let rest_votes = targets
				.as_slice()
				.choose_multiple(&mut rng, votes_to_everyone as usize)
				.cloned();

			let votes = winner_votes.chain(rest_votes).collect::<Vec<_>>();
			let voter = account::<T::AccountId>("Voter", i, SEED);
			(voter, stake, votes)
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

	dbg!(active_voters.len(), rest_voters.len(), winners.len());
	// active_voters.extend(rest_voters);
	let mut all_voters = active_voters.clone();
	all_voters.extend(rest_voters);

	assert_eq!(active_voters.len() as u32, active_voters_count);
	assert_eq!(all_voters.len() as u32, witness.voters);
	assert_eq!(winners.len() as u32, winners_count);

	let voters = active_voters;

	<Snapshot<T>>::put(RoundSnapshot {
		desired_targets: winners_count,
		voters: all_voters,
		targets: targets.clone(),
	});

	let voter_index = crate::voter_index_fn!(voters, T::AccountId, T);
	let voter_at = crate::voter_at_fn!(voters, T::AccountId, T);
	let target_at = crate::target_at_fn!(targets, T::AccountId, T);
	let target_index = crate::target_index_fn!(targets, T::AccountId, T);
	let stake_of = crate::stake_of_fn!(voters, T::AccountId);

	let assignments = voters
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

	RawSolution { compact, score }
}

benchmarks! {
	where_clause {
		where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
		// TODO: do I really need this?
		<InnerOf<CompactAccuracyOf<T>> as std::convert::TryFrom<usize>>::Error: std::fmt::Debug,
	}
	_{}

	submit_signed {}: {} verify {}
	submit_unsigned {}: {} verify {}
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

		println!("running v {}, t {}, a {}, d {}", v, t, a, d);

		let witness = WitnessData { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d);

		assert_eq!(raw_solution.compact.voters_count() as u32, a);
		assert_eq!(raw_solution.compact.unique_targets().len() as u32, d);

		let compute = ElectionCompute::Unsigned;
	}: {
		assert_ok!(<TwoPhase<T>>::feasibility_check(raw_solution, compute));
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
		})
	}
}
