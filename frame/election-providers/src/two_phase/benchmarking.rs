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
use sp_runtime::{InnerOf, PerU16};

const SEED: u32 = 0;

// TODO: the entire snapshot can probably live in a single place.. we most often Read and write it
// at the same time.

/// Generate mock on-chain snapshots.
///
/// This emulates the start of signed phase, where snapshots are received from an upstream crate.
fn mock_snapshot<T: Trait>(
	witness: WitnessData,
) -> (
	Vec<T::AccountId>,
	Vec<(T::AccountId, VoteWeight, Vec<T::AccountId>)>,
)
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	// first generates random targets.
	let targets: Vec<T::AccountId> = (0..witness.targets)
		.map(|i| account("Targets", i, SEED))
		.collect();

	// generate targets, each voting for a random subset of the targets.\
	let mut voters = (0..(witness.voters - witness.targets))
		.map(|i| {
			let mut rng = thread_rng();
			let stake = 1000_000u64;
			let to_vote = rand::random::<usize>() % <CompactOf<T>>::LIMIT + 1;
			let votes = targets.as_slice().choose_multiple(&mut rng, to_vote).cloned().collect::<Vec<_>>();
			let voter = account::<T::AccountId>("Voter", i, SEED);

			(voter, stake, votes)
		})
		.collect::<Vec<_>>();

	// targets should have self vote. This is very helpful, because it ensure that by doing the trim,
	// we almost never reduce the number of unique targets. For this cause, we also make the self
	// vote heavier, to ensure that trimming only removes a voter here and there, not a target.
	voters.extend(targets.iter().map(|t| (t.clone(), 1000_000_0u64, vec![t.clone()])));

	(targets, voters)
}

fn put_mock_snapshot<T: Trait>(witness: WitnessData, desired_targets: u32)
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	let (targets, voters) = mock_snapshot::<T>(witness);
	<SnapshotTargets<T>>::put(targets);
	<SnapshotVoters<T>>::put(voters);
	DesiredTargets::put(desired_targets);
}

/// Creates a **valid** solution with exactly the given size.
///
/// The snapshot size must be bigger, otherwise this will panic.
fn solution_with_size<T: Trait>(active_voters: u32, winners_count: u32) -> RawSolution<CompactOf<T>>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	let voters = <TwoPhase<T>>::snapshot_voters().unwrap();
	let targets = <TwoPhase<T>>::snapshot_targets().unwrap();

	// else we cannot support this, self vote is a must.
	assert!(active_voters >= winners_count);
	// else we won't have enough voters.
	assert!(voters.len() >= active_voters as usize);
	// else we won't have enough winners
	assert!(targets.len() >= winners_count as usize);

	let voter_index = crate::voter_index_fn!(voters, T::AccountId, T);
	let voter_at = crate::voter_at_fn!(voters, T::AccountId, T);
	let target_at = crate::target_at_fn!(targets, T::AccountId, T);
	let stake_of = crate::stake_of_fn!(voters, T::AccountId);

	// First chose random winners.
	let mut rng = rand::thread_rng();
	let winners = targets
		.as_slice()
		.choose_multiple(&mut rng, winners_count as usize)
		.cloned()
		.collect::<Vec<_>>();

	let mut assignments = winners
		.iter()
		.map(|w| Assignment {
			who: *w,
			distribution: vec![(w, PerU16::one())],
		})
		.collect::<Vec<_>>();

	// all external voters who are not self vote.
	let mut voters_pool = voters
		.iter()
		.filter(|(x, _, z)| *x != z[0])
		.cloned()
		.collect::<Vec<_>>();
	while assignments.len() < active_voters as usize {
		// pop one of the voters.
		let (who, _, votes) = voters_pool.remove(rand::random::<usize>() % voters_pool.len());
		// see if it votes for any of the winners.
		let winner_intersection = votes
			.iter()
			.filter(|v| winners.contains(v))
			.cloned()
			.collect::<Vec<_>>();
		// if any, add assignment to all of them.
		if winner_intersection.len() > 0 {
			assignments.push(Assignment {
				who,
				distribution: winner_intersection
					.into_iter()
					.map(|w| {
						(
							w,
							PerU16::from_percent((100 / winner_intersection.len()) as u16),
						)
					})
					.collect::<Vec<_>>(),
			})
		}
	}

	let compact = <CompactOf<T>>::from_assignment(assignments, &voter_index, &target_index);

	unimplemented!()
}

benchmarks! {
	where_clause { where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>, }
	_{}
	submit_signed {}: {} verify {}
	submit_unsigned {}: {} verify {}
	open_signed_phase {}: {} verify {}
	close_signed_phase {}: {} verify {}

	// This is checking a valid solution. The worse case is indeed a valid solution.
	feasibility_check {
		// number of votes in snapshot.
		let v in 200 .. 300;
		// number of targets in snapshot.
		let t in 50 .. 80;
		// number of assignments, i.e. compact.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in 20 .. 80;
		// number of desired targets. Must be a subset of `t` component.
		let d in 20 .. 40;

		println!("running v  {}, t {}, a {}, d {}", v, t, a, d);

		let witness = WitnessData { voters: v, targets: t };
		put_mock_snapshot::<T>(witness, d);

		let voters = <TwoPhase<T>>::snapshot_voters().unwrap();
		let targets = <TwoPhase<T>>::snapshot_targets().unwrap();

		let voter_index = crate::voter_index_fn!(voters, T::AccountId, T);
		let voter_at = crate::voter_at_fn!(voters, T::AccountId, T);
		let target_at = crate::target_at_fn!(targets, T::AccountId, T);
		let stake_of = crate::stake_of_fn!(voters, T::AccountId);

		// the score at this point is not usable -- It might change when we resize the compact.
		let RawSolution { compact, score: _ } = <TwoPhase<T>>::mine_solution(0).unwrap();
		let compact = <TwoPhase<T>>::trim_compact(a, compact, voter_index).unwrap();

		assert_eq!(compact.len() as u32, a);
		assert_eq!(compact.unique_targets().len() as u32, d);

		// re-calc score.
		let winners = compact.unique_targets().iter().map(|i| target_at(*i).unwrap()).collect::<Vec<_>>();
		let score = compact
			.clone()
			.score(&winners, stake_of, voter_at, target_at).unwrap();
		let raw_solution = RawSolution { compact, score };
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
