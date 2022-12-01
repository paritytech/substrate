// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
use crate::{unsigned::IndexAssignmentOf, Pallet as MultiPhase};
use frame_benchmarking::account;
use frame_support::{assert_ok, traits::Hooks};
use frame_system::RawOrigin;
use rand::{prelude::SliceRandom, rngs::SmallRng, SeedableRng};
use sp_arithmetic::{per_things::Percent, traits::One};
use sp_npos_elections::IndexAssignment;
use sp_runtime::InnerOf;

const SEED: u32 = 999;

/// Creates a **valid** solution with exactly the given size.
///
/// The snapshot is also created internally.
fn solution_with_size<T: Config>(
	size: SolutionOrSnapshotSize,
	active_voters_count: u32,
	desired_targets: u32,
) -> Result<RawSolution<SolutionOf<T>>, &'static str> {
	ensure!(size.targets >= desired_targets, "must have enough targets");
	ensure!(
		size.targets >= (<SolutionOf<T>>::LIMIT * 2) as u32,
		"must have enough targets for unique votes."
	);
	ensure!(size.voters >= active_voters_count, "must have enough voters");
	ensure!(
		(<SolutionOf<T>>::LIMIT as u32) < desired_targets,
		"must have enough winners to give them votes."
	);

	let ed: VoteWeight = T::Currency::minimum_balance().saturated_into::<u64>();
	let stake: VoteWeight = ed.max(One::one()).saturating_mul(100);

	// first generates random targets.
	let targets: Vec<T::AccountId> = (0..size.targets)
		.map(|i| frame_benchmarking::account("Targets", i, SEED))
		.collect();

	let mut rng = SmallRng::seed_from_u64(SEED.into());

	// decide who are the winners.
	let winners = targets
		.as_slice()
		.choose_multiple(&mut rng, desired_targets as usize)
		.cloned()
		.collect::<Vec<_>>();

	// first generate active voters who must vote for a subset of winners.
	let active_voters = (0..active_voters_count)
		.map(|i| {
			// chose a random subset of winners.
			let winner_votes = winners
				.as_slice()
				.choose_multiple(&mut rng, <SolutionOf<T>>::LIMIT)
				.cloned()
				.collect::<Vec<_>>();
			let voter = frame_benchmarking::account::<T::AccountId>("Voter", i, SEED);
			(voter, stake, winner_votes)
		})
		.collect::<Vec<_>>();

	// rest of the voters. They can only vote for non-winners.
	let non_winners = targets
		.iter()
		.filter(|t| !winners.contains(t))
		.cloned()
		.collect::<Vec<T::AccountId>>();
	let rest_voters = (active_voters_count..size.voters)
		.map(|i| {
			let votes = (&non_winners)
				.choose_multiple(&mut rng, <SolutionOf<T>>::LIMIT)
				.cloned()
				.collect::<Vec<T::AccountId>>();
			let voter = frame_benchmarking::account::<T::AccountId>("Voter", i, SEED);
			(voter, stake, votes)
		})
		.collect::<Vec<_>>();

	let mut all_voters = active_voters.clone();
	all_voters.extend(rest_voters);
	all_voters.shuffle(&mut rng);

	assert_eq!(active_voters.len() as u32, active_voters_count);
	assert_eq!(all_voters.len() as u32, size.voters);
	assert_eq!(winners.len() as u32, desired_targets);

	<SnapshotMetadata<T>>::put(SolutionOrSnapshotSize {
		voters: all_voters.len() as u32,
		targets: targets.len() as u32,
	});
	<DesiredTargets<T>>::put(desired_targets);
	<Snapshot<T>>::put(RoundSnapshot { voters: all_voters.clone(), targets: targets.clone() });

	// write the snapshot to staking or whoever is the data provider, in case it is needed further
	// down the road.
	T::DataProvider::put_snapshot(all_voters.clone(), targets.clone(), Some(stake));

	let cache = helpers::generate_voter_cache::<T>(&all_voters);
	let stake_of = helpers::stake_of_fn::<T>(&all_voters, &cache);
	let voter_index = helpers::voter_index_fn::<T>(&cache);
	let target_index = helpers::target_index_fn::<T>(&targets);
	let voter_at = helpers::voter_at_fn::<T>(&all_voters);
	let target_at = helpers::target_at_fn::<T>(&targets);

	let assignments = active_voters
		.iter()
		.map(|(voter, _stake, votes)| {
			let percent_per_edge: InnerOf<SolutionAccuracyOf<T>> =
				(100 / votes.len()).try_into().unwrap_or_else(|_| panic!("failed to convert"));
			crate::unsigned::Assignment::<T> {
				who: voter.clone(),
				distribution: votes
					.iter()
					.map(|t| (t.clone(), <SolutionAccuracyOf<T>>::from_percent(percent_per_edge)))
					.collect::<Vec<_>>(),
			}
		})
		.collect::<Vec<_>>();

	let solution =
		<SolutionOf<T>>::from_assignment(&assignments, &voter_index, &target_index).unwrap();
	let score = solution.clone().score(stake_of, voter_at, target_at).unwrap();
	let round = <MultiPhase<T>>::round();

	assert!(score[0] > 0, "score is zero, this probably means that the stakes are not set.");
	Ok(RawSolution { solution, score, round })
}

fn set_up_data_provider<T: Config>(v: u32, t: u32) {
	T::DataProvider::clear();
	log!(
		info,
		"setting up with voters = {} [degree = {}], targets = {}",
		v,
		T::DataProvider::MAXIMUM_VOTES_PER_VOTER,
		t
	);

	// fill targets.
	let mut targets = (0..t)
		.map(|i| {
			let target = frame_benchmarking::account::<T::AccountId>("Target", i, SEED);
			T::DataProvider::add_target(target.clone());
			target
		})
		.collect::<Vec<_>>();
	// we should always have enough voters to fill.
	assert!(targets.len() > T::DataProvider::MAXIMUM_VOTES_PER_VOTER as usize);
	targets.truncate(T::DataProvider::MAXIMUM_VOTES_PER_VOTER as usize);

	// fill voters.
	(0..v).for_each(|i| {
		let voter = frame_benchmarking::account::<T::AccountId>("Voter", i, SEED);
		let weight = T::Currency::minimum_balance().saturated_into::<u64>() * 1000;
		T::DataProvider::add_voter(voter, weight, targets.clone());
	});
}

frame_benchmarking::benchmarks! {
	on_initialize_nothing {
		assert!(<MultiPhase<T>>::current_phase().is_off());
	}: {
		<MultiPhase<T>>::on_initialize(1u32.into());
	} verify {
		assert!(<MultiPhase<T>>::current_phase().is_off());
	}

	on_initialize_open_signed {
		assert!(<MultiPhase<T>>::snapshot().is_none());
		assert!(<MultiPhase<T>>::current_phase().is_off());
	}: {
		<MultiPhase<T>>::on_initialize_open_signed();
	} verify {
		assert!(<MultiPhase<T>>::snapshot().is_none());
		assert!(<MultiPhase<T>>::current_phase().is_signed());
	}

	on_initialize_open_unsigned {
		assert!(<MultiPhase<T>>::snapshot().is_none());
		assert!(<MultiPhase<T>>::current_phase().is_off());
	}: {
		<MultiPhase<T>>::on_initialize_open_unsigned(true, 1u32.into())
	} verify {
		assert!(<MultiPhase<T>>::snapshot().is_none());
		assert!(<MultiPhase<T>>::current_phase().is_unsigned());
	}

	finalize_signed_phase_accept_solution {
		let receiver = account("receiver", 0, SEED);
		let initial_balance = T::Currency::minimum_balance() * 10u32.into();
		T::Currency::make_free_balance_be(&receiver, initial_balance);
		let ready = ReadySolution {
			supports: vec![],
			score: Default::default(),
			compute: Default::default()
		};
		let deposit: BalanceOf<T> = 10u32.into();
		let reward: BalanceOf<T> = 20u32.into();

		assert_ok!(T::Currency::reserve(&receiver, deposit));
		assert_eq!(T::Currency::free_balance(&receiver), initial_balance - 10u32.into());
	}: {
		<MultiPhase<T>>::finalize_signed_phase_accept_solution(ready, &receiver, deposit, reward)
	} verify {
		assert_eq!(T::Currency::free_balance(&receiver), initial_balance + 20u32.into());
		assert_eq!(T::Currency::reserved_balance(&receiver), 0u32.into());
	}

	finalize_signed_phase_reject_solution {
		let receiver = account("receiver", 0, SEED);
		let initial_balance = T::Currency::minimum_balance().max(One::one()) * 10u32.into();
		let deposit: BalanceOf<T> = 10u32.into();
		T::Currency::make_free_balance_be(&receiver, initial_balance);
		assert_ok!(T::Currency::reserve(&receiver, deposit));

		assert_eq!(T::Currency::free_balance(&receiver), initial_balance - 10u32.into());
		assert_eq!(T::Currency::reserved_balance(&receiver), 10u32.into());
	}: {
		<MultiPhase<T>>::finalize_signed_phase_reject_solution(&receiver, deposit)
	} verify {
		assert_eq!(T::Currency::free_balance(&receiver), initial_balance - 10u32.into());
		assert_eq!(T::Currency::reserved_balance(&receiver), 0u32.into());
	}

	create_snapshot_internal {
		// number of votes in snapshot.
		let v in (T::BenchmarkingConfig::VOTERS[0]) .. T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot.
		let t in (T::BenchmarkingConfig::TARGETS[0]) .. T::BenchmarkingConfig::TARGETS[1];

		// we don't directly need the data-provider to be populated, but it is just easy to use it.
		set_up_data_provider::<T>(v, t);
		let targets = T::DataProvider::targets(None)?;
		let voters = T::DataProvider::voters(None)?;
		let desired_targets = T::DataProvider::desired_targets()?;
		assert!(<MultiPhase<T>>::snapshot().is_none());
	}: {
		<MultiPhase::<T>>::create_snapshot_internal(targets, voters, desired_targets)
	} verify {
		assert!(<MultiPhase<T>>::snapshot().is_some());
		assert_eq!(<MultiPhase<T>>::snapshot_metadata().ok_or("metadata missing")?.voters, v + t);
		assert_eq!(<MultiPhase<T>>::snapshot_metadata().ok_or("metadata missing")?.targets, t);
	}

	// a call to `<Pallet as ElectionProvider>::elect` where we only return the queued solution.
	elect_queued {
		// number of assignments, i.e. solution.len(). This means the active nominators, thus must be
		// a subset of `v`.
		let a in (T::BenchmarkingConfig::ACTIVE_VOTERS[0]) .. T::BenchmarkingConfig::ACTIVE_VOTERS[1];
		// number of desired targets. Must be a subset of `t`.
		let d in (T::BenchmarkingConfig::DESIRED_TARGETS[0]) .. T::BenchmarkingConfig::DESIRED_TARGETS[1];

		// number of votes in snapshot. Not dominant.
		let v  = T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot. Not dominant.
		let t = T::BenchmarkingConfig::TARGETS[1];

		let witness = SolutionOrSnapshotSize { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d)?;
		let ready_solution =
			<MultiPhase<T>>::feasibility_check(raw_solution, ElectionCompute::Signed)
				.map_err(<&str>::from)?;
		<CurrentPhase<T>>::put(Phase::Signed);
		// assume a queued solution is stored, regardless of where it comes from.
		<QueuedSolution<T>>::put(ready_solution);

		// these are set by the `solution_with_size` function.
		assert!(<DesiredTargets<T>>::get().is_some());
		assert!(<Snapshot<T>>::get().is_some());
		assert!(<SnapshotMetadata<T>>::get().is_some());
	}: {
		assert_ok!(<MultiPhase<T> as ElectionProvider>::elect());
	} verify {
		assert!(<MultiPhase<T>>::queued_solution().is_none());
		assert!(<DesiredTargets<T>>::get().is_none());
		assert!(<Snapshot<T>>::get().is_none());
		assert!(<SnapshotMetadata<T>>::get().is_none());
		assert_eq!(<CurrentPhase<T>>::get(), <Phase<T::BlockNumber>>::Off);
	}

	submit {
		let c in 1 .. (T::SignedMaxSubmissions::get() - 1);

		// the solution will be worse than all of them meaning the score need to be checked against
		// ~ log2(c)
		let solution = RawSolution {
			score: [(10_000_000u128 - 1).into(), 0, 0],
			..Default::default()
		};

		<MultiPhase<T>>::create_snapshot().map_err(<&str>::from)?;
		MultiPhase::<T>::on_initialize_open_signed();
		<Round<T>>::put(1);

		let mut signed_submissions = SignedSubmissions::<T>::get();
		for i in 0..c {
			let raw_solution = RawSolution {
				score: [(10_000_000 + i).into(), 0, 0],
				..Default::default()
			};
			let signed_submission = SignedSubmission {
				raw_solution,
				who: account("submitters", i, SEED),
				deposit: Default::default(),
				reward: Default::default(),
			};
			signed_submissions.insert(signed_submission);
		}
		signed_submissions.put();

		let caller = frame_benchmarking::whitelisted_caller();
		T::Currency::make_free_balance_be(&caller,  T::Currency::minimum_balance() * 10u32.into());

	}: _(RawOrigin::Signed(caller), Box::new(solution), c)
	verify {
		assert!(<MultiPhase<T>>::signed_submissions().len() as u32 == c + 1);
	}

	submit_unsigned {
		// number of votes in snapshot.
		let v in (T::BenchmarkingConfig::VOTERS[0]) .. T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot.
		let t in (T::BenchmarkingConfig::TARGETS[0]) .. T::BenchmarkingConfig::TARGETS[1];
		// number of assignments, i.e. solution.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in
			(T::BenchmarkingConfig::ACTIVE_VOTERS[0]) .. T::BenchmarkingConfig::ACTIVE_VOTERS[1];
		// number of desired targets. Must be a subset of `t` component.
		let d in
			(T::BenchmarkingConfig::DESIRED_TARGETS[0]) ..
			T::BenchmarkingConfig::DESIRED_TARGETS[1];

		let witness = SolutionOrSnapshotSize { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(witness, a, d)?;

		assert!(<MultiPhase<T>>::queued_solution().is_none());
		<CurrentPhase<T>>::put(Phase::Unsigned((true, 1u32.into())));
	}: _(RawOrigin::None, Box::new(raw_solution), witness)
	verify {
		assert!(<MultiPhase<T>>::queued_solution().is_some());
	}

	// This is checking a valid solution. The worse case is indeed a valid solution.
	feasibility_check {
		// number of votes in snapshot.
		let v in (T::BenchmarkingConfig::VOTERS[0]) .. T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot.
		let t in (T::BenchmarkingConfig::TARGETS[0]) .. T::BenchmarkingConfig::TARGETS[1];
		// number of assignments, i.e. solution.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in (T::BenchmarkingConfig::ACTIVE_VOTERS[0]) .. T::BenchmarkingConfig::ACTIVE_VOTERS[1];
		// number of desired targets. Must be a subset of `t` component.
		let d in (T::BenchmarkingConfig::DESIRED_TARGETS[0]) .. T::BenchmarkingConfig::DESIRED_TARGETS[1];

		let size = SolutionOrSnapshotSize { voters: v, targets: t };
		let raw_solution = solution_with_size::<T>(size, a, d)?;

		assert_eq!(raw_solution.solution.voter_count() as u32, a);
		assert_eq!(raw_solution.solution.unique_targets().len() as u32, d);
	}: {
		assert_ok!(<MultiPhase<T>>::feasibility_check(raw_solution, ElectionCompute::Unsigned));
	}

	// NOTE: this weight is not used anywhere, but the fact that it should succeed when execution in
	// isolation is vital to ensure memory-safety. For the same reason, we don't care about the
	// components iterating, we merely check that this operation will work with the "maximum"
	// numbers.
	//
	// ONLY run this benchmark in isolation, and pass the `--extra` flag to enable it.
	//
	// NOTE: If this benchmark does not run out of memory with a given heap pages, it means that the
	// OCW process can SURELY succeed with the given configuration, but the opposite is not true.
	// This benchmark is doing more work than a raw call to `OffchainWorker_offchain_worker` runtime
	// api call, since it is also setting up some mock data, which will itself exhaust the heap to
	// some extent.
	#[extra]
	mine_solution_offchain_memory {
		// number of votes in snapshot. Fixed to maximum.
		let v = T::BenchmarkingConfig::MINER_MAXIMUM_VOTERS;
		// number of targets in snapshot. Fixed to maximum.
		let t = T::BenchmarkingConfig::MAXIMUM_TARGETS;

		set_up_data_provider::<T>(v, t);
		let now = frame_system::Pallet::<T>::block_number();
		<CurrentPhase<T>>::put(Phase::Unsigned((true, now)));
		<MultiPhase::<T>>::create_snapshot().unwrap();
	}: {
		// we can't really verify this as it won't write anything to state, check logs.
		<MultiPhase::<T>>::offchain_worker(now)
	}

	// NOTE: this weight is not used anywhere, but the fact that it should succeed when execution in
	// isolation is vital to ensure memory-safety. For the same reason, we don't care about the
	// components iterating, we merely check that this operation will work with the "maximum"
	// numbers.
	//
	// ONLY run this benchmark in isolation, and pass the `--extra` flag to enable it.
	#[extra]
	create_snapshot_memory {
		// number of votes in snapshot. Fixed to maximum.
		let v = T::BenchmarkingConfig::SNAPSHOT_MAXIMUM_VOTERS;
		// number of targets in snapshot. Fixed to maximum.
		let t = T::BenchmarkingConfig::MAXIMUM_TARGETS;

		set_up_data_provider::<T>(v, t);
		assert!(<MultiPhase<T>>::snapshot().is_none());
	}: {
		<MultiPhase::<T>>::create_snapshot().map_err(|_| "could not create snapshot")?;
	} verify {
		assert!(<MultiPhase<T>>::snapshot().is_some());
		assert_eq!(<MultiPhase<T>>::snapshot_metadata().ok_or("snapshot missing")?.voters, v + t);
		assert_eq!(<MultiPhase<T>>::snapshot_metadata().ok_or("snapshot missing")?.targets, t);
	}

	#[extra]
	trim_assignments_length {
		// number of votes in snapshot.
		let v in (T::BenchmarkingConfig::VOTERS[0]) .. T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot.
		let t in (T::BenchmarkingConfig::TARGETS[0]) .. T::BenchmarkingConfig::TARGETS[1];
		// number of assignments, i.e. solution.len(). This means the active nominators, thus must be
		// a subset of `v` component.
		let a in
			(T::BenchmarkingConfig::ACTIVE_VOTERS[0]) .. T::BenchmarkingConfig::ACTIVE_VOTERS[1];
		// number of desired targets. Must be a subset of `t` component.
		let d in
			(T::BenchmarkingConfig::DESIRED_TARGETS[0]) ..
			T::BenchmarkingConfig::DESIRED_TARGETS[1];
		// Subtract this percentage from the actual encoded size
		let f in 0 .. 95;

		// Compute a random solution, then work backwards to get the lists of voters, targets, and
		// assignments
		let witness = SolutionOrSnapshotSize { voters: v, targets: t };
		let RawSolution { solution, .. } = solution_with_size::<T>(witness, a, d)?;
		let RoundSnapshot { voters, targets } = MultiPhase::<T>::snapshot().ok_or("snapshot missing")?;
		let voter_at = helpers::voter_at_fn::<T>(&voters);
		let target_at = helpers::target_at_fn::<T>(&targets);
		let mut assignments = solution.into_assignment(voter_at, target_at).expect("solution generated by `solution_with_size` must be valid.");

		// make a voter cache and some helper functions for access
		let cache = helpers::generate_voter_cache::<T>(&voters);
		let voter_index = helpers::voter_index_fn::<T>(&cache);
		let target_index = helpers::target_index_fn::<T>(&targets);

		// sort assignments by decreasing voter stake
		assignments.sort_by_key(|crate::unsigned::Assignment::<T> { who, .. }| {
			let stake = cache.get(&who).map(|idx| {
				let (_, stake, _) = voters[*idx];
				stake
			}).unwrap_or_default();
			sp_std::cmp::Reverse(stake)
		});

		let mut index_assignments = assignments
			.into_iter()
			.map(|assignment| IndexAssignment::new(&assignment, &voter_index, &target_index))
			.collect::<Result<Vec<_>, _>>()
			.unwrap();

		let encoded_size_of = |assignments: &[IndexAssignmentOf<T>]| {
			SolutionOf::<T>::try_from(assignments).map(|solution| solution.encoded_size())
		};

		let desired_size = Percent::from_percent(100 - f.saturated_into::<u8>())
			.mul_ceil(encoded_size_of(index_assignments.as_slice()).unwrap());
		log!(trace, "desired_size = {}", desired_size);
	}: {
		MultiPhase::<T>::trim_assignments_length(
			desired_size.saturated_into(),
			&mut index_assignments,
			&encoded_size_of,
		).unwrap();
	} verify {
		let solution = SolutionOf::<T>::try_from(index_assignments.as_slice()).unwrap();
		let encoding = solution.encode();
		log!(
			trace,
			"encoded size prediction = {}",
			encoded_size_of(index_assignments.as_slice()).unwrap(),
		);
		log!(trace, "actual encoded size = {}", encoding.len());
		assert!(encoding.len() <= desired_size);
	}

	impl_benchmark_test_suite!(
		MultiPhase,
		crate::mock::ExtBuilder::default().build_offchainify(10).0,
		crate::mock::Runtime,
	);
}
