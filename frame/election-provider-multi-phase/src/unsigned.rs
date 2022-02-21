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

//! The unsigned phase, and its miner.

use crate::{
	helpers, Call, Config, ElectionCompute, Error, FeasibilityError, Pallet, RawSolution,
	ReadySolution, RoundSnapshot, SolutionAccuracyOf, SolutionOf, SolutionOrSnapshotSize, Weight,
	WeightInfo,
};
use codec::Encode;
use frame_election_provider_support::{NposSolver, PerThing128};
use frame_support::{dispatch::DispatchResult, ensure, traits::Get};
use frame_system::offchain::SubmitTransaction;
use sp_npos_elections::{
	assignment_ratio_to_staked_normalized, assignment_staked_to_ratio_normalized, ElectionResult,
	NposSolution,
};
use sp_runtime::{
	offchain::storage::{MutateStorageError, StorageValueRef},
	DispatchError, SaturatedConversion,
};
use sp_std::{cmp::Ordering, prelude::*};

/// Storage key used to store the last block number at which offchain worker ran.
pub(crate) const OFFCHAIN_LAST_BLOCK: &[u8] = b"parity/multi-phase-unsigned-election";
/// Storage key used to store the offchain worker running status.
pub(crate) const OFFCHAIN_LOCK: &[u8] = b"parity/multi-phase-unsigned-election/lock";

/// Storage key used to cache the solution `call`.
pub(crate) const OFFCHAIN_CACHED_CALL: &[u8] = b"parity/multi-phase-unsigned-election/call";

/// A voter's fundamental data: their ID, their stake, and the list of candidates for whom they
/// voted.
pub type VoterOf<T> = frame_election_provider_support::VoterOf<<T as Config>::DataProvider>;

/// The relative distribution of a voter's stake among the winning targets.
pub type Assignment<T> =
	sp_npos_elections::Assignment<<T as frame_system::Config>::AccountId, SolutionAccuracyOf<T>>;

/// The [`IndexAssignment`][sp_npos_elections::IndexAssignment] type specialized for a particular
/// runtime `T`.
pub type IndexAssignmentOf<T> = sp_npos_elections::IndexAssignmentOf<SolutionOf<T>>;

/// Error type of the pallet's [`crate::Config::Solver`].
pub type SolverErrorOf<T> = <<T as Config>::Solver as NposSolver>::Error;
/// Error type for operations related to the OCW npos solution miner.
#[derive(frame_support::DebugNoBound, frame_support::PartialEqNoBound)]
pub enum MinerError<T: Config> {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	PoolSubmissionFailed,
	/// The pre-dispatch checks failed for the mined solution.
	PreDispatchChecksFailed(DispatchError),
	/// The solution generated from the miner is not feasible.
	Feasibility(FeasibilityError),
	/// Something went wrong fetching the lock.
	Lock(&'static str),
	/// Cannot restore a solution that was not stored.
	NoStoredSolution,
	/// Cached solution is not a `submit_unsigned` call.
	SolutionCallInvalid,
	/// Failed to store a solution.
	FailedToStoreSolution,
	/// There are no more voters to remove to trim the solution.
	NoMoreVoters,
	/// An error from the solver.
	Solver(SolverErrorOf<T>),
}

impl<T: Config> From<sp_npos_elections::Error> for MinerError<T> {
	fn from(e: sp_npos_elections::Error) -> Self {
		MinerError::NposElections(e)
	}
}

impl<T: Config> From<FeasibilityError> for MinerError<T> {
	fn from(e: FeasibilityError) -> Self {
		MinerError::Feasibility(e)
	}
}

/// Save a given call into OCW storage.
fn save_solution<T: Config>(call: &Call<T>) -> Result<(), MinerError<T>> {
	log!(debug, "saving a call to the offchain storage.");
	let storage = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
	match storage.mutate::<_, (), _>(|_| Ok(call.clone())) {
		Ok(_) => Ok(()),
		Err(MutateStorageError::ConcurrentModification(_)) =>
			Err(MinerError::FailedToStoreSolution),
		Err(MutateStorageError::ValueFunctionFailed(_)) => {
			// this branch should be unreachable according to the definition of
			// `StorageValueRef::mutate`: that function should only ever `Err` if the closure we
			// pass it returns an error. however, for safety in case the definition changes, we do
			// not optimize the branch away or panic.
			Err(MinerError::FailedToStoreSolution)
		},
	}
}

/// Get a saved solution from OCW storage if it exists.
fn restore_solution<T: Config>() -> Result<Call<T>, MinerError<T>> {
	StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL)
		.get()
		.ok()
		.flatten()
		.ok_or(MinerError::NoStoredSolution)
}

/// Clear a saved solution from OCW storage.
pub(super) fn kill_ocw_solution<T: Config>() {
	log!(debug, "clearing offchain call cache storage.");
	let mut storage = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
	storage.clear();
}

/// Clear the offchain repeat storage.
///
/// After calling this, the next offchain worker is guaranteed to work, with respect to the
/// frequency repeat.
fn clear_offchain_repeat_frequency() {
	let mut last_block = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);
	last_block.clear();
}

/// `true` when OCW storage contains a solution
#[cfg(test)]
fn ocw_solution_exists<T: Config>() -> bool {
	matches!(StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL).get::<Call<T>>(), Ok(Some(_)))
}

impl<T: Config> Pallet<T> {
	/// Attempt to restore a solution from cache. Otherwise, compute it fresh. Either way, submit
	/// if our call's score is greater than that of the cached solution.
	pub fn restore_or_compute_then_maybe_submit() -> Result<(), MinerError<T>> {
		log!(debug, "miner attempting to restore or compute an unsigned solution.");

		let call = restore_solution::<T>()
			.and_then(|call| {
				// ensure the cached call is still current before submitting
				if let Call::submit_unsigned { raw_solution, .. } = &call {
					// prevent errors arising from state changes in a forkful chain
					Self::basic_checks(raw_solution, "restored")?;
					Ok(call)
				} else {
					Err(MinerError::SolutionCallInvalid)
				}
			})
			.or_else::<MinerError<T>, _>(|error| {
				log!(debug, "restoring solution failed due to {:?}", error);
				match error {
					MinerError::NoStoredSolution => {
						log!(trace, "mining a new solution.");
						// if not present or cache invalidated due to feasibility, regenerate.
						// note that failing `Feasibility` can only mean that the solution was
						// computed over a snapshot that has changed due to a fork.
						let call = Self::mine_checked_call()?;
						save_solution(&call)?;
						Ok(call)
					},
					MinerError::Feasibility(_) => {
						log!(trace, "wiping infeasible solution.");
						// kill the infeasible solution, hopefully in the next runs (whenever they
						// may be) we mine a new one.
						kill_ocw_solution::<T>();
						clear_offchain_repeat_frequency();
						Err(error)
					},
					_ => {
						// nothing to do. Return the error as-is.
						Err(error)
					},
				}
			})?;

		Self::submit_call(call)
	}

	/// Mine a new solution, cache it, and submit it back to the chain as an unsigned transaction.
	pub fn mine_check_save_submit() -> Result<(), MinerError<T>> {
		log!(debug, "miner attempting to compute an unsigned solution.");

		let call = Self::mine_checked_call()?;
		save_solution(&call)?;
		Self::submit_call(call)
	}

	/// Mine a new solution as a call. Performs all checks.
	pub fn mine_checked_call() -> Result<Call<T>, MinerError<T>> {
		// get the solution, with a load of checks to ensure if submitted, IT IS ABSOLUTELY VALID.
		let (raw_solution, witness) = Self::mine_and_check()?;

		let score = raw_solution.score.clone();
		let call: Call<T> =
			Call::submit_unsigned { raw_solution: Box::new(raw_solution), witness }.into();

		log!(
			debug,
			"mined a solution with score {:?} and size {}",
			score,
			call.using_encoded(|b| b.len())
		);

		Ok(call)
	}

	fn submit_call(call: Call<T>) -> Result<(), MinerError<T>> {
		log!(debug, "miner submitting a solution as an unsigned transaction");

		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into())
			.map_err(|_| MinerError::PoolSubmissionFailed)
	}

	// perform basic checks of a solution's validity
	//
	// Performance: note that it internally clones the provided solution.
	pub fn basic_checks(
		raw_solution: &RawSolution<SolutionOf<T>>,
		solution_type: &str,
	) -> Result<(), MinerError<T>> {
		Self::unsigned_pre_dispatch_checks(raw_solution).map_err(|err| {
			log!(debug, "pre-dispatch checks failed for {} solution: {:?}", solution_type, err);
			MinerError::PreDispatchChecksFailed(err)
		})?;

		Self::feasibility_check(raw_solution.clone(), ElectionCompute::Unsigned).map_err(
			|err| {
				log!(debug, "feasibility check failed for {} solution: {:?}", solution_type, err);
				err
			},
		)?;

		Ok(())
	}

	/// Mine a new npos solution, with all the relevant checks to make sure that it will be accepted
	/// to the chain.
	///
	/// If you want an unchecked solution, use [`Pallet::mine_solution`].
	/// If you want a checked solution and submit it at the same time, use
	/// [`Pallet::mine_check_save_submit`].
	pub fn mine_and_check(
	) -> Result<(RawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError<T>> {
		let (raw_solution, witness) = Self::mine_solution::<T::Solver>()?;
		Self::basic_checks(&raw_solution, "mined")?;
		Ok((raw_solution, witness))
	}

	/// Mine a new npos solution.
	///
	/// The Npos Solver type, `S`, must have the same AccountId and Error type as the
	/// [`crate::Config::Solver`] in order to create a unified return type.
	pub fn mine_solution<S>(
	) -> Result<(RawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError<T>>
	where
		S: NposSolver<AccountId = T::AccountId, Error = SolverErrorOf<T>>,
	{
		let RoundSnapshot { voters, targets } =
			Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
		let desired_targets = Self::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;

		S::solve(desired_targets as usize, targets, voters)
			.map_err(|e| MinerError::Solver::<T>(e))
			.and_then(|e| Self::prepare_election_result::<S::Accuracy>(e))
	}

	/// Convert a raw solution from [`sp_npos_elections::ElectionResult`] to [`RawSolution`], which
	/// is ready to be submitted to the chain.
	///
	/// Will always reduce the solution as well.
	pub fn prepare_election_result<Accuracy: PerThing128>(
		election_result: ElectionResult<T::AccountId, Accuracy>,
	) -> Result<(RawSolution<SolutionOf<T>>, SolutionOrSnapshotSize), MinerError<T>> {
		// NOTE: This code path is generally not optimized as it is run offchain. Could use some at
		// some point though.

		// storage items. Note: we have already read this from storage, they must be in cache.
		let RoundSnapshot { voters, targets } =
			Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
		let desired_targets = Self::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;

		// now make some helper closures.
		let cache = helpers::generate_voter_cache::<T>(&voters);
		let voter_index = helpers::voter_index_fn::<T>(&cache);
		let target_index = helpers::target_index_fn::<T>(&targets);
		let voter_at = helpers::voter_at_fn::<T>(&voters);
		let target_at = helpers::target_at_fn::<T>(&targets);
		let stake_of = helpers::stake_of_fn::<T>(&voters, &cache);

		// Compute the size of a solution comprised of the selected arguments.
		//
		// This function completes in `O(edges)`; it's expensive, but linear.
		let encoded_size_of = |assignments: &[IndexAssignmentOf<T>]| {
			SolutionOf::<T>::try_from(assignments).map(|s| s.encoded_size())
		};

		let ElectionResult { assignments, winners: _ } = election_result;

		// Reduce (requires round-trip to staked form)
		let sorted_assignments = {
			// convert to staked and reduce.
			let mut staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)?;

			// we reduce before sorting in order to ensure that the reduction process doesn't
			// accidentally change the sort order
			sp_npos_elections::reduce(&mut staked);

			// Sort the assignments by reversed voter stake. This ensures that we can efficiently
			// truncate the list.
			staked.sort_by_key(
				|sp_npos_elections::StakedAssignment::<T::AccountId> { who, .. }| {
					// though staked assignments are expressed in terms of absolute stake, we'd
					// still need to iterate over all votes in order to actually compute the total
					// stake. it should be faster to look it up from the cache.
					let stake = cache
						.get(who)
						.map(|idx| {
							let (_, stake, _) = voters[*idx];
							stake
						})
						.unwrap_or_default();
					sp_std::cmp::Reverse(stake)
				},
			);

			// convert back.
			assignment_staked_to_ratio_normalized(staked)?
		};

		// convert to `IndexAssignment`. This improves the runtime complexity of repeatedly
		// converting to `Solution`.
		let mut index_assignments = sorted_assignments
			.into_iter()
			.map(|assignment| IndexAssignmentOf::<T>::new(&assignment, &voter_index, &target_index))
			.collect::<Result<Vec<_>, _>>()?;

		// trim assignments list for weight and length.
		let size =
			SolutionOrSnapshotSize { voters: voters.len() as u32, targets: targets.len() as u32 };
		Self::trim_assignments_weight(
			desired_targets,
			size,
			T::MinerMaxWeight::get(),
			&mut index_assignments,
		);
		Self::trim_assignments_length(
			T::MinerMaxLength::get(),
			&mut index_assignments,
			&encoded_size_of,
		)?;

		// now make solution.
		let solution = SolutionOf::<T>::try_from(&index_assignments)?;

		// re-calc score.
		let score = solution.clone().score(stake_of, voter_at, target_at)?;

		let round = Self::round();
		Ok((RawSolution { solution, score, round }, size))
	}

	/// Greedily reduce the size of the solution to fit into the block w.r.t. weight.
	///
	/// The weight of the solution is foremost a function of the number of voters (i.e.
	/// `assignments.len()`). Aside from this, the other components of the weight are invariant. The
	/// number of winners shall not be changed (otherwise the solution is invalid) and the
	/// `ElectionSize` is merely a representation of the total number of stakers.
	///
	/// Thus, we reside to stripping away some voters from the `assignments`.
	///
	/// Note that the solution is already computed, and the winners are elected based on the merit
	/// of the entire stake in the system. Nonetheless, some of the voters will be removed further
	/// down the line.
	///
	/// Indeed, the score must be computed **after** this step. If this step reduces the score too
	/// much or remove a winner, then the solution must be discarded **after** this step.
	pub fn trim_assignments_weight(
		desired_targets: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
		assignments: &mut Vec<IndexAssignmentOf<T>>,
	) {
		let maximum_allowed_voters =
			Self::maximum_voter_for_weight::<T::WeightInfo>(desired_targets, size, max_weight);
		let removing: usize =
			assignments.len().saturating_sub(maximum_allowed_voters.saturated_into());
		log!(
			debug,
			"from {} assignments, truncating to {} for weight, removing {}",
			assignments.len(),
			maximum_allowed_voters,
			removing,
		);
		assignments.truncate(maximum_allowed_voters as usize);
	}

	/// Greedily reduce the size of the solution to fit into the block w.r.t length.
	///
	/// The length of the solution is largely a function of the number of voters. The number of
	/// winners cannot be changed. Thus, to reduce the solution size, we need to strip voters.
	///
	/// Note that this solution is already computed, and winners are elected based on the merit of
	/// the total stake in the system. Nevertheless, some of the voters may be removed here.
	///
	/// Sometimes, removing a voter can cause a validator to also be implicitly removed, if
	/// that voter was the only backer of that winner. In such cases, this solution is invalid,
	/// which will be caught prior to submission.
	///
	/// The score must be computed **after** this step. If this step reduces the score too much,
	/// then the solution must be discarded.
	pub fn trim_assignments_length(
		max_allowed_length: u32,
		assignments: &mut Vec<IndexAssignmentOf<T>>,
		encoded_size_of: impl Fn(&[IndexAssignmentOf<T>]) -> Result<usize, sp_npos_elections::Error>,
	) -> Result<(), MinerError<T>> {
		// Perform a binary search for the max subset of which can fit into the allowed
		// length. Having discovered that, we can truncate efficiently.
		let max_allowed_length: usize = max_allowed_length.saturated_into();
		let mut high = assignments.len();
		let mut low = 0;

		// not much we can do if assignments are already empty.
		if high == low {
			return Ok(())
		}

		while high - low > 1 {
			let test = (high + low) / 2;
			if encoded_size_of(&assignments[..test])? <= max_allowed_length {
				low = test;
			} else {
				high = test;
			}
		}
		let maximum_allowed_voters = if low < assignments.len() &&
			encoded_size_of(&assignments[..low + 1])? <= max_allowed_length
		{
			low + 1
		} else {
			low
		};

		// ensure our post-conditions are correct
		debug_assert!(
			encoded_size_of(&assignments[..maximum_allowed_voters]).unwrap() <= max_allowed_length
		);
		debug_assert!(if maximum_allowed_voters < assignments.len() {
			encoded_size_of(&assignments[..maximum_allowed_voters + 1]).unwrap() >
				max_allowed_length
		} else {
			true
		});

		// NOTE: before this point, every access was immutable.
		// after this point, we never error.
		// check before edit.

		log!(
			debug,
			"from {} assignments, truncating to {} for length, removing {}",
			assignments.len(),
			maximum_allowed_voters,
			assignments.len().saturating_sub(maximum_allowed_voters),
		);
		assignments.truncate(maximum_allowed_voters);

		Ok(())
	}

	/// Find the maximum `len` that a solution can have in order to fit into the block weight.
	///
	/// This only returns a value between zero and `size.nominators`.
	pub fn maximum_voter_for_weight<W: WeightInfo>(
		desired_winners: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
	) -> u32 {
		if size.voters < 1 {
			return size.voters
		}

		let max_voters = size.voters.max(1);
		let mut voters = max_voters;

		// helper closures.
		let weight_with = |active_voters: u32| -> Weight {
			W::submit_unsigned(size.voters, size.targets, active_voters, desired_winners)
		};

		let next_voters = |current_weight: Weight, voters: u32, step: u32| -> Result<u32, ()> {
			match current_weight.cmp(&max_weight) {
				Ordering::Less => {
					let next_voters = voters.checked_add(step);
					match next_voters {
						Some(voters) if voters < max_voters => Ok(voters),
						_ => Err(()),
					}
				},
				Ordering::Greater => voters.checked_sub(step).ok_or(()),
				Ordering::Equal => Ok(voters),
			}
		};

		// First binary-search the right amount of voters
		let mut step = voters / 2;
		let mut current_weight = weight_with(voters);

		while step > 0 {
			match next_voters(current_weight, voters, step) {
				// proceed with the binary search
				Ok(next) if next != voters => {
					voters = next;
				},
				// we are out of bounds, break out of the loop.
				Err(()) => break,
				// we found the right value - early exit the function.
				Ok(next) => return next,
			}
			step = step / 2;
			current_weight = weight_with(voters);
		}

		// Time to finish. We might have reduced less than expected due to rounding error. Increase
		// one last time if we have any room left, the reduce until we are sure we are below limit.
		while voters < max_voters && weight_with(voters + 1) < max_weight {
			voters += 1;
		}
		while voters.checked_sub(1).is_some() && weight_with(voters) > max_weight {
			voters -= 1;
		}

		let final_decision = voters.min(size.voters);
		debug_assert!(
			weight_with(final_decision) <= max_weight,
			"weight_with({}) <= {}",
			final_decision,
			max_weight,
		);
		final_decision
	}

	/// Checks if an execution of the offchain worker is permitted at the given block number, or
	/// not.
	///
	/// This makes sure that
	/// 1. we don't run on previous blocks in case of a re-org
	/// 2. we don't run twice within a window of length `T::OffchainRepeat`.
	///
	/// Returns `Ok(())` if offchain worker limit is respected, `Err(reason)` otherwise. If `Ok()`
	/// is returned, `now` is written in storage and will be used in further calls as the baseline.
	pub fn ensure_offchain_repeat_frequency(now: T::BlockNumber) -> Result<(), MinerError<T>> {
		let threshold = T::OffchainRepeat::get();
		let last_block = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

		let mutate_stat = last_block.mutate::<_, &'static str, _>(
			|maybe_head: Result<Option<T::BlockNumber>, _>| {
				match maybe_head {
					Ok(Some(head)) if now < head => Err("fork."),
					Ok(Some(head)) if now >= head && now <= head + threshold =>
						Err("recently executed."),
					Ok(Some(head)) if now > head + threshold => {
						// we can run again now. Write the new head.
						Ok(now)
					},
					_ => {
						// value doesn't exists. Probably this node just booted up. Write, and run
						Ok(now)
					},
				}
			},
		);

		match mutate_stat {
			// all good
			Ok(_) => Ok(()),
			// failed to write.
			Err(MutateStorageError::ConcurrentModification(_)) =>
				Err(MinerError::Lock("failed to write to offchain db (concurrent modification).")),
			// fork etc.
			Err(MutateStorageError::ValueFunctionFailed(why)) => Err(MinerError::Lock(why)),
		}
	}

	/// Do the basics checks that MUST happen during the validation and pre-dispatch of an unsigned
	/// transaction.
	///
	/// Can optionally also be called during dispatch, if needed.
	///
	/// NOTE: Ideally, these tests should move more and more outside of this and more to the miner's
	/// code, so that we do less and less storage reads here.
	pub fn unsigned_pre_dispatch_checks(
		raw_solution: &RawSolution<SolutionOf<T>>,
	) -> DispatchResult {
		// ensure solution is timely. Don't panic yet. This is a cheap check.
		ensure!(Self::current_phase().is_unsigned_open(), Error::<T>::PreDispatchEarlySubmission);

		// ensure round is current
		ensure!(Self::round() == raw_solution.round, Error::<T>::OcwCallWrongEra);

		// ensure correct number of winners.
		ensure!(
			Self::desired_targets().unwrap_or_default() ==
				raw_solution.solution.unique_targets().len() as u32,
			Error::<T>::PreDispatchWrongWinnerCount,
		);

		// ensure score is being improved. Panic henceforth.
		ensure!(
			Self::queued_solution().map_or(true, |q: ReadySolution<_>| raw_solution
				.score
				.strict_threshold_better(q.score, T::SolutionImprovementThreshold::get())),
			Error::<T>::PreDispatchWeakSubmission,
		);

		Ok(())
	}
}

#[cfg(test)]
mod max_weight {
	#![allow(unused_variables)]
	use super::*;
	use crate::mock::MultiPhase;

	struct TestWeight;
	impl crate::weights::WeightInfo for TestWeight {
		fn elect_queued(a: u32, d: u32) -> Weight {
			unreachable!()
		}
		fn create_snapshot_internal(v: u32, t: u32) -> Weight {
			unreachable!()
		}
		fn on_initialize_nothing() -> Weight {
			unreachable!()
		}
		fn on_initialize_open_signed() -> Weight {
			unreachable!()
		}
		fn on_initialize_open_unsigned() -> Weight {
			unreachable!()
		}
		fn finalize_signed_phase_accept_solution() -> Weight {
			unreachable!()
		}
		fn finalize_signed_phase_reject_solution() -> Weight {
			unreachable!()
		}
		fn submit(c: u32) -> Weight {
			unreachable!()
		}
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
			(0 * v + 0 * t + 1000 * a + 0 * d) as Weight
		}
		fn feasibility_check(v: u32, _t: u32, a: u32, d: u32) -> Weight {
			unreachable!()
		}
	}

	#[test]
	fn find_max_voter_binary_search_works() {
		let w = SolutionOrSnapshotSize { voters: 10, targets: 0 };

		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2990), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2999), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 3000), 3);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 3);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 5500), 5);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 7777), 7);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 9999), 9);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 10_000), 10);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 10_999), 10);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 11_000), 10);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 22_000), 10);

		let w = SolutionOrSnapshotSize { voters: 1, targets: 0 };

		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 1);

		let w = SolutionOrSnapshotSize { voters: 2, targets: 0 };

		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(MultiPhase::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 2);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		mock::{
			roll_to, roll_to_with_ocw, trim_helpers, witness, BlockNumber, Call as OuterCall,
			ExtBuilder, Extrinsic, MinerMaxWeight, MultiPhase, Origin, Runtime, System,
			TestNposSolution, TrimHelpers, UnsignedPhase,
		},
		CurrentPhase, InvalidTransaction, Phase, QueuedSolution, TransactionSource,
		TransactionValidityError,
	};
	use codec::Decode;
	use frame_benchmarking::Zero;
	use frame_support::{
		assert_noop, assert_ok, bounded_vec, dispatch::Dispatchable, traits::OffchainWorker,
	};
	use sp_npos_elections::{ElectionScore, IndexAssignment};
	use sp_runtime::{
		offchain::storage_lock::{BlockAndTime, StorageLock},
		traits::ValidateUnsigned,
		ModuleError, PerU16, Perbill,
	};

	type Assignment = crate::unsigned::Assignment<Runtime>;

	#[test]
	fn validate_unsigned_retracts_wrong_phase() {
		ExtBuilder::default().desired_targets(0).build_and_execute(|| {
			let solution = RawSolution::<TestNposSolution> {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			let call = Call::submit_unsigned {
				raw_solution: Box::new(solution.clone()),
				witness: witness(),
			};

			// initial
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));

			// signed
			roll_to(15);
			assert_eq!(MultiPhase::current_phase(), Phase::Signed);
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));

			// unsigned
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			assert!(<MultiPhase as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).is_ok());

			// unsigned -- but not enabled.
			<CurrentPhase<Runtime>>::put(Phase::Unsigned((false, 25)));
			assert!(MultiPhase::current_phase().is_unsigned());
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
		})
	}

	#[test]
	fn validate_unsigned_retracts_low_score() {
		ExtBuilder::default().desired_targets(0).build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			let solution = RawSolution::<TestNposSolution> {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			let call = Call::submit_unsigned {
				raw_solution: Box::new(solution.clone()),
				witness: witness(),
			};

			// initial
			assert!(<MultiPhase as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).is_ok());

			// set a better score
			let ready = ReadySolution {
				score: ElectionScore { minimal_stake: 10, ..Default::default() },
				..Default::default()
			};
			<QueuedSolution<Runtime>>::put(ready);

			// won't work anymore.
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(2))
			));
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(2))
			));
		})
	}

	#[test]
	fn validate_unsigned_retracts_incorrect_winner_count() {
		ExtBuilder::default().desired_targets(1).build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			let raw = RawSolution::<TestNposSolution> {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			let call =
				Call::submit_unsigned { raw_solution: Box::new(raw.clone()), witness: witness() };
			assert_eq!(raw.solution.unique_targets().len(), 0);

			// won't work anymore.
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(1))
			));
		})
	}

	#[test]
	fn priority_is_set() {
		ExtBuilder::default()
			.miner_tx_priority(20)
			.desired_targets(0)
			.build_and_execute(|| {
				roll_to(25);
				assert!(MultiPhase::current_phase().is_unsigned());

				let solution = RawSolution::<TestNposSolution> {
					score: ElectionScore { minimal_stake: 5, ..Default::default() },
					..Default::default()
				};
				let call = Call::submit_unsigned {
					raw_solution: Box::new(solution.clone()),
					witness: witness(),
				};

				assert_eq!(
					<MultiPhase as ValidateUnsigned>::validate_unsigned(
						TransactionSource::Local,
						&call
					)
					.unwrap()
					.priority,
					25
				);
			})
	}

	#[test]
	#[should_panic(expected = "Invalid unsigned submission must produce invalid block and \
	                           deprive validator from their authoring reward.: \
	                           Module(ModuleError { index: 2, error: 1, message: \
	                           Some(\"PreDispatchWrongWinnerCount\") })")]
	fn unfeasible_solution_panics() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// This is in itself an invalid BS solution.
			let solution = RawSolution::<TestNposSolution> {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			let call = Call::submit_unsigned {
				raw_solution: Box::new(solution.clone()),
				witness: witness(),
			};
			let outer_call: OuterCall = call.into();
			let _ = outer_call.dispatch(Origin::none());
		})
	}

	#[test]
	#[should_panic(expected = "Invalid unsigned submission must produce invalid block and \
	                           deprive validator from their authoring reward.")]
	fn wrong_witness_panics() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// This solution is unfeasible as well, but we won't even get there.
			let solution = RawSolution::<TestNposSolution> {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};

			let mut correct_witness = witness();
			correct_witness.voters += 1;
			correct_witness.targets -= 1;
			let call = Call::submit_unsigned {
				raw_solution: Box::new(solution.clone()),
				witness: correct_witness,
			};
			let outer_call: OuterCall = call.into();
			let _ = outer_call.dispatch(Origin::none());
		})
	}

	#[test]
	fn miner_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// ensure we have snapshots in place.
			assert!(MultiPhase::snapshot().is_some());
			assert_eq!(MultiPhase::desired_targets().unwrap(), 2);

			// mine seq_phragmen solution with 2 iters.
			let (solution, witness) =
				MultiPhase::mine_solution::<<Runtime as Config>::Solver>().unwrap();

			// ensure this solution is valid.
			assert!(MultiPhase::queued_solution().is_none());
			assert_ok!(MultiPhase::submit_unsigned(Origin::none(), Box::new(solution), witness));
			assert!(MultiPhase::queued_solution().is_some());
		})
	}

	#[test]
	fn miner_trims_weight() {
		ExtBuilder::default()
			.miner_weight(100)
			.mock_weight_info(true)
			.build_and_execute(|| {
				roll_to(25);
				assert!(MultiPhase::current_phase().is_unsigned());

				let (raw, witness) =
					MultiPhase::mine_solution::<<Runtime as Config>::Solver>().unwrap();
				let solution_weight = <Runtime as Config>::WeightInfo::submit_unsigned(
					witness.voters,
					witness.targets,
					raw.solution.voter_count() as u32,
					raw.solution.unique_targets().len() as u32,
				);
				// default solution will have 5 edges (5 * 5 + 10)
				assert_eq!(solution_weight, 35);
				assert_eq!(raw.solution.voter_count(), 5);

				// now reduce the max weight
				<MinerMaxWeight>::set(25);

				let (raw, witness) =
					MultiPhase::mine_solution::<<Runtime as Config>::Solver>().unwrap();
				let solution_weight = <Runtime as Config>::WeightInfo::submit_unsigned(
					witness.voters,
					witness.targets,
					raw.solution.voter_count() as u32,
					raw.solution.unique_targets().len() as u32,
				);
				// default solution will have 5 edges (5 * 5 + 10)
				assert_eq!(solution_weight, 25);
				assert_eq!(raw.solution.voter_count(), 3);
			})
	}

	#[test]
	fn miner_will_not_submit_if_not_enough_winners() {
		let (mut ext, _) = ExtBuilder::default().desired_targets(8).build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			assert_eq!(
				MultiPhase::mine_check_save_submit().unwrap_err(),
				MinerError::PreDispatchChecksFailed(DispatchError::Module(ModuleError {
					index: 2,
					error: 1,
					message: Some("PreDispatchWrongWinnerCount"),
				})),
			);
		})
	}

	#[test]
	fn unsigned_per_dispatch_checks_can_only_submit_threshold_better() {
		ExtBuilder::default()
			.desired_targets(1)
			.add_voter(7, 2, bounded_vec![10])
			.add_voter(8, 5, bounded_vec![10])
			.solution_improvement_threshold(Perbill::from_percent(50))
			.build_and_execute(|| {
				roll_to(25);
				assert!(MultiPhase::current_phase().is_unsigned());
				assert_eq!(MultiPhase::desired_targets().unwrap(), 1);

				// an initial solution
				let result = ElectionResult {
					// note: This second element of backing stake is not important here.
					winners: vec![(10, 10)],
					assignments: vec![Assignment {
						who: 10,
						distribution: vec![(10, PerU16::one())],
					}],
				};
				let (solution, witness) = MultiPhase::prepare_election_result(result).unwrap();
				assert_ok!(MultiPhase::unsigned_pre_dispatch_checks(&solution));
				assert_ok!(MultiPhase::submit_unsigned(
					Origin::none(),
					Box::new(solution),
					witness
				));
				assert_eq!(MultiPhase::queued_solution().unwrap().score.minimal_stake, 10);

				// trial 1: a solution who's score is only 2, i.e. 20% better in the first element.
				let result = ElectionResult {
					winners: vec![(10, 12)],
					assignments: vec![
						Assignment { who: 10, distribution: vec![(10, PerU16::one())] },
						Assignment {
							who: 7,
							// note: this percent doesn't even matter, in solution it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let (solution, _) = MultiPhase::prepare_election_result(result).unwrap();
				// 12 is not 50% more than 10
				assert_eq!(solution.score.minimal_stake, 12);
				assert_noop!(
					MultiPhase::unsigned_pre_dispatch_checks(&solution),
					Error::<Runtime>::PreDispatchWeakSubmission,
				);
				// submitting this will actually panic.

				// trial 2: a solution who's score is only 7, i.e. 70% better in the first element.
				let result = ElectionResult {
					winners: vec![(10, 12)],
					assignments: vec![
						Assignment { who: 10, distribution: vec![(10, PerU16::one())] },
						Assignment { who: 7, distribution: vec![(10, PerU16::one())] },
						Assignment {
							who: 8,
							// note: this percent doesn't even matter, in solution it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let (solution, witness) = MultiPhase::prepare_election_result(result).unwrap();
				assert_eq!(solution.score.minimal_stake, 17);

				// and it is fine
				assert_ok!(MultiPhase::unsigned_pre_dispatch_checks(&solution));
				assert_ok!(MultiPhase::submit_unsigned(
					Origin::none(),
					Box::new(solution),
					witness
				));
			})
	}

	#[test]
	fn ocw_lock_prevents_frequent_execution() {
		let (mut ext, _) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// first execution -- okay.
			assert!(MultiPhase::ensure_offchain_repeat_frequency(25).is_ok());

			// next block: rejected.
			assert_noop!(
				MultiPhase::ensure_offchain_repeat_frequency(26),
				MinerError::Lock("recently executed.")
			);

			// allowed after `OFFCHAIN_REPEAT`
			assert!(
				MultiPhase::ensure_offchain_repeat_frequency((26 + offchain_repeat).into()).is_ok()
			);

			// a fork like situation: re-execute last 3.
			assert!(MultiPhase::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 3).into()
			)
			.is_err());
			assert!(MultiPhase::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 2).into()
			)
			.is_err());
			assert!(MultiPhase::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 1).into()
			)
			.is_err());
		})
	}

	#[test]
	fn ocw_lock_released_after_successful_execution() {
		// first, ensure that a successful execution releases the lock
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			let guard = StorageValueRef::persistent(&OFFCHAIN_LOCK);
			let last_block = StorageValueRef::persistent(OFFCHAIN_LAST_BLOCK);

			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// initially, the lock is not set.
			assert!(guard.get::<bool>().unwrap().is_none());

			// a successful a-z execution.
			MultiPhase::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);

			// afterwards, the lock is not set either..
			assert!(guard.get::<bool>().unwrap().is_none());
			assert_eq!(last_block.get::<BlockNumber>().unwrap(), Some(25));
		});
	}

	#[test]
	fn ocw_lock_prevents_overlapping_execution() {
		// ensure that if the guard is in hold, a new execution is not allowed.
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// artificially set the value, as if another thread is mid-way.
			let mut lock = StorageLock::<BlockAndTime<System>>::with_block_deadline(
				OFFCHAIN_LOCK,
				UnsignedPhase::get().saturated_into(),
			);
			let guard = lock.lock();

			// nothing submitted.
			MultiPhase::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 0);
			MultiPhase::offchain_worker(26);
			assert_eq!(pool.read().transactions.len(), 0);

			drop(guard);

			// 🎉 !
			MultiPhase::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
		});
	}

	#[test]
	fn ocw_only_runs_when_unsigned_open_now() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiPhase::offchain_worker(24);
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiPhase::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// locked, but also, has previously cached.
			MultiPhase::offchain_worker(26);
			assert!(pool.read().transactions.len().is_zero());
		})
	}

	#[test]
	fn ocw_clears_cache_on_unsigned_phase_open() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			const BLOCK: u64 = 25;
			let block_plus = |delta: u64| BLOCK + delta;
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(BLOCK);
			// we are on the first block of the unsigned phase
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, BLOCK)));

			assert!(
				!ocw_solution_exists::<Runtime>(),
				"no solution should be present before we mine one",
			);

			// create and cache a solution on the first block of the unsigned phase
			MultiPhase::offchain_worker(BLOCK);
			assert!(
				ocw_solution_exists::<Runtime>(),
				"a solution must be cached after running the worker",
			);

			// record the submitted tx,
			let tx_cache_1 = pool.read().transactions[0].clone();
			// and assume it has been processed.
			pool.try_write().unwrap().transactions.clear();

			// after an election, the solution is not cleared
			// we don't actually care about the result of the election
			let _ = MultiPhase::do_elect();
			MultiPhase::offchain_worker(block_plus(1));
			assert!(ocw_solution_exists::<Runtime>(), "elections does not clear the ocw cache");

			// submit a solution with the offchain worker after the repeat interval
			MultiPhase::offchain_worker(block_plus(offchain_repeat + 1));

			// record the submitted tx,
			let tx_cache_2 = pool.read().transactions[0].clone();
			// and assume it has been processed.
			pool.try_write().unwrap().transactions.clear();

			// the OCW submitted the same solution twice since the cache was not cleared.
			assert_eq!(tx_cache_1, tx_cache_2);

			let current_block = block_plus(offchain_repeat * 2 + 2);
			// force the unsigned phase to start on the current block.
			CurrentPhase::<Runtime>::set(Phase::Unsigned((true, current_block)));

			// clear the cache and create a solution since we are on the first block of the unsigned
			// phase.
			MultiPhase::offchain_worker(current_block);
			let tx_cache_3 = pool.read().transactions[0].clone();

			// the submitted solution changes because the cache was cleared.
			assert_eq!(tx_cache_1, tx_cache_3);
		})
	}

	#[test]
	fn ocw_resubmits_after_offchain_repeat() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			const BLOCK: u64 = 25;
			let block_plus = |delta: i32| ((BLOCK as i32) + delta) as u64;
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(BLOCK);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, BLOCK)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiPhase::offchain_worker(block_plus(-1));
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiPhase::offchain_worker(BLOCK);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// attempts to resubmit the tx after the threshold has expired
			// note that we have to add 1: the semantics forbid resubmission at
			// BLOCK + offchain_repeat
			MultiPhase::offchain_worker(block_plus(1 + offchain_repeat as i32));
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn ocw_regenerates_and_resubmits_after_offchain_repeat() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			const BLOCK: u64 = 25;
			let block_plus = |delta: i32| ((BLOCK as i32) + delta) as u64;
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(BLOCK);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, BLOCK)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiPhase::offchain_worker(block_plus(-1));
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiPhase::offchain_worker(BLOCK);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// remove the cached submitted tx
			// this ensures that when the resubmit window rolls around, we're ready to regenerate
			// from scratch if necessary
			let mut call_cache = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<Call<Runtime>>(), Ok(Some(_call))));
			call_cache.clear();

			// attempts to resubmit the tx after the threshold has expired
			// note that we have to add 1: the semantics forbid resubmission at
			// BLOCK + offchain_repeat
			MultiPhase::offchain_worker(block_plus(1 + offchain_repeat as i32));
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn ocw_can_submit_to_pool() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to_with_ocw(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			// OCW must have submitted now

			let encoded = pool.read().transactions[0].clone();
			let extrinsic: Extrinsic = codec::Decode::decode(&mut &*encoded).unwrap();
			let call = extrinsic.call;
			assert!(matches!(call, OuterCall::MultiPhase(Call::submit_unsigned { .. })));
		})
	}

	#[test]
	fn ocw_solution_must_have_correct_round() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to_with_ocw(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));
			// OCW must have submitted now
			// now, before we check the call, update the round
			<crate::Round<Runtime>>::mutate(|round| *round += 1);

			let encoded = pool.read().transactions[0].clone();
			let extrinsic = Extrinsic::decode(&mut &*encoded).unwrap();
			let call = match extrinsic.call {
				OuterCall::MultiPhase(call @ Call::submit_unsigned { .. }) => call,
				_ => panic!("bad call: unexpected submission"),
			};

			// Custom(7) maps to PreDispatchChecksFailed
			let pre_dispatch_check_error =
				TransactionValidityError::Invalid(InvalidTransaction::Custom(7));
			assert_eq!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call,
				)
				.unwrap_err(),
				pre_dispatch_check_error,
			);
			assert_eq!(
				<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				pre_dispatch_check_error,
			);
		})
	}

	#[test]
	fn trim_assignments_length_does_not_modify_when_short_enough() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);

			// given
			let TrimHelpers { mut assignments, encoded_size_of, .. } = trim_helpers();
			let solution = SolutionOf::<Runtime>::try_from(assignments.as_slice()).unwrap();
			let encoded_len = solution.encoded_size() as u32;
			let solution_clone = solution.clone();

			// when
			MultiPhase::trim_assignments_length(encoded_len, &mut assignments, encoded_size_of)
				.unwrap();

			// then
			let solution = SolutionOf::<Runtime>::try_from(assignments.as_slice()).unwrap();
			assert_eq!(solution, solution_clone);
		});
	}

	#[test]
	fn trim_assignments_length_modifies_when_too_long() {
		ExtBuilder::default().build().execute_with(|| {
			roll_to(25);

			// given
			let TrimHelpers { mut assignments, encoded_size_of, .. } = trim_helpers();
			let solution = SolutionOf::<Runtime>::try_from(assignments.as_slice()).unwrap();
			let encoded_len = solution.encoded_size();
			let solution_clone = solution.clone();

			// when
			MultiPhase::trim_assignments_length(
				encoded_len as u32 - 1,
				&mut assignments,
				encoded_size_of,
			)
			.unwrap();

			// then
			let solution = SolutionOf::<Runtime>::try_from(assignments.as_slice()).unwrap();
			assert_ne!(solution, solution_clone);
			assert!(solution.encoded_size() < encoded_len);
		});
	}

	#[test]
	fn trim_assignments_length_trims_lowest_stake() {
		ExtBuilder::default().build().execute_with(|| {
			roll_to(25);

			// given
			let TrimHelpers { voters, mut assignments, encoded_size_of, voter_index } =
				trim_helpers();
			let solution = SolutionOf::<Runtime>::try_from(assignments.as_slice()).unwrap();
			let encoded_len = solution.encoded_size() as u32;
			let count = assignments.len();
			let min_stake_voter = voters
				.iter()
				.map(|(id, weight, _)| (weight, id))
				.min()
				.and_then(|(_, id)| voter_index(id))
				.unwrap();

			// when
			MultiPhase::trim_assignments_length(encoded_len - 1, &mut assignments, encoded_size_of)
				.unwrap();

			// then
			assert_eq!(assignments.len(), count - 1, "we must have removed exactly one assignment");
			assert!(
				assignments.iter().all(|IndexAssignment { who, .. }| *who != min_stake_voter),
				"min_stake_voter must no longer be in the set of voters",
			);
		});
	}

	#[test]
	fn trim_assignments_length_wont_panic() {
		// we shan't panic if assignments are initially empty.
		ExtBuilder::default().build_and_execute(|| {
			let encoded_size_of = Box::new(|assignments: &[IndexAssignmentOf<Runtime>]| {
				SolutionOf::<Runtime>::try_from(assignments).map(|solution| solution.encoded_size())
			});

			let mut assignments = vec![];

			// since we have 16 fields, we need to store the length fields of 16 vecs, thus 16 bytes
			// minimum.
			let min_solution_size = encoded_size_of(&assignments).unwrap();
			assert_eq!(min_solution_size, SolutionOf::<Runtime>::LIMIT);

			// all of this should not panic.
			MultiPhase::trim_assignments_length(0, &mut assignments, encoded_size_of.clone())
				.unwrap();
			MultiPhase::trim_assignments_length(1, &mut assignments, encoded_size_of.clone())
				.unwrap();
			MultiPhase::trim_assignments_length(
				min_solution_size as u32,
				&mut assignments,
				encoded_size_of,
			)
			.unwrap();
		});

		// or when we trim it to zero.
		ExtBuilder::default().build_and_execute(|| {
			// we need snapshot for `trim_helpers` to work.
			roll_to(25);
			let TrimHelpers { mut assignments, encoded_size_of, .. } = trim_helpers();
			assert!(assignments.len() > 0);

			// trim to min solution size.
			let min_solution_size = SolutionOf::<Runtime>::LIMIT as u32;
			MultiPhase::trim_assignments_length(
				min_solution_size,
				&mut assignments,
				encoded_size_of,
			)
			.unwrap();
			assert_eq!(assignments.len(), 0);
		});
	}

	// all the other solution-generation functions end up delegating to `mine_solution`, so if we
	// demonstrate that `mine_solution` solutions are all trimmed to an acceptable length, then
	// we know that higher-level functions will all also have short-enough solutions.
	#[test]
	fn mine_solution_solutions_always_within_acceptable_length() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);

			// how long would the default solution be?
			let solution = MultiPhase::mine_solution::<<Runtime as Config>::Solver>().unwrap();
			let max_length = <Runtime as Config>::MinerMaxLength::get();
			let solution_size = solution.0.solution.encoded_size();
			assert!(solution_size <= max_length as usize);

			// now set the max size to less than the actual size and regenerate
			<Runtime as Config>::MinerMaxLength::set(solution_size as u32 - 1);
			let solution = MultiPhase::mine_solution::<<Runtime as Config>::Solver>().unwrap();
			let max_length = <Runtime as Config>::MinerMaxLength::get();
			let solution_size = solution.0.solution.encoded_size();
			assert!(solution_size <= max_length as usize);
		});
	}
}
