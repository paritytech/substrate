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

//! The unsigned phase implementation.

use crate::*;
use frame_support::dispatch::DispatchResult;
use frame_system::offchain::SubmitTransaction;
use sp_npos_elections::{
	seq_phragmen, CompactSolution, ElectionResult, assignment_ratio_to_staked_normalized,
	assignment_staked_to_ratio_normalized,
};
use sp_runtime::{offchain::storage::StorageValueRef, traits::TrailingZeroInput};
use sp_std::cmp::Ordering;

/// Storage key used to store the persistent offchain worker status.
pub(crate) const OFFCHAIN_HEAD_DB: &[u8] = b"parity/multi-phase-unsigned-election";

/// The repeat threshold of the offchain worker. This means we won't run the offchain worker twice
/// within a window of 5 blocks.
pub(crate) const OFFCHAIN_REPEAT: u32 = 5;

#[derive(Debug, Eq, PartialEq)]
pub enum MinerError {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	PoolSubmissionFailed,
	/// The pre-dispatch checks failed for the mined solution.
	PreDispatchChecksFailed,
	/// The solution generated from the miner is not feasible.
	Feasibility(FeasibilityError),
}

impl From<sp_npos_elections::Error> for MinerError {
	fn from(e: sp_npos_elections::Error) -> Self {
		MinerError::NposElections(e)
	}
}

impl From<FeasibilityError> for MinerError {
	fn from(e: FeasibilityError) -> Self {
		MinerError::Feasibility(e)
	}
}

impl<T: Config> Pallet<T> {
	/// Mine a new solution, and submit it back to the chain as an unsigned transaction.
	pub fn mine_check_and_submit() -> Result<(), MinerError> {
		let iters = Self::get_balancing_iters();
		// get the solution, with a load of checks to ensure if submitted, IT IS ABSOLUTELY VALID.
		let (raw_solution, witness) = Self::mine_and_check(iters)?;
		let score = raw_solution.score.clone();

		let call: <T as frame_system::offchain::SendTransactionTypes<Call<T>>>::OverarchingCall =
			Call::submit_unsigned(raw_solution, witness).into();
		log!(
			info,
			"mined a solution with score {:?} and size {}",
			score,
			call.using_encoded(|b| b.len())
		);

		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call)
			.map_err(|_| MinerError::PoolSubmissionFailed)
	}

	/// Mine a new npos solution, with all the relevant checks to make sure that it will be accepted
	/// to the chain.
	///
	/// If you want an unchecked solution, use [`Pallet::mine_solution`].
	/// If you want a checked solution and submit it at the same time, use
	/// [`Pallet::mine_check_and_submit`].
	pub fn mine_and_check(
		iters: usize,
	) -> Result<(RawSolution<CompactOf<T>>, SolutionOrSnapshotSize), MinerError> {
		let (raw_solution, witness) = Self::mine_solution(iters)?;

		// ensure that this will pass the pre-dispatch checks
		Self::unsigned_pre_dispatch_checks(&raw_solution).map_err(|e| {
			log!(warn, "pre-dispatch-checks failed for mined solution: {:?}", e);
			MinerError::PreDispatchChecksFailed
		})?;

		// ensure that this is a feasible solution
		let _ = Self::feasibility_check(raw_solution.clone(), ElectionCompute::Unsigned).map_err(
			|e| {
				log!(warn, "feasibility-check failed for mined solution: {:?}", e);
				MinerError::from(e)
			},
		)?;

		Ok((raw_solution, witness))
	}

	/// Mine a new npos solution.
	pub fn mine_solution(
		iters: usize,
	) -> Result<(RawSolution<CompactOf<T>>, SolutionOrSnapshotSize), MinerError> {
		let RoundSnapshot { voters, targets } =
			Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
		let desired_targets = Self::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;

		seq_phragmen::<_, CompactAccuracyOf<T>>(
			desired_targets as usize,
			targets,
			voters,
			Some((iters, 0)),
		)
		.map_err(Into::into)
		.and_then(Self::prepare_election_result)
	}

	/// Convert a raw solution from [`sp_npos_elections::ElectionResult`] to [`RawSolution`], which
	/// is ready to be submitted to the chain.
	///
	/// Will always reduce the solution as well.
	pub fn prepare_election_result(
		election_result: ElectionResult<T::AccountId, CompactAccuracyOf<T>>,
	) -> Result<(RawSolution<CompactOf<T>>, SolutionOrSnapshotSize), MinerError> {
		// NOTE: This code path is generally not optimized as it is run offchain. Could use some at
		// some point though.

		// storage items. Note: we have already read this from storage, they must be in cache.
		let RoundSnapshot { voters, targets } =
			Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
		let desired_targets = Self::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;

		// closures.
		let cache = helpers::generate_voter_cache::<T>(&voters);
		let voter_index = helpers::voter_index_fn::<T>(&cache);
		let target_index = helpers::target_index_fn::<T>(&targets);
		let voter_at = helpers::voter_at_fn::<T>(&voters);
		let target_at = helpers::target_at_fn::<T>(&targets);
		let stake_of = helpers::stake_of_fn::<T>(&voters, &cache);

		let ElectionResult { assignments, winners } = election_result;

		// convert to staked and reduce.
		let mut staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)
			.map_err::<MinerError, _>(Into::into)?;
		sp_npos_elections::reduce(&mut staked);

		// convert back to ration and make compact.
		let ratio = assignment_staked_to_ratio_normalized(staked)?;
		let compact = <CompactOf<T>>::from_assignment(ratio, &voter_index, &target_index)?;

		let size =
			SolutionOrSnapshotSize { voters: voters.len() as u32, targets: targets.len() as u32 };
		let maximum_allowed_voters = Self::maximum_voter_for_weight::<T::WeightInfo>(
			desired_targets,
			size,
			T::MinerMaxWeight::get(),
		);

		log!(
			debug,
			"initial solution voters = {}, snapshot = {:?}, maximum_allowed(capped) = {}",
			compact.voter_count(),
			size,
			maximum_allowed_voters,
		);

		// trim weight.
		let compact = Self::trim_compact(maximum_allowed_voters, compact, &voter_index)?;

		// re-calc score.
		let winners = sp_npos_elections::to_without_backing(winners);
		let score = compact.clone().score(&winners, stake_of, voter_at, target_at)?;

		let round = Self::round();
		Ok((RawSolution { compact, score, round }, size))
	}

	/// Get a random number of iterations to run the balancing in the OCW.
	///
	/// Uses the offchain seed to generate a random number, maxed with
	/// [`Config::MinerMaxIterations`].
	pub fn get_balancing_iters() -> usize {
		match T::MinerMaxIterations::get() {
			0 => 0,
			max @ _ => {
				let seed = sp_io::offchain::random_seed();
				let random = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
					.expect("input is padded with zeroes; qed")
					% max.saturating_add(1);
				random as usize
			}
		}
	}

	/// Greedily reduce the size of the a solution to fit into the block, w.r.t. weight.
	///
	/// The weight of the solution is foremost a function of the number of voters (i.e.
	/// `compact.len()`). Aside from this, the other components of the weight are invariant. The
	/// number of winners shall not be changed (otherwise the solution is invalid) and the
	/// `ElectionSize` is merely a representation of the total number of stakers.
	///
	/// Thus, we reside to stripping away some voters. This means only changing the `compact`
	/// struct.
	///
	/// Note that the solution is already computed, and the winners are elected based on the merit
	/// of the entire stake in the system. Nonetheless, some of the voters will be removed further
	/// down the line.
	///
	/// Indeed, the score must be computed **after** this step. If this step reduces the score too
	/// much or remove a winner, then the solution must be discarded **after** this step.
	pub fn trim_compact<FN>(
		maximum_allowed_voters: u32,
		mut compact: CompactOf<T>,
		voter_index: FN,
	) -> Result<CompactOf<T>, MinerError>
	where
		for<'r> FN: Fn(&'r T::AccountId) -> Option<CompactVoterIndexOf<T>>,
	{
		match compact.voter_count().checked_sub(maximum_allowed_voters as usize) {
			Some(to_remove) if to_remove > 0 => {
				// grab all voters and sort them by least stake.
				let RoundSnapshot { voters, .. } =
					Self::snapshot().ok_or(MinerError::SnapshotUnAvailable)?;
				let mut voters_sorted = voters
					.into_iter()
					.map(|(who, stake, _)| (who.clone(), stake))
					.collect::<Vec<_>>();
				voters_sorted.sort_by_key(|(_, y)| *y);

				// start removing from the least stake. Iterate until we know enough have been
				// removed.
				let mut removed = 0;
				for (maybe_index, _stake) in
					voters_sorted.iter().map(|(who, stake)| (voter_index(&who), stake))
				{
					let index = maybe_index.ok_or(MinerError::SnapshotUnAvailable)?;
					if compact.remove_voter(index) {
						removed += 1
					}

					if removed >= to_remove {
						break;
					}
				}

				log!(debug, "removed {} voter to meet the max weight limit.", to_remove);
				Ok(compact)
			}
			_ => {
				// nada, return as-is
				log!(debug, "didn't remove any voter for weight limits.");
				Ok(compact)
			}
		}
	}

	/// Find the maximum `len` that a compact can have in order to fit into the block weight.
	///
	/// This only returns a value between zero and `size.nominators`.
	pub fn maximum_voter_for_weight<W: WeightInfo>(
		desired_winners: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
	) -> u32 {
		if size.voters < 1 {
			return size.voters;
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
				}
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
				}
				// we are out of bounds, break out of the loop.
				Err(()) => {
					break;
				}
				// we found the right value - early exit the function.
				Ok(next) => return next,
			}
			step = step / 2;
			current_weight = weight_with(voters);
		}

		// Time to finish. We might have reduced less than expected due to rounding error. Increase
		// one last time if we have any room left, the reduce until we are sure we are below limit.
		while voters + 1 <= max_voters && weight_with(voters + 1) < max_weight {
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
	/// This essentially makes sure that we don't run on previous blocks in case of a re-org, and we
	/// don't run twice within a window of length [`OFFCHAIN_REPEAT`].
	///
	/// Returns `Ok(())` if offchain worker should happen, `Err(reason)` otherwise.
	pub(crate) fn try_acquire_offchain_lock(now: T::BlockNumber) -> Result<(), &'static str> {
		let storage = StorageValueRef::persistent(&OFFCHAIN_HEAD_DB);
		let threshold = T::BlockNumber::from(OFFCHAIN_REPEAT);

		let mutate_stat =
			storage.mutate::<_, &'static str, _>(|maybe_head: Option<Option<T::BlockNumber>>| {
				match maybe_head {
					Some(Some(head)) if now < head => Err("fork."),
					Some(Some(head)) if now >= head && now <= head + threshold => {
						Err("recently executed.")
					}
					Some(Some(head)) if now > head + threshold => {
						// we can run again now. Write the new head.
						Ok(now)
					}
					_ => {
						// value doesn't exists. Probably this node just booted up. Write, and run
						Ok(now)
					}
				}
			});

		match mutate_stat {
			// all good
			Ok(Ok(_)) => Ok(()),
			// failed to write.
			Ok(Err(_)) => Err("failed to write to offchain db."),
			// fork etc.
			Err(why) => Err(why),
		}
	}

	/// Do the basics checks that MUST happen during the validation and pre-dispatch of an unsigned
	/// transaction.
	///
	/// Can optionally also be called during dispatch, if needed.
	///
	/// NOTE: Ideally, these tests should move more and more outside of this and more to the miner's
	/// code, so that we do less and less storage reads here.
	pub(crate) fn unsigned_pre_dispatch_checks(
		solution: &RawSolution<CompactOf<T>>,
	) -> DispatchResult {
		// ensure solution is timely. Don't panic yet. This is a cheap check.
		ensure!(Self::current_phase().is_unsigned_open(), Error::<T>::PreDispatchEarlySubmission);

		// ensure correct number of winners.
		ensure!(
			Self::desired_targets().unwrap_or_default()
				== solution.compact.unique_targets().len() as u32,
			Error::<T>::PreDispatchWrongWinnerCount,
		);

		// ensure score is being improved. Panic henceforth.
		ensure!(
			Self::queued_solution().map_or(true, |q: ReadySolution<_>| is_score_better::<Perbill>(
				solution.score,
				q.score,
				T::SolutionImprovementThreshold::get()
			)),
			Error::<T>::PreDispatchWeakSubmission,
		);

		Ok(())
	}
}

#[cfg(test)]
mod max_weight {
	#![allow(unused_variables)]
	use super::{mock::*, *};

	struct TestWeight;
	impl crate::weights::WeightInfo for TestWeight {
		fn on_initialize_nothing() -> Weight {
			unreachable!()
		}
		fn on_initialize_open_signed() -> Weight {
			unreachable!()
		}
		fn on_initialize_open_unsigned_with_snapshot() -> Weight {
			unreachable!()
		}
		fn elect_queued() -> Weight {
			0
		}
		fn on_initialize_open_unsigned_without_snapshot() -> Weight {
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
	use super::{
		mock::{Origin, *},
		Call, *,
	};
	use frame_support::{dispatch::Dispatchable, traits::OffchainWorker};
	use mock::Call as OuterCall;
	use frame_election_provider_support::Assignment;
	use sp_runtime::{traits::ValidateUnsigned, PerU16};

	#[test]
	fn validate_unsigned_retracts_wrong_phase() {
		ExtBuilder::default().desired_targets(0).build_and_execute(|| {
			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(solution.clone(), witness());

			// initial
			assert_eq!(MultiPhase::current_phase(), Phase::Off);
			assert!(matches!(
				<MultiPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
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
				<MultiPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
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
				<MultiPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
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

			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(solution.clone(), witness());

			// initial
			assert!(<MultiPhase as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<MultiPhase as ValidateUnsigned>::pre_dispatch(&call).is_ok());

			// set a better score
			let ready = ReadySolution { score: [10, 0, 0], ..Default::default() };
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

			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(solution.clone(), witness());
			assert_eq!(solution.compact.unique_targets().len(), 0);

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
		ExtBuilder::default().miner_tx_priority(20).desired_targets(0).build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(solution.clone(), witness());

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
	                           Module { index: 2, error: 1, message: \
	                           Some(\"PreDispatchWrongWinnerCount\") }")]
	fn unfeasible_solution_panics() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// This is in itself an invalid BS solution.
			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(solution.clone(), witness());
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
			let solution = RawSolution::<TestCompact> { score: [5, 0, 0], ..Default::default() };

			let mut correct_witness = witness();
			correct_witness.voters += 1;
			correct_witness.targets -= 1;
			let call = Call::submit_unsigned(solution.clone(), correct_witness);
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
			let (solution, witness) = MultiPhase::mine_solution(2).unwrap();

			// ensure this solution is valid.
			assert!(MultiPhase::queued_solution().is_none());
			assert_ok!(MultiPhase::submit_unsigned(Origin::none(), solution, witness));
			assert!(MultiPhase::queued_solution().is_some());
		})
	}

	#[test]
	fn miner_trims_weight() {
		ExtBuilder::default().miner_weight(100).mock_weight_info(true).build_and_execute(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			let (solution, witness) = MultiPhase::mine_solution(2).unwrap();
			let solution_weight = <Runtime as Config>::WeightInfo::submit_unsigned(
				witness.voters,
				witness.targets,
				solution.compact.voter_count() as u32,
				solution.compact.unique_targets().len() as u32,
			);
			// default solution will have 5 edges (5 * 5 + 10)
			assert_eq!(solution_weight, 35);
			assert_eq!(solution.compact.voter_count(), 5);

			// now reduce the max weight
			<MinerMaxWeight>::set(25);

			let (solution, witness) = MultiPhase::mine_solution(2).unwrap();
			let solution_weight = <Runtime as Config>::WeightInfo::submit_unsigned(
				witness.voters,
				witness.targets,
				solution.compact.voter_count() as u32,
				solution.compact.unique_targets().len() as u32,
			);
			// default solution will have 5 edges (5 * 5 + 10)
			assert_eq!(solution_weight, 25);
			assert_eq!(solution.compact.voter_count(), 3);
		})
	}

	#[test]
	fn miner_will_not_submit_if_not_enough_winners() {
		let (mut ext, _) = ExtBuilder::default().desired_targets(8).build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			assert_eq!(
				MultiPhase::mine_check_and_submit().unwrap_err(),
				MinerError::PreDispatchChecksFailed,
			);
		})
	}

	#[test]
	fn unsigned_per_dispatch_checks_can_only_submit_threshold_better() {
		ExtBuilder::default()
			.desired_targets(1)
			.add_voter(7, 2, vec![10])
			.add_voter(8, 5, vec![10])
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
				assert_ok!(MultiPhase::submit_unsigned(Origin::none(), solution, witness));
				assert_eq!(MultiPhase::queued_solution().unwrap().score[0], 10);

				// trial 1: a solution who's score is only 2, i.e. 20% better in the first element.
				let result = ElectionResult {
					winners: vec![(10, 12)],
					assignments: vec![
						Assignment { who: 10, distribution: vec![(10, PerU16::one())] },
						Assignment {
							who: 7,
							// note: this percent doesn't even matter, in compact it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let (solution, _) = MultiPhase::prepare_election_result(result).unwrap();
				// 12 is not 50% more than 10
				assert_eq!(solution.score[0], 12);
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
							// note: this percent doesn't even matter, in compact it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let (solution, witness) = MultiPhase::prepare_election_result(result).unwrap();
				assert_eq!(solution.score[0], 17);

				// and it is fine
				assert_ok!(MultiPhase::unsigned_pre_dispatch_checks(&solution));
				assert_ok!(MultiPhase::submit_unsigned(Origin::none(), solution, witness));
			})
	}

	#[test]
	fn ocw_check_prevent_duplicate() {
		let (mut ext, _) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert!(MultiPhase::current_phase().is_unsigned());

			// first execution -- okay.
			assert!(MultiPhase::try_acquire_offchain_lock(25).is_ok());

			// next block: rejected.
			assert!(MultiPhase::try_acquire_offchain_lock(26).is_err());

			// allowed after `OFFCHAIN_REPEAT`
			assert!(MultiPhase::try_acquire_offchain_lock((26 + OFFCHAIN_REPEAT).into()).is_ok());

			// a fork like situation: re-execute last 3.
			assert!(
				MultiPhase::try_acquire_offchain_lock((26 + OFFCHAIN_REPEAT - 3).into()).is_err()
			);
			assert!(
				MultiPhase::try_acquire_offchain_lock((26 + OFFCHAIN_REPEAT - 2).into()).is_err()
			);
			assert!(
				MultiPhase::try_acquire_offchain_lock((26 + OFFCHAIN_REPEAT - 1).into()).is_err()
			);
		})
	}

	#[test]
	fn ocw_only_runs_when_unsigned_open_now() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert_eq!(MultiPhase::current_phase(), Phase::Unsigned((true, 25)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_HEAD_DB);

			MultiPhase::offchain_worker(24);
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			MultiPhase::offchain_worker(26);
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// submits!
			MultiPhase::offchain_worker(25);
			assert!(!pool.read().transactions.len().is_zero());
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
			let extrinsic: Extrinsic = Decode::decode(&mut &*encoded).unwrap();
			let call = extrinsic.call;
			assert!(matches!(call, OuterCall::MultiPhase(Call::submit_unsigned(_, _))));
		})
	}
}
