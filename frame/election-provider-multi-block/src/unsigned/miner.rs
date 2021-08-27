// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use crate::{helpers, log, types::*, verifier};
use codec::{Decode, Encode};
use frame_election_provider_support::ExtendedBalance;
use frame_support::{dispatch::Weight, traits::Get};
use sp_runtime::{
	offchain::storage::{MutateStorageError, StorageValueRef},
	traits::SaturatedConversion,
};

// TODO: unify naming: everything should be
// xxx_page: singular
// paged_xxx: plural

#[derive(Debug, Eq, PartialEq)]
pub enum MinerError {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable,
	/// Submitting a transaction to the pool failed.
	PoolSubmissionFailed,
	/// The snapshot-independent checks failed for the mined solution.
	SnapshotIndependentChecksFailed(sp_runtime::DispatchError),
	/// unsigned-specific checks failed.
	UnsignedChecksFailed(sp_runtime::DispatchError),
	/// The solution generated from the miner is not feasible.
	Feasibility(verifier::FeasibilityError),
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
	/// Some page index has been invalid.
	InvalidPage,
}

impl From<sp_npos_elections::Error> for MinerError {
	fn from(e: sp_npos_elections::Error) -> Self {
		MinerError::NposElections(e)
	}
}

impl From<crate::verifier::FeasibilityError> for MinerError {
	fn from(e: verifier::FeasibilityError) -> Self {
		MinerError::Feasibility(e)
	}
}

/// The [`IndexAssignment`][sp_npos_elections::IndexAssignment] type specialized for a particular
/// runtime `T`.
pub type IndexAssignmentOf<T> = sp_npos_elections::IndexAssignmentOf<SolutionOf<T>>;

/// A base miner that is only capable of mining a new solution and checking it against the state of
/// this pallet for feasibility, and trimming its length/weight.
///
/// The type of solver is hardcoded for now, `seq-phragmen`. TODO: turn it a configurable,
/// extensible trait.
pub struct BaseMiner<T: super::Config>(sp_std::marker::PhantomData<T>);

impl<T: super::Config> BaseMiner<T> {
	/// Mine a new npos solution, with the given number of pages.
	pub fn mine_solution(pages: PageIndex) -> Result<PagedRawSolution<SolutionOf<T>>, MinerError> {
		// read the appropriate snapshot pages.
		let desired_targets =
			crate::Snapshot::<T>::desired_targets().ok_or(MinerError::SnapshotUnAvailable)?;
		let targets = crate::Snapshot::<T>::targets().ok_or(MinerError::SnapshotUnAvailable)?;
		let voter_pages_range =
			(crate::Pallet::<T>::msp()..crate::Pallet::<T>::msp()).take(pages.into());
		let voter_pages = voter_pages_range
			.map(|p| crate::Snapshot::<T>::voters(p).ok_or(MinerError::SnapshotUnAvailable))
			.collect::<Result<Vec<_>, _>>()?;

		// we also build this closure early, so we can let `targets` be consumed.
		let voter_page_fn = helpers::generate_voter_page_fn::<T>(&voter_pages);
		let target_index_fn = helpers::target_index_fn::<T>(&targets);

		// now flatten the voters, ready to be used as if pagination did not existed.
		let voters = voter_pages.iter().flatten().cloned().collect::<Vec<_>>();

		let ElectionResult { winners, assignments } =
			sp_npos_elections::seq_phragmen::<_, SolutionAccuracyOf<T>>(
				desired_targets as usize,
				targets.clone(),
				voters.clone(),
				None,
			)
			.map_err::<MinerError, _>(Into::into)?;

		// compute score from the overall solution before dealing with pages in any way.
		let score = {
			use crate::helpers;
			use sp_npos_elections::{
				assignment_ratio_to_staked_normalized, to_supports, to_without_backing,
				EvaluateSupport,
			};
			// These closures are of no use in the rest of these code, since they only deal with the
			// overall list of voters.
			let cache = helpers::generate_voter_cache::<T>(&voters);
			let stake_of = helpers::stake_of_fn::<T>(&voters, &cache);
			let staked = assignment_ratio_to_staked_normalized(assignments.clone(), &stake_of)
				.map_err::<MinerError, _>(Into::into)?;
			let winners = to_without_backing(winners);
			to_supports(&winners, &staked).map_err::<MinerError, _>(Into::into)?.evaluate()
		};

		// split the assignments into different pages.
		let mut paged_assignments: Vec<Vec<AssignmentOf<T>>> =
			Vec::with_capacity(T::Pages::get() as usize);
		paged_assignments.resize(T::Pages::get() as usize, vec![]);
		for assignment in assignments {
			let page = voter_page_fn(&assignment.who).ok_or(MinerError::InvalidPage)?;
			let mut assignment_page =
				paged_assignments.get_mut(page as usize).ok_or(MinerError::InvalidPage)?;
			assignment_page.push(assignment);
		}

		// convert each page to a compact struct
		let mut solution_pages: Vec<SolutionOf<T>> = paged_assignments
			.into_iter()
			.enumerate()
			.map(|(page_index, assignment_page)| {
				// get the page of the snapshot that corresponds to this page of the assignments.
				let page: PageIndex = page_index.saturated_into();
				let voter_snapshot_page =
					voter_pages.get(page_index).ok_or(MinerError::SnapshotUnAvailable)?;

				let voter_index_fn = {
					let cache = helpers::generate_voter_cache::<T>(&voter_snapshot_page);
					helpers::voter_index_fn_owned::<T>(cache)
				};
				<SolutionOf<T>>::from_assignment(
					&assignment_page,
					&voter_index_fn,
					&target_index_fn,
				)
				.map_err::<MinerError, _>(Into::into)
			})
			.collect::<Result<Vec<_>, _>>()?;

		// finally, get the round, and pack everything.
		let round = crate::Pallet::<T>::round();

		log!(
			debug,
			"mined a solution with score {:?} and size {} bytes",
			score,
			solution_pages.using_encoded(|b| b.len())
		);

		Ok(PagedRawSolution { round, score, solution_pages })
	}

	/// Mine a new solution. Performs the feasibility checks on it as well.
	pub fn mine_checked_solution(
		pages: PageIndex,
	) -> Result<PagedRawSolution<SolutionOf<T>>, MinerError> {
		let paged_solution = Self::mine_solution(pages)?;
		let _ = Self::full_checks(&paged_solution, "mined")?;
		Ok(paged_solution)
	}

	/// Perform all checks:
	///
	/// 1. feasibility check.
	/// 2. snapshot-independent checks.
	pub fn full_checks(
		paged_solution: &PagedRawSolution<SolutionOf<T>>,
		solution_type: &str,
	) -> Result<(), MinerError> {
		crate::Pallet::<T>::snapshot_independent_checks(paged_solution)
			.map_err(|de| MinerError::SnapshotIndependentChecksFailed(de))
			.and_then(|_| Self::check_feasibility(&paged_solution, solution_type))
	}

	/// perform the feasibility check on all pages of a solution, returning `Ok(())` if all good and
	/// the corresponding error otherwise.
	pub fn check_feasibility(
		paged_solution: &PagedRawSolution<SolutionOf<T>>,
		solution_type: &str,
	) -> Result<(), MinerError> {
		// check every solution page for feasibility.
		let _ = paged_solution
			.solution_pages
			.iter()
			.enumerate()
			.map(|(page_index, page_solution)| {
				<T::Verifier as verifier::Verifier>::feasibility_check_page(
					page_solution.clone(),
					page_index as PageIndex,
				)
			})
			.collect::<Result<Vec<_>, _>>()
			.map_err(|err| {
				log!(
					debug,
					"feasibility check failed for {} solution at: {:?}",
					solution_type,
					err
				);
				err
			})?;

		Ok(())
	}

	/// Greedily reduce the size of the solution to fit into the block w.r.t. weight.
	///
	/// The weight of the solution is foremost a function of the number of voters (i.e.
	/// `assignments.len()`). Aside from this, the other components of the weight are invariant.
	/// The number of winners shall not be changed (otherwise the solution is invalid) and the
	/// `ElectionSize` is merely a representation of the total number of stakers.
	///
	/// Thus, we reside to stripping away some voters from the `assignments`.
	///
	/// Note that the solution is already computed, and the winners are elected based on the
	/// merit of the entire stake in the system. Nonetheless, some of the voters will be removed
	/// further down the line.
	///
	/// Indeed, the score must be computed **after** this step. If this step reduces the score
	/// too much or remove a winner, then the solution must be discarded **after** this step.
	pub fn trim_assignments_weight(
		desired_targets: u32,
		size: SolutionOrSnapshotSize,
		max_weight: Weight,
		assignments: &mut Vec<IndexAssignmentOf<T>>,
	) {
		let maximum_allowed_voters = Self::maximum_voter_for_weight::<
			<T as super::Config>::WeightInfo,
		>(desired_targets, size, max_weight);
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
	/// Note that this solution is already computed, and winners are elected based on the merit
	/// of the total stake in the system. Nevertheless, some of the voters may be removed here.
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
	) -> Result<(), MinerError> {
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
	fn maximum_voter_for_weight<W: super::WeightInfo>(
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
			use sp_std::cmp::Ordering;
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

		// Time to finish. We might have reduced less than expected due to rounding error.
		// Increase one last time if we have any room left, the reduce until we are sure we are
		// below limit.
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
}

/// A miner that is suited to work inside offchain worker environment.
pub(crate) struct OffchainWorkerMiner<T: super::Config>(sp_std::marker::PhantomData<T>);
impl<T: super::Config> OffchainWorkerMiner<T> {
	/// Storage key used to store the offchain worker running status.
	pub(crate) const OFFCHAIN_LOCK: &'static [u8] = b"parity/multi-block-unsigned-election/lock";
	/// Storage key used to store the last block number at which offchain worker ran.
	const OFFCHAIN_LAST_BLOCK: &'static [u8] = b"parity/multi-block-unsigned-election";
	/// Storage key used to cache the solution `call`.
	const OFFCHAIN_CACHED_CALL: &'static [u8] = b"parity/multi-block-unsigned-election/call";

	/// Get a checked solution from the base miner, ensure unsigned-specific checks also pass, then
	/// return an submittable call.
	fn mine_checked_call() -> Result<super::Call<T>, MinerError> {
		let iters = Self::get_balancing_iters();
		let witness = todo!();
		let paged_solution = BaseMiner::<T>::mine_checked_solution(1)?;
		let _ = super::Pallet::<T>::unsigned_specific_checks(&paged_solution)
			.map_err(|de| MinerError::UnsignedChecksFailed(de))?;

		let call: super::Call<T> =
			super::Call::<T>::submit_unsigned(Box::new(paged_solution), witness).into();

		Ok(call)
	}

	/// Mine a new checked solution, cache it, and submit it back to the chain as an unsigned
	/// transaction.
	pub fn mine_check_save_submit() -> Result<(), MinerError> {
		log!(debug, "miner attempting to compute an unsigned solution.");
		let call = Self::mine_checked_call()?;
		Self::save_solution(&call)?;
		Self::submit_call(call)
	}

	fn submit_call(call: super::Call<T>) -> Result<(), MinerError> {
		log!(debug, "miner submitting a solution as an unsigned transaction");
		frame_system::offchain::SubmitTransaction::<T, super::Call<T>>::submit_unsigned_transaction(
			call.into(),
		)
		.map_err(|_| MinerError::PoolSubmissionFailed)
	}

	/// Get a random number of iterations to run the balancing in the OCW.
	///
	/// Uses the offchain seed to generate a random number, maxed with
	/// [`Config::MinerMaxIterations`].
	pub fn get_balancing_iters() -> usize {
		use sp_runtime::traits::TrailingZeroInput;
		match T::MinerMaxIterations::get() {
			0 => 0,
			max @ _ => {
				let seed = sp_io::offchain::random_seed();
				let random = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
					.expect("input is padded with zeroes; qed") %
					max.saturating_add(1);
				random as usize
			},
		}
	}

	/// Attempt to restore a solution from cache. Otherwise, compute it fresh. Either way,
	/// submit if our call's score is greater than that of the cached solution.
	pub fn restore_or_compute_then_maybe_submit() -> Result<(), MinerError> {
		log!(debug, "miner attempting to restore or compute an unsigned solution.");

		let call = Self::restore_solution()
			.and_then(|call| {
				// ensure the cached call is still current before submitting
				if let super::Call::submit_unsigned(solution, _) = &call {
					// prevent errors arising from state changes in a forkful chain
					BaseMiner::<T>::full_checks(solution, "restored")?;
					Ok(call)
				} else {
					Err(MinerError::SolutionCallInvalid)
				}
			})
			.or_else::<MinerError, _>(|error| {
				log!(debug, "restoring solution failed due to {:?}", error);
				match error {
					// TODO: after we have a snapshot check we can change this. If the snapshot has
					// not changed, then we won't need to re-check feasibility.
					MinerError::NoStoredSolution => {
						log!(trace, "mining a new solution.");
						// if not present or cache invalidated due to feasibility, regenerate.
						// note that failing `Feasibility` can only mean that the solution was
						// computed over a snapshot that has changed due to a fork.
						let call = Self::mine_checked_call()?;
						Self::save_solution(&call)?;
						Ok(call)
					},
					MinerError::Feasibility(_) |
					MinerError::SnapshotIndependentChecksFailed(_) |
					MinerError::UnsignedChecksFailed(_) => {
						log!(trace, "wiping infeasible solution, but recovering from it.");
						// kill the infeasible solution, hopefully in the next runs (whenever
						// they may be) we mine a new one.
						Self::kill_ocw_solution();
						Self::clear_offchain_repeat_frequency();
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

	/// Checks if an execution of the offchain worker is permitted at the given block number, or
	/// not.
	///
	/// This makes sure that
	/// 1. we don't run on previous blocks in case of a re-org
	/// 2. we don't run twice within a window of length `T::OffchainRepeat`.
	///
	/// Returns `Ok(())` if offchain worker limit is respected, `Err(reason)` otherwise. If
	/// `Ok()` is returned, `now` is written in storage and will be used in further calls as the
	/// baseline.
	pub fn ensure_offchain_repeat_frequency(now: T::BlockNumber) -> Result<(), MinerError> {
		let threshold = T::OffchainRepeat::get();
		let last_block = StorageValueRef::persistent(&Self::OFFCHAIN_LAST_BLOCK);

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
						// value doesn't exists. Probably this node just booted up. Write, and
						// run
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

	/// Save a given call into OCW storage.
	fn save_solution(call: &super::Call<T>) -> Result<(), MinerError> {
		log!(debug, "saving a call to the offchain storage.");
		let storage = StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL);
		match storage.mutate::<_, (), _>(|_| Ok(call.clone())) {
			Ok(_) => Ok(()),
			Err(MutateStorageError::ConcurrentModification(_)) =>
				Err(MinerError::FailedToStoreSolution),
			Err(MutateStorageError::ValueFunctionFailed(_)) => {
				// this branch should be unreachable according to the definition of
				// `StorageValueRef::mutate`: that function should only ever `Err` if the closure we
				// pass it returns an error. however, for safety in case the definition changes, we
				// do not optimize the branch away or panic.
				Err(MinerError::FailedToStoreSolution)
			},
		}
	}

	/// Get a saved solution from OCW storage if it exists.
	fn restore_solution() -> Result<super::Call<T>, MinerError> {
		StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL)
			.get()
			.ok()
			.flatten()
			.ok_or(MinerError::NoStoredSolution)
	}

	/// Clear a saved solution from OCW storage.
	fn kill_ocw_solution() {
		log!(debug, "clearing offchain call cache storage.");
		let mut storage = StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL);
		storage.clear();
	}

	/// Clear the offchain repeat storage.
	///
	/// After calling this, the next offchain worker is guaranteed to work, with respect to the
	/// frequency repeat.
	fn clear_offchain_repeat_frequency() {
		let mut last_block = StorageValueRef::persistent(&Self::OFFCHAIN_LAST_BLOCK);
		last_block.clear();
	}
}

#[cfg(test)]
mod max_weight_binary_search {
	#![allow(unused_variables)]
	use frame_support::dispatch::Weight;

	use crate::{mock::Runtime, types::SolutionOrSnapshotSize, unsigned::miner::BaseMiner};

	struct TestWeight;
	impl crate::unsigned::WeightInfo for TestWeight {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
			(0 * v + 0 * t + 1000 * a + 0 * d) as Weight
		}
	}

	#[test]
	fn find_max_voter_binary_search_works() {
		let w = SolutionOrSnapshotSize { voters: 10, targets: 0 };

		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2990), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2999), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3000), 3);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 3);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 5500), 5);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 7777), 7);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 9999), 9);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 10_000), 10);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 10_999), 10);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 11_000), 10);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 22_000), 10);

		let w = SolutionOrSnapshotSize { voters: 1, targets: 0 };

		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1990), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 1);

		let w = SolutionOrSnapshotSize { voters: 2, targets: 0 };

		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 0), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 999), 0);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1000), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1001), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 1999), 1);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2000), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2001), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 2010), 2);
		assert_eq!(BaseMiner::<Runtime>::maximum_voter_for_weight::<TestWeight>(0, w, 3333), 2);
	}
}
