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

use super::{Call, Config, Pallet, WeightInfo};
use crate::{
	helpers,
	types::*,
	verifier::{self},
};
use codec::Encode;
use frame_election_provider_support::{ExtendedBalance, NposSolver, Support, VoteWeight};
use frame_support::{traits::Get, BoundedVec};
use sp_runtime::{
	offchain::storage::{MutateStorageError, StorageValueRef},
	traits::{SaturatedConversion, Saturating, Zero},
};
use sp_std::prelude::*;

// TODO: fuzzer for the miner

/// The type of the snapshot.
///
/// Used to express errors.
#[derive(Debug, Eq, PartialEq)]
pub enum SnapshotType {
	/// Voters at the given page missing.
	Voters(PageIndex),
	/// Targets missing.
	Targets,
	/// Metadata missing.
	Metadata,
	// Desired targets missing.
	DesiredTargets,
}

/// Error type of the pallet's [`crate::Config::Solver`].
pub type OffchainSolverErrorOf<T> = <<T as Config>::OffchainSolver as NposSolver>::Error;

/// The errors related to the [`BaseMiner`].
#[derive(
	frame_support::DebugNoBound, frame_support::EqNoBound, frame_support::PartialEqNoBound,
)]
pub enum MinerError<T: Config> {
	/// An internal error in the NPoS elections crate.
	NposElections(sp_npos_elections::Error),
	/// An internal error in the generic solver.
	Solver(OffchainSolverErrorOf<T>),
	/// Snapshot data was unavailable unexpectedly.
	SnapshotUnAvailable(SnapshotType),
	/// The snapshot-independent checks failed for the mined solution.
	SnapshotIndependentChecks(crate::Error<T>),
	/// The solution generated from the miner is not feasible.
	Feasibility(verifier::FeasibilityError),
	/// Some page index has been invalid.
	InvalidPage,
	/// Too many winners were removed during trimming.
	TooManyWinnersRemoved,
	/// A defensive error has occurred.
	Defensive(&'static str),
}

impl<T: Config> From<sp_npos_elections::Error> for MinerError<T> {
	fn from(e: sp_npos_elections::Error) -> Self {
		MinerError::NposElections(e)
	}
}

impl<T: Config> From<crate::verifier::FeasibilityError> for MinerError<T> {
	fn from(e: verifier::FeasibilityError) -> Self {
		MinerError::Feasibility(e)
	}
}

/// The errors related to the [`OffchainMiner`].
#[derive(
	frame_support::DebugNoBound, frame_support::EqNoBound, frame_support::PartialEqNoBound,
)]
pub enum OffchainMinerError<T: Config> {
	/// An error in the base miner.
	BaseMiner(MinerError<T>),
	/// unsigned-specific checks failed.
	// NOTE: This uses the error type of the parent crate for now. Might be reworked.
	UnsignedChecks(crate::Error<T>),
	/// Something went wrong fetching the lock.
	Lock(&'static str),
	/// Submitting a transaction to the pool failed.
	PoolSubmissionFailed,
	/// Cannot restore a solution that was not stored.
	NoStoredSolution,
	/// Cached solution is not a `submit_unsigned` call.
	SolutionCallInvalid,
	/// Failed to store a solution.
	FailedToStoreSolution,
}

impl<T: Config> From<MinerError<T>> for OffchainMinerError<T> {
	fn from(e: MinerError<T>) -> Self {
		OffchainMinerError::BaseMiner(e)
	}
}

/// A base miner that is only capable of mining a new solution and checking it against the state of
/// this pallet for feasibility, and trimming its length/weight.
///
/// The type of solver is generic and can be provided, as long as it has the same error and account
/// id type as the [`crate::Config::OffchainSolver`]. The default is whatever is fed to
/// [`crate::unsigned::Config::OffchainSolver`].
pub struct BaseMiner<T: Config, Solver = <T as Config>::OffchainSolver>(
	sp_std::marker::PhantomData<(T, Solver)>,
);

impl<T: Config, Solver: NposSolver<AccountId = T::AccountId, Error = OffchainSolverErrorOf<T>>>
	BaseMiner<T, Solver>
{
	/// Mine a new npos solution, with the given number of pages.
	///
	/// This miner is only capable of mining a solution that either uses all of the pages of the
	/// snapshot, or the top `pages` thereof.
	///
	/// This always trims the solution to match a few parameters:
	///
	/// 1. [`crate::verifier::Config::MaxBackersPerWinner`]
	/// 2. [`crate::unsigned::Config::MinerMaxLength`]
	/// 3. [`crate::unsigned::Config::MinerMaxWeight`]
	///
	/// The order of pages returned is aligned with the snapshot. For example, the index 0 of the
	/// returning solution pages corresponds to the page 0 of the snapshot.
	///
	/// The only difference is, if the solution is partial, then [`Pagify`] must be used to properly
	/// pad the results.
	pub fn mine_solution(
		mut pages: PageIndex,
		do_reduce: bool,
	) -> Result<PagedRawSolution<T>, MinerError<T>> {
		pages = pages.min(T::Pages::get());

		// read the appropriate snapshot pages.
		let desired_targets = crate::Snapshot::<T>::desired_targets()
			.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::DesiredTargets))?;
		let all_targets = crate::Snapshot::<T>::targets()
			.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::Targets))?;

		// This is the range of voters that we are interested in. Mind the second `.rev`, it is
		// super critical.
		let voter_pages_range = (crate::Pallet::<T>::lsp()..crate::Pallet::<T>::msp() + 1)
			.rev()
			.take(pages as usize)
			.rev();

		sublog!(
			debug,
			"unsigned::base-miner",
			"mining a solution with {} pages, voter snapshot range will be: {:?}",
			pages,
			voter_pages_range.clone().collect::<Vec<_>>()
		);

		// NOTE: if `pages (2) < T::Pages (3)`, at this point this vector will have length 2, with a
		// layout of `[snapshot(1), snapshot(2)]`, namely the two most significant pages of the
		// snapshot.
		let voter_pages: BoundedVec<_, T::Pages> =
			voter_pages_range
				.map(|p| {
					crate::Snapshot::<T>::voters(p)
						.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::Voters(p)))
				})
				.collect::<Result<Vec<_>, _>>()?
				.try_into()
				.expect("`voter_pages_range` has `.take(pages)`; it must have length less than pages; it must convert to `BoundedVec`; qed");

		// we also build this closure early, so we can let `targets` be consumed.
		let voter_page_fn = helpers::generate_voter_page_fn::<T>(&voter_pages);
		let target_index_fn = helpers::target_index_fn::<T>(&all_targets);

		// now flatten the voters, ready to be used as if pagination did not existed.
		let all_voters: AllVoterPagesFlattenedOf<T> = voter_pages
			.iter()
			.cloned()
			.flatten()
			.collect::<Vec<_>>()
			.try_into()
			.expect("Flattening the voters into `AllVoterPagesFlattenedOf` cannot fail; qed");

		let ElectionResult { winners: _, assignments } = Solver::solve(
			desired_targets as usize,
			all_targets.clone().to_vec(),
			all_voters.clone().into_inner(),
		)
		.map_err(|e| MinerError::Solver(e))?;

		// reduce and trim supports. We don't trim length and weight here, since those are dependent
		// on the final form of the solution ([`PagedRawSolution`]), thus we do it later.
		let trimmed_assignments = {
			// Implementation note: the overall code path is as follows: election_results ->
			// assignments -> staked assignments -> reduce -> supports -> trim supports -> staked
			// assignments -> final assignments
			// This is by no means the most performant, but is the clear and correct.
			use sp_npos_elections::{
				assignment_ratio_to_staked_normalized, assignment_staked_to_ratio_normalized,
				reduce, supports_to_staked_assignment, to_supports, EvaluateSupport,
			};

			// These closures are of no use in the rest of these code, since they only deal with the
			// overall list of voters.
			let cache = helpers::generate_voter_cache::<T, _>(&all_voters);
			let stake_of = helpers::stake_of_fn::<T, _>(&all_voters, &cache);

			// 1. convert to staked and reduce
			let (reduced_count, staked) = {
				let mut staked = assignment_ratio_to_staked_normalized(assignments, &stake_of)
					.map_err::<MinerError<T>, _>(Into::into)?;

				// first, reduce the solution if requested. This will already remove a lot of
				// "redundant" and reduce the chance for the need of any further trimming.
				let count = if do_reduce { reduce(&mut staked) } else { 0 };
				(count, staked)
			};

			// 2. trim the supports by backing.
			let (_pre_score, trim_support_count, final_trimmed_assignments) = {
				// these supports could very well be invalid for SCORE purposes. The reason is that
				// you might trim out half of an account's stake, but we don't look for this
				// account's other votes to fix it.
				let mut supports_invalid_score = to_supports(&staked);

				let pre_score = (&supports_invalid_score).evaluate();
				let num_trimmed = Self::trim_supports(&mut supports_invalid_score);

				// now recreated the staked assignments
				let staked = supports_to_staked_assignment(supports_invalid_score);
				let assignments = assignment_staked_to_ratio_normalized(staked)
					.map_err::<MinerError<T>, _>(Into::into)?;
				(pre_score, num_trimmed, assignments)
			};

			sublog!(
				debug,
				"unsigned::base-miner",
				"initial score = {:?}, reduced {} edges, trimmed {} supports",
				_pre_score,
				reduced_count,
				trim_support_count,
			);

			final_trimmed_assignments
		};

		// split the assignments into different pages.
		let mut paged_assignments: BoundedVec<Vec<AssignmentOf<T>>, T::Pages> =
			BoundedVec::with_bounded_capacity(pages as usize);
		paged_assignments.bounded_resize(pages as usize, Default::default());
		for assignment in trimmed_assignments {
			// NOTE: this `page` index is LOCAL. It does not correspond to the actual page index of
			// the snapshot map, but rather the index in the `voter_pages`.
			let page = voter_page_fn(&assignment.who).ok_or(MinerError::InvalidPage)?;
			let assignment_page =
				paged_assignments.get_mut(page as usize).ok_or(MinerError::InvalidPage)?;
			assignment_page.push(assignment);
		}

		// convert each page to a compact struct
		let solution_pages: BoundedVec<SolutionOf<T>, T::Pages> = paged_assignments
			.into_iter()
			.enumerate()
			.map(|(page_index, assignment_page)| {
				// get the page of the snapshot that corresponds to this page of the assignments.
				let page: PageIndex = page_index.saturated_into();
				let voter_snapshot_page = voter_pages
					.get(page as usize)
					.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::Voters(page)))?;

				let voter_index_fn = {
					let cache = helpers::generate_voter_cache::<T, _>(&voter_snapshot_page);
					helpers::voter_index_fn_owned::<T>(cache)
				};
				<SolutionOf<T>>::from_assignment(
					&assignment_page,
					&voter_index_fn,
					&target_index_fn,
				)
				.map_err::<MinerError<T>, _>(Into::into)
			})
			.collect::<Result<Vec<_>, _>>()?
			.try_into()
			.expect("`paged_assignments` is bound by `T::Pages`; length cannot change in iter chain; qed");

		// now do the weight and length trim.
		let mut solution_pages_unbounded = solution_pages.into_inner();
		let _trim_length_weight =
			Self::maybe_trim_weight_and_len(&mut solution_pages_unbounded, &voter_pages)?;
		let solution_pages = solution_pages_unbounded
			.try_into()
			.expect("maybe_trim_weight_and_len cannot increase the length of its input; qed.");
		sublog!(
			debug,
			"unsigned::base-miner",
			"trimmed {} voters due to length/weight restriction.",
			_trim_length_weight
		);

		// finally, wrap everything up. Assign a fake score here, since we might need to re-compute
		// it.
		let round = crate::Pallet::<T>::round();
		let mut paged = PagedRawSolution { round, solution_pages, score: Default::default() };

		// OPTIMIZATION: we do feasibility_check inside `compute_score`, and once later
		// pre_dispatch. I think it is fine, but maybe we can improve it.
		let score = Self::compute_score(&paged).map_err::<MinerError<T>, _>(Into::into)?;
		paged.score = score.clone();

		sublog!(
			info,
			"unsigned::base-miner",
			"mined a solution with score {:?}, {} winners, {} voters, {} edges, and {} bytes",
			score,
			paged.winner_count_single_page_target_snapshot(),
			paged.voter_count(),
			paged.edge_count(),
			paged.using_encoded(|b| b.len())
		);

		Ok(paged)
	}

	/// Mine a new solution. Performs the feasibility checks on it as well.
	pub fn mine_checked_solution(
		pages: PageIndex,
		reduce: bool,
	) -> Result<PagedRawSolution<T>, MinerError<T>> {
		let paged_solution = Self::mine_solution(pages, reduce)?;
		let _ = Self::check_solution(&paged_solution, None, true, "mined")?;
		Ok(paged_solution)
	}

	/// Check the solution, from the perspective of the base miner:
	///
	/// 1. snapshot-independent checks.
	/// 	- with the fingerprint check being an optional step fo that.
	/// 2. optionally, feasibility check.
	///
	/// In most cases, you should always use this either with `do_feasibility = true` or
	/// `maybe_snapshot_fingerprint.is_some()`. Doing both could be an overkill. The snapshot
	/// staying constant (which can be checked via the hash) is a string guarantee that the
	/// feasibility still holds.
	pub fn check_solution(
		paged_solution: &PagedRawSolution<T>,
		maybe_snapshot_fingerprint: Option<T::Hash>,
		do_feasibility: bool,
		solution_type: &str,
	) -> Result<(), MinerError<T>> {
		let _ = crate::Pallet::<T>::snapshot_independent_checks(
			paged_solution,
			maybe_snapshot_fingerprint,
		)
		.map_err(|pe| MinerError::SnapshotIndependentChecks(pe))?;

		if do_feasibility {
			let _ = Self::check_feasibility(&paged_solution, solution_type)?;
		}

		Ok(())
	}

	/// perform the feasibility check on all pages of a solution, returning `Ok(())` if all good and
	/// the corresponding error otherwise.
	pub fn check_feasibility(
		paged_solution: &PagedRawSolution<T>,
		solution_type: &str,
	) -> Result<Vec<SupportsOf<T::Verifier>>, MinerError<T>> {
		// check every solution page for feasibility.
		paged_solution
			.solution_pages
			.pagify(T::Pages::get())
			.map(|(page_index, page_solution)| {
				<T::Verifier as verifier::Verifier>::feasibility_check_page(
					page_solution.clone(),
					page_index as PageIndex,
				)
			})
			.collect::<Result<Vec<_>, _>>()
			.map_err(|err| {
				sublog!(
					warn,
					"unsigned::base-miner",
					"feasibility check failed for {} solution at: {:?}",
					solution_type,
					err
				);
				MinerError::from(err)
			})
	}

	/// Take the given raw paged solution and compute its score. This will replicate what the chain
	/// would do as closely as possible, and expects all the corresponding snapshot data to be
	/// available.
	fn compute_score(paged_solution: &PagedRawSolution<T>) -> Result<ElectionScore, MinerError<T>> {
		use sp_npos_elections::EvaluateSupport;
		use sp_std::collections::btree_map::BTreeMap;

		let all_supports = Self::check_feasibility(paged_solution, "mined")?;
		let mut total_backings: BTreeMap<T::AccountId, ExtendedBalance> = BTreeMap::new();
		all_supports.into_iter().map(|x| x.0).flatten().for_each(|(who, support)| {
			let backing = total_backings.entry(who).or_default();
			*backing = backing.saturating_add(support.total);
		});

		let all_supports = total_backings
			.into_iter()
			.map(|(who, total)| (who, Support { total, ..Default::default() }))
			.collect::<Vec<_>>();

		Ok((&all_supports).evaluate())
	}

	/// Trim the given supports so that the count of backings in none of them exceeds
	/// [`crate::verifier::Config::MaxBackersPerWinner`].
	///
	/// Note that this should only be called on the *global, non-paginated* supports. Calling this
	/// on a single page of supports is essentially pointless and does not guarantee anything in
	/// particular.
	///
	/// Returns the count of supports trimmed.
	pub fn trim_supports(supports: &mut sp_npos_elections::Supports<T::AccountId>) -> u32 {
		let limit = <T::Verifier as crate::verifier::Verifier>::MaxBackersPerWinner::get() as usize;
		let mut count = 0;
		supports
			.iter_mut()
			.filter_map(
				|(_, support)| if support.voters.len() > limit { Some(support) } else { None },
			)
			.for_each(|support| {
				support.voters.sort_unstable_by(|(_, b1), (_, b2)| b1.cmp(&b2).reverse());
				support.voters.truncate(limit);
				support.total = support.voters.iter().fold(0, |acc, (_, x)| acc.saturating_add(*x));
				count.saturating_inc();
			});
		count
	}

	/// Maybe tim the weight and length of the given multi-page solution.
	///
	/// Returns the number of voters removed.
	///
	/// If either of the bounds are not met, the trimming strategy is as follows:
	///
	/// Start from the least significant page. Assume only this page is going to be trimmed. call
	/// `page.sort()` on this page. This will make sure in each field (`votes1`, `votes2`, etc.) of
	/// that page, the voters are sorted by descending stake. Then, we compare the last item of each
	/// field. This is the process of removing the single least staked voter.
	///
	/// We repeat this until satisfied, for both weight and length. If a full page is removed, but
	/// the bound is not satisfied, we need to make sure that we sort the next least valuable page,
	/// and repeat the same process.
	///
	/// NOTE: this is a public function to be used by the `OffchainWorkerMiner` or any similar one,
	/// based on the submission strategy. The length and weight bounds of a call are dependent on
	/// the number of pages being submitted, the number of blocks over which we submit, and the type
	/// of the transaction and its weight (e.g. signed or unsigned).
	///
	/// NOTE: It could be that this function removes too many voters, and the solution becomes
	/// invalid. This is not yet handled and only a warning is emitted.
	pub fn maybe_trim_weight_and_len(
		solution_pages: &mut Vec<SolutionOf<T>>,
		paged_voters: &AllVoterPagesOf<T>,
	) -> Result<u32, MinerError<T>> {
		debug_assert_eq!(solution_pages.len(), paged_voters.len());
		let size_limit = T::MinerMaxLength::get();
		let weight_limit = T::MinerMaxWeight::get();

		let all_voters_count = crate::Snapshot::<T>::voters_decode_len(crate::Pallet::<T>::msp())
			.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::Voters(
				crate::Pallet::<T>::msp(),
			)))? as u32;
		let all_targets_count = crate::Snapshot::<T>::targets_decode_len()
			.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::Targets))?
			as u32;
		let desired_targets = crate::Snapshot::<T>::desired_targets()
			.ok_or(MinerError::SnapshotUnAvailable(SnapshotType::DesiredTargets))?;

		let winner_count_of = |solution_pages: &Vec<SolutionOf<T>>| {
			solution_pages
				.iter()
				.map(|page| page.unique_targets())
				.flatten()
				.collect::<sp_std::collections::btree_set::BTreeSet<_>>()
				.len() as u32
		};

		let voter_count_of = |solution_pages: &Vec<SolutionOf<T>>| {
			solution_pages
				.iter()
				.map(|page| page.voter_count())
				.fold(0, |acc, x| acc.saturating_add(x)) as u32
		};

		let needs_any_trim = |solution_pages: &mut Vec<SolutionOf<T>>| {
			let size = solution_pages.encoded_size() as u32;

			let next_active_targets = winner_count_of(solution_pages);
			if next_active_targets < desired_targets {
				sublog!(warn, "unsigned::base-miner", "trimming has cause a solution to have less targets than desired, this might fail feasibility");
			}

			let weight = <T as Config>::WeightInfo::submit_unsigned(
				all_voters_count,
				all_targets_count,
				// NOTE: we could not re-compute this all the time and instead assume that in each
				// round, it is the previous value minus one.
				voter_count_of(solution_pages),
				next_active_targets,
			);
			let needs_weight_trim = weight > weight_limit;
			let needs_len_trim = size > size_limit;

			needs_weight_trim || needs_len_trim
		};

		// Note the solution might be partial. In either case, this is its least significant page.
		let mut current_trimming_page = 0;
		let current_trimming_page_stake_of = |current_trimming_page: usize| {
			Box::new(move |voter_index: &SolutionVoterIndexOf<T>| -> VoteWeight {
				paged_voters
					.get(current_trimming_page)
					.and_then(|page_voters| {
						page_voters
							.get((*voter_index).saturated_into::<usize>())
							.map(|(_, s, _)| *s)
					})
					.unwrap_or_default()
			})
		};

		let sort_current_trimming_page =
			|current_trimming_page: usize, solution_pages: &mut Vec<SolutionOf<T>>| {
				solution_pages.get_mut(current_trimming_page).map(|solution_page| {
					let stake_of_fn = current_trimming_page_stake_of(current_trimming_page);
					solution_page.sort(stake_of_fn)
				});
			};

		let is_empty = |solution_pages: &Vec<SolutionOf<T>>| {
			solution_pages.iter().all(|page| page.voter_count().is_zero())
		};

		if needs_any_trim(solution_pages) {
			sort_current_trimming_page(current_trimming_page, solution_pages)
		}

		// Implementation note: we want `solution_pages` and `paged_voters` to remain in sync, so
		// while one of the pages of `solution_pages` might become "empty" we prefer not removing
		// it. This has a slight downside that even an empty pages consumes a few dozens of bytes,
		// which we accept for code simplicity.

		let mut removed = 0;
		while needs_any_trim(solution_pages) && !is_empty(solution_pages) {
			if let Some(removed_idx) =
				solution_pages.get_mut(current_trimming_page).and_then(|page| {
					let stake_of_fn = current_trimming_page_stake_of(current_trimming_page);
					page.remove_weakest_sorted(&stake_of_fn)
				}) {
				sublog!(
					trace,
					"unsigned::base-miner",
					"removed voter at index {:?} of (un-pagified) page {} as the weakest due to weight/length limits.",
					removed_idx,
					current_trimming_page
				);
				// we removed one person, continue.
				removed.saturating_inc();
			} else {
				// this page cannot support remove anymore. Try and go to the next page.
				sublog!(
					debug,
					"unsigned::base-miner",
					"page {} seems to be fully empty now, moving to the next one",
					current_trimming_page
				);
				let next_page = current_trimming_page.saturating_add(1);
				if paged_voters.len() > next_page {
					current_trimming_page = next_page;
					sort_current_trimming_page(current_trimming_page, solution_pages);
				} else {
					sublog!(
						warn,
						"unsigned::base-miner",
						"no more pages to trim from at page {}, already trimmed",
						current_trimming_page
					);
					break
				}
			}
		}

		Ok(removed)
	}
}

/// A miner that is suited to work inside offchain worker environment.
pub(crate) struct OffchainWorkerMiner<T: Config>(sp_std::marker::PhantomData<T>);

impl<T: Config> OffchainWorkerMiner<T> {
	/// Storage key used to store the offchain worker running status.
	pub(crate) const OFFCHAIN_LOCK: &'static [u8] = b"parity/multi-block-unsigned-election/lock";
	/// Storage key used to store the last block number at which offchain worker ran.
	const OFFCHAIN_LAST_BLOCK: &'static [u8] = b"parity/multi-block-unsigned-election";
	/// Storage key used to cache the solution `call` and its snapshot fingerprint.
	const OFFCHAIN_CACHED_CALL: &'static [u8] = b"parity/multi-block-unsigned-election/call";
	/// The number of pages that the offchain worker miner will try and mine.
	const MINING_PAGES: PageIndex = 1;

	/// Get a checked solution from the base miner, ensure unsigned-specific checks also pass, then
	/// return an submittable call.
	fn mine_checked_call() -> Result<Call<T>, OffchainMinerError<T>> {
		// we always do reduce in the offchain worker miner.
		let reduce = true;

		// NOTE: we don't run any checks in the base miner, and run all of them via
		// `Self::full_checks`.
		let paged_solution =
			BaseMiner::<T, T::OffchainSolver>::mine_solution(Self::MINING_PAGES, reduce)
				.map_err::<OffchainMinerError<T>, _>(Into::into)?;
		// check the call fully, no fingerprinting.
		let _ = Self::check_solution(&paged_solution, None, true, "mined")?;

		let call: Call<T> =
			Call::<T>::submit_unsigned { paged_solution: Box::new(paged_solution) }.into();

		Ok(call)
	}

	/// Mine a new checked solution, cache it, and submit it back to the chain as an unsigned
	/// transaction.
	pub fn mine_check_save_submit() -> Result<(), OffchainMinerError<T>> {
		sublog!(debug, "unsigned::ocw-miner", "miner attempting to compute an unsigned solution.");
		let call = Self::mine_checked_call()?;
		Self::save_solution(&call, crate::Snapshot::<T>::fingerprint())?;
		Self::submit_call(call)
	}

	/// Check the solution, from the perspective of the offchain-worker miner:
	///
	/// 1. unsigned-specific checks.
	/// 2. full-checks of the base miner
	/// 	1. optionally feasibility check.
	/// 	2. snapshot-independent checks.
	/// 		1. optionally, snapshot fingerprint.
	pub fn check_solution(
		paged_solution: &PagedRawSolution<T>,
		maybe_snapshot_fingerprint: Option<T::Hash>,
		do_feasibility: bool,
		solution_type: &str,
	) -> Result<(), OffchainMinerError<T>> {
		// NOTE: we prefer cheap checks first, so first run unsigned checks.
		Pallet::unsigned_specific_checks(paged_solution)
			.map_err(|pe| OffchainMinerError::UnsignedChecks(pe))
			.and_then(|_| {
				BaseMiner::<T, T::OffchainSolver>::check_solution(
					paged_solution,
					maybe_snapshot_fingerprint,
					do_feasibility,
					solution_type,
				)
				.map_err(OffchainMinerError::BaseMiner)
			})
	}

	fn submit_call(call: Call<T>) -> Result<(), OffchainMinerError<T>> {
		sublog!(
			debug,
			"unsigned::ocw-miner",
			"miner submitting a solution as an unsigned transaction"
		);
		frame_system::offchain::SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(
			call.into(),
		)
		.map_err(|_| OffchainMinerError::PoolSubmissionFailed)
	}

	/// Attempt to restore a solution from cache. Otherwise, compute it fresh. Either way,
	/// submit if our call's score is greater than that of the cached solution.
	pub fn restore_or_compute_then_maybe_submit() -> Result<(), OffchainMinerError<T>> {
		sublog!(
			debug,
			"unsigned::ocw-miner",
			"miner attempting to restore or compute an unsigned solution."
		);

		let call = Self::restore_solution()
			.and_then(|(call, snapshot_fingerprint)| {
				// ensure the cached call is still current before submitting
				if let Call::submit_unsigned { paged_solution, .. } = &call {
					// we check the snapshot fingerprint instead of doing a full feasibility.
					OffchainWorkerMiner::<T>::check_solution(
						paged_solution,
						Some(snapshot_fingerprint),
						false,
						"restored"
					).map_err::<OffchainMinerError<T>, _>(Into::into)?;
					Ok(call)
				} else {
					Err(OffchainMinerError::SolutionCallInvalid)
				}
			})
			.or_else::<OffchainMinerError<T>, _>(|error| {
				use MinerError::*;
				use OffchainMinerError::*;

				match error {
					NoStoredSolution => {
						// IFF, not present regenerate.
						let call = Self::mine_checked_call()?;
						Self::save_solution(&call, crate::Snapshot::<T>::fingerprint())?;
						Ok(call)
					},
					UnsignedChecks(ref e) => {
						sublog!(
							error,
							"unsigned::ocw-miner",
							"unsigned specific checks failed ({:?}) while restoring solution. This should never happen. clearing cache.",
							e,
						);
						Self::clear_offchain_solution_cache();
						Err(error)
					},
					BaseMiner(Feasibility(_))
						| BaseMiner(SnapshotIndependentChecks(crate::Error::<T>::WrongRound))
						| BaseMiner(SnapshotIndependentChecks(crate::Error::<T>::WrongFingerprint))
					=> {
						// note that failing `Feasibility` can only mean that the solution was
						// computed over a snapshot that has changed due to a fork.
						sublog!(warn, "unsigned::ocw-miner", "wiping infeasible solution ({:?}).", error);
						// kill the "bad" solution.
						Self::clear_offchain_solution_cache();

						// .. then return the error as-is.
						Err(error)
					},
					_ => {
						sublog!(debug, "unsigned::ocw-miner", "unhandled error in restoring offchain solution {:?}", error);
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
	pub fn ensure_offchain_repeat_frequency(
		now: T::BlockNumber,
	) -> Result<(), OffchainMinerError<T>> {
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
			Err(MutateStorageError::ConcurrentModification(_)) => Err(OffchainMinerError::Lock(
				"failed to write to offchain db (concurrent modification).",
			)),
			// fork etc.
			Err(MutateStorageError::ValueFunctionFailed(why)) => Err(OffchainMinerError::Lock(why)),
		}
	}

	/// Save a given call into OCW storage.
	fn save_solution(
		call: &Call<T>,
		snapshot_fingerprint: T::Hash,
	) -> Result<(), OffchainMinerError<T>> {
		sublog!(debug, "unsigned::ocw-miner", "saving a call to the offchain storage.");
		let storage = StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL);
		match storage.mutate::<_, (), _>(|_| Ok((call.clone(), snapshot_fingerprint))) {
			Ok(_) => Ok(()),
			Err(MutateStorageError::ConcurrentModification(_)) =>
				Err(OffchainMinerError::FailedToStoreSolution),
			Err(MutateStorageError::ValueFunctionFailed(_)) => {
				// this branch should be unreachable according to the definition of
				// `StorageValueRef::mutate`: that function should only ever `Err` if the closure we
				// pass it returns an error. however, for safety in case the definition changes, we
				// do not optimize the branch away or panic.
				Err(OffchainMinerError::FailedToStoreSolution)
			},
		}
	}

	/// Get a saved solution from OCW storage if it exists.
	fn restore_solution() -> Result<(Call<T>, T::Hash), OffchainMinerError<T>> {
		StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL)
			.get()
			.ok()
			.flatten()
			.ok_or(OffchainMinerError::NoStoredSolution)
	}

	/// Clear a saved solution from OCW storage.
	fn clear_offchain_solution_cache() {
		sublog!(debug, "unsigned::ocw-miner", "clearing offchain call cache storage.");
		let mut storage = StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL);
		storage.clear();
	}

	#[cfg(test)]
	fn cached_solution() -> Option<Call<T>> {
		StorageValueRef::persistent(&Self::OFFCHAIN_CACHED_CALL)
			.get::<Call<T>>()
			.unwrap()
	}
}

// This will only focus on testing the internals of `maybe_trim_weight_and_len_works`.
#[cfg(test)]
mod trim_weight_length {
	use super::*;
	use crate::{mock::*, verifier::Verifier};
	use frame_election_provider_support::TryIntoBoundedSupportsVec;
	use sp_npos_elections::Support;

	#[test]
	fn trim_weight_basic() {
		// This is just demonstration to show the normal election result with new votes, without any
		// trimming.
		ExtBuilder::unsigned().build_and_execute(|| {
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_full_solution().unwrap();

			// 4 of these will be trimmed.
			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				8
			);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// NOTE: this test is a bit funny because our msp snapshot page actually contains voters
			// with less stake than lsp.. but that's not relevant here.
			assert_eq!(
				supports,
				vec![
					// supports from 30, 40, both will be removed.
					vec![
						(30, Support { total: 30, voters: vec![(30, 30)] }),
						(40, Support { total: 40, voters: vec![(40, 40)] })
					],
					// supports from 5, 6, 7. 5 and 6 will be removed.
					vec![
						(30, Support { total: 11, voters: vec![(7, 7), (5, 2), (6, 2)] }),
						(40, Support { total: 7, voters: vec![(5, 3), (6, 4)] })
					],
					// all will stay
					vec![(40, Support { total: 9, voters: vec![(2, 2), (3, 3), (4, 4)] })]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		});

		// now we get to the real test...
		ExtBuilder::unsigned().miner_weight(4).build_and_execute(|| {
			// first, replace the stake of all voters with their account id.
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			// with 1 weight unit per voter, this can only support 4 voters, despite having 12 in
			// the snapshot.
			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_full_solution().unwrap();
			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				4
			);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// a solution is queued.
			assert!(VerifierPallet::queued_score().is_some());

			assert_eq!(
				supports,
				vec![
					vec![],
					vec![(30, Support { total: 7, voters: vec![(7, 7)] })],
					vec![(40, Support { total: 9, voters: vec![(2, 2), (3, 3), (4, 4)] })]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		})
	}

	#[test]
	fn trim_weight_partial_solution() {
		// This is just demonstration to show the normal election result with new votes, without any
		// trimming.
		ExtBuilder::unsigned().build_and_execute(|| {
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_solution(2).unwrap();

			// 3 of these will be trimmed.
			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				7
			);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// a solution is queued.
			assert!(VerifierPallet::queued_score().is_some());

			assert_eq!(
				supports,
				vec![
					vec![],
					// 5, 6, 7 will be removed in the next test block
					vec![
						(10, Support { total: 10, voters: vec![(8, 8), (5, 2)] }),
						(30, Support { total: 16, voters: vec![(6, 6), (7, 7), (5, 3)] })
					],
					vec![
						(10, Support { total: 5, voters: vec![(1, 1), (4, 4)] }),
						(30, Support { total: 2, voters: vec![(2, 2)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		});

		// now we get to the real test...
		ExtBuilder::unsigned().miner_weight(4).build_and_execute(|| {
			// first, replace the stake of all voters with their account id.
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_solution(2).unwrap();
			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				4
			);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// a solution is queued.
			assert!(VerifierPallet::queued_score().is_some());

			assert_eq!(
				supports,
				vec![
					vec![],
					vec![(10, Support { total: 8, voters: vec![(8, 8)] })],
					vec![
						(10, Support { total: 5, voters: vec![(1, 1), (4, 4)] }),
						(30, Support { total: 2, voters: vec![(2, 2)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		})
	}

	#[test]
	fn trim_weight_too_much_makes_solution_invalid() {
		// with just 1 units, we can support 1 voter. This is not enough to have 2 winner which we
		// want.
		ExtBuilder::unsigned().miner_weight(1).build_and_execute(|| {
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_full_solution().unwrap();
			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				1
			);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// nothing is queued
			assert!(VerifierPallet::queued_score().is_none());
			assert_eq!(
				supports,
				vec![vec![], vec![], vec![]].try_into_bounded_supports_vec().unwrap()
			);
		})
	}

	#[test]
	fn trim_length() {
		// This is just demonstration to show the normal election result with new votes, without any
		// trimming.
		ExtBuilder::unsigned().build_and_execute(|| {
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_full_solution().unwrap();

			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				8
			);

			assert_eq!(solution.solution_pages.encoded_size(), 105);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// a solution is queued.
			assert!(VerifierPallet::queued_score().is_some());

			assert_eq!(
				supports,
				vec![
					// if we set any limit less than 105, 30 will be the first to leave.
					vec![
						(30, Support { total: 30, voters: vec![(30, 30)] }),
						(40, Support { total: 40, voters: vec![(40, 40)] })
					],
					vec![
						(30, Support { total: 11, voters: vec![(7, 7), (5, 2), (6, 2)] }),
						(40, Support { total: 7, voters: vec![(5, 3), (6, 4)] })
					],
					vec![(40, Support { total: 9, voters: vec![(2, 2), (3, 3), (4, 4)] })]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		});

		ExtBuilder::unsigned().miner_max_length(104).build_and_execute(|| {
			let mut current_voters = Voters::get();
			current_voters.iter_mut().for_each(|(who, stake, ..)| *stake = *who);
			Voters::set(current_voters);

			roll_to_snapshot_created();
			ensure_voters(3, 12);

			let solution = mine_full_solution().unwrap();

			assert_eq!(
				solution.solution_pages.iter().map(|page| page.voter_count()).sum::<usize>(),
				7
			);

			assert_eq!(solution.solution_pages.encoded_size(), 99);

			load_mock_signed_and_start(solution);
			let supports = roll_to_full_verification();

			// a solution is queued.
			assert!(VerifierPallet::queued_score().is_some());

			assert_eq!(
				supports,
				vec![
					// 30 is gone!
					vec![(40, Support { total: 40, voters: vec![(40, 40)] })],
					vec![
						(30, Support { total: 11, voters: vec![(7, 7), (5, 2), (6, 2)] }),
						(40, Support { total: 7, voters: vec![(5, 3), (6, 4)] })
					],
					vec![(40, Support { total: 9, voters: vec![(2, 2), (3, 3), (4, 4)] })]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);
		});
	}
}

#[cfg(test)]
mod base_miner {
	use super::*;
	use crate::{mock::*, Snapshot};
	use frame_election_provider_support::TryIntoBoundedSupportsVec;
	use sp_npos_elections::Support;
	use sp_runtime::PerU16;

	#[test]
	fn pagination_does_not_affect_score() {
		let score_1 = ExtBuilder::unsigned()
			.pages(1)
			.voter_per_page(12)
			.build_unchecked()
			.execute_with(|| {
				roll_to_snapshot_created();
				mine_full_solution().unwrap().score
			});
		let score_2 = ExtBuilder::unsigned()
			.pages(2)
			.voter_per_page(6)
			.build_unchecked()
			.execute_with(|| {
				roll_to_snapshot_created();
				mine_full_solution().unwrap().score
			});
		let score_3 = ExtBuilder::unsigned()
			.pages(3)
			.voter_per_page(4)
			.build_unchecked()
			.execute_with(|| {
				roll_to_snapshot_created();
				mine_full_solution().unwrap().score
			});

		assert_eq!(score_1, score_2);
		assert_eq!(score_2, score_3);
	}

	#[test]
	fn mine_solution_single_page_works() {
		ExtBuilder::unsigned().pages(1).voter_per_page(8).build_and_execute(|| {
			roll_to_snapshot_created();

			ensure_voters(1, 8);
			ensure_targets(1, 4);

			assert_eq!(
				Snapshot::<Runtime>::voters(0)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![1, 2, 3, 4, 5, 6, 7, 8]
			);

			let paged = mine_full_solution().unwrap();
			assert_eq!(paged.solution_pages.len(), 1);

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, true, "mined").unwrap();

			// now do a realistic full verification
			load_mock_signed_and_start(paged.clone());
			let supports = roll_to_full_verification();

			assert_eq!(
				supports,
				vec![vec![
					(10, Support { total: 30, voters: vec![(1, 10), (8, 10), (4, 5), (5, 5)] }),
					(
						40,
						Support {
							total: 40,
							voters: vec![(2, 10), (3, 10), (6, 10), (4, 5), (5, 5)]
						}
					)
				]]
				.try_into_bounded_supports_vec()
				.unwrap()
			);

			// NOTE: this is the same as the score of any other test that contains the first 8
			// voters, we already test for this in `pagination_does_not_affect_score`.
			assert_eq!(
				paged.score,
				ElectionScore { minimal_stake: 30, sum_stake: 70, sum_stake_squared: 2500 }
			);
		})
	}

	#[test]
	fn mine_solution_double_page_works() {
		ExtBuilder::unsigned().pages(2).voter_per_page(4).build_and_execute(|| {
			roll_to_snapshot_created();

			// 2 pages of 8 voters
			ensure_voters(2, 8);
			// 1 page of 4 targets
			ensure_targets(1, 4);

			// voters in pages. note the reverse page index.
			assert_eq!(
				Snapshot::<Runtime>::voters(0)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8]
			);
			assert_eq!(
				Snapshot::<Runtime>::voters(1)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![1, 2, 3, 4]
			);
			// targets in pages.
			assert_eq!(Snapshot::<Runtime>::targets().unwrap(), vec![10, 20, 30, 40]);
			let paged = mine_full_solution().unwrap();

			assert_eq!(
				paged.solution_pages,
				vec![
					TestNposSolution {
						// voter 6 (index 1) is backing 40 (index 3).
						// voter 8 (index 3) is backing 10 (index 0)
						votes1: vec![(1, 3), (3, 0)],
						// voter 5 (index 0) is backing 40 (index 10) and 10 (index 0)
						votes2: vec![(0, [(0, PerU16::from_parts(32768))], 3)],
						..Default::default()
					},
					TestNposSolution {
						// voter 1 (index 0) is backing 10 (index 0)
						// voter 2 (index 1) is backing 40 (index 3)
						// voter 3 (index 2) is backing 40 (index 3)
						votes1: vec![(0, 0), (1, 3), (2, 3)],
						// voter 4 (index 3) is backing 40 (index 10) and 10 (index 0)
						votes2: vec![(3, [(0, PerU16::from_parts(32768))], 3)],
						..Default::default()
					},
				]
			);

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, false, "mined").unwrap();

			// it must also be verified in the verifier
			load_mock_signed_and_start(paged.clone());
			let supports = roll_to_full_verification();

			assert_eq!(
				supports,
				vec![
					// page0, supports from voters 5, 6, 7, 8
					vec![
						(10, Support { total: 15, voters: vec![(8, 10), (5, 5)] }),
						(40, Support { total: 15, voters: vec![(6, 10), (5, 5)] })
					],
					// page1 supports from voters 1, 2, 3, 4
					vec![
						(10, Support { total: 15, voters: vec![(1, 10), (4, 5)] }),
						(40, Support { total: 25, voters: vec![(2, 10), (3, 10), (4, 5)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);

			assert_eq!(
				paged.score,
				ElectionScore { minimal_stake: 30, sum_stake: 70, sum_stake_squared: 2500 }
			);
		})
	}

	#[test]
	fn mine_solution_triple_page_works() {
		ExtBuilder::unsigned().pages(3).voter_per_page(4).build_and_execute(|| {
			roll_to_snapshot_created();

			ensure_voters(3, 12);
			ensure_targets(1, 4);

			// voters in pages. note the reverse page index.
			assert_eq!(
				Snapshot::<Runtime>::voters(2)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![1, 2, 3, 4]
			);
			assert_eq!(
				Snapshot::<Runtime>::voters(1)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8]
			);
			assert_eq!(
				Snapshot::<Runtime>::voters(0)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![10, 20, 30, 40]
			);

			let paged = mine_full_solution().unwrap();
			assert_eq!(
				paged.solution_pages,
				vec![
					TestNposSolution { votes1: vec![(2, 2), (3, 3)], ..Default::default() },
					TestNposSolution {
						votes1: vec![(2, 2)],
						votes2: vec![
							(0, [(2, PerU16::from_parts(32768))], 3),
							(1, [(2, PerU16::from_parts(32768))], 3)
						],
						..Default::default()
					},
					TestNposSolution {
						votes1: vec![(2, 3), (3, 3)],
						votes2: vec![(1, [(2, PerU16::from_parts(32768))], 3)],
						..Default::default()
					},
				]
			);

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, true, "mined").unwrap();
			// now do a realistic full verification
			load_mock_signed_and_start(paged.clone());
			let supports = roll_to_full_verification();

			assert_eq!(
				supports,
				vec![
					// page 0: self-votes.
					vec![
						(30, Support { total: 30, voters: vec![(30, 30)] }),
						(40, Support { total: 40, voters: vec![(40, 40)] })
					],
					// page 1: 5, 6, 7, 8
					vec![
						(30, Support { total: 20, voters: vec![(7, 10), (5, 5), (6, 5)] }),
						(40, Support { total: 10, voters: vec![(5, 5), (6, 5)] })
					],
					// page 2: 1, 2, 3, 4
					vec![
						(30, Support { total: 5, voters: vec![(2, 5)] }),
						(40, Support { total: 25, voters: vec![(3, 10), (4, 10), (2, 5)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);

			assert_eq!(
				paged.score,
				ElectionScore { minimal_stake: 55, sum_stake: 130, sum_stake_squared: 8650 }
			);
		})
	}

	#[test]
	fn mine_solution_choses_most_significant_pages() {
		ExtBuilder::unsigned().pages(2).voter_per_page(4).build_and_execute(|| {
			roll_to_snapshot_created();

			ensure_voters(2, 8);
			ensure_targets(1, 4);

			// these folks should be ignored safely.
			assert_eq!(
				Snapshot::<Runtime>::voters(0)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8]
			);
			// voters in pages 1, this is the most significant page.
			assert_eq!(
				Snapshot::<Runtime>::voters(1)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![1, 2, 3, 4]
			);

			// now we ask for just 1 page of solution.
			let paged = mine_solution(1).unwrap();

			assert_eq!(
				paged.solution_pages,
				vec![TestNposSolution {
					// voter 1 (index 0) is backing 10 (index 0)
					// voter 2 (index 1) is backing 40 (index 3)
					// voter 3 (index 2) is backing 40 (index 3)
					votes1: vec![(0, 0), (1, 3), (2, 3)],
					// voter 4 (index 3) is backing 40 (index 10) and 10 (index 0)
					votes2: vec![(3, [(0, PerU16::from_parts(32768))], 3)],
					..Default::default()
				}]
			);

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, true, "mined").unwrap();
			// now do a realistic full verification.
			load_mock_signed_and_start(paged.clone());
			let supports = roll_to_full_verification();

			assert_eq!(
				supports,
				vec![
					// page0: non existent.
					vec![],
					// page1 supports from voters 1, 2, 3, 4
					vec![
						(10, Support { total: 15, voters: vec![(1, 10), (4, 5)] }),
						(40, Support { total: 25, voters: vec![(2, 10), (3, 10), (4, 5)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);

			assert_eq!(
				paged.score,
				ElectionScore { minimal_stake: 15, sum_stake: 40, sum_stake_squared: 850 }
			);
		})
	}

	#[test]
	fn mine_solution_2_out_of_3_pages() {
		ExtBuilder::unsigned().pages(3).voter_per_page(4).build_and_execute(|| {
			roll_to_snapshot_created();

			ensure_voters(3, 12);
			ensure_targets(1, 4);

			assert_eq!(
				Snapshot::<Runtime>::voters(0)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![10, 20, 30, 40]
			);
			assert_eq!(
				Snapshot::<Runtime>::voters(1)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8]
			);
			assert_eq!(
				Snapshot::<Runtime>::voters(2)
					.unwrap()
					.into_iter()
					.map(|(x, _, _)| x)
					.collect::<Vec<_>>(),
				vec![1, 2, 3, 4]
			);

			// now we ask for just 1 page of solution.
			let paged = mine_solution(2).unwrap();

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, true, "mined").unwrap();

			assert_eq!(
				paged.solution_pages,
				vec![
					// this can be 'pagified" to snapshot at index 1, which contains 5, 6, 7, 8
					// in which:
					// 6 (index:1) votes for 40 (index:3)
					// 8 (index:1) votes for 10 (index:0)
					// 5 votes for both 10 and 40
					TestNposSolution {
						votes1: vec![(1, 3), (3, 0)],
						votes2: vec![(0, [(0, PerU16::from_parts(32768))], 3)],
						..Default::default()
					},
					// this can be 'pagified" to snapshot at index 2, which contains 1, 2, 3, 4
					// in which:
					// 1 (index:0) votes for 10 (index:0)
					// 2 (index:1) votes for 40 (index:3)
					// 3 (index:2) votes for 40 (index:3)
					// 4 votes for both 10 and 40
					TestNposSolution {
						votes1: vec![(0, 0), (1, 3), (2, 3)],
						votes2: vec![(3, [(0, PerU16::from_parts(32768))], 3)],
						..Default::default()
					}
				]
			);

			// this solution must be feasible and submittable.
			BaseMiner::<Runtime>::check_solution(&paged, None, true, "mined").unwrap();
			// now do a realistic full verification.
			load_mock_signed_and_start(paged.clone());
			let supports = roll_to_full_verification();

			assert_eq!(
				supports,
				vec![
					// empty page 0.
					vec![],
					// supports from voters 5, 6, 7, 8
					vec![
						(10, Support { total: 15, voters: vec![(8, 10), (5, 5)] }),
						(40, Support { total: 15, voters: vec![(6, 10), (5, 5)] })
					],
					// supports from voters 1, 2, 3, 4
					vec![
						(10, Support { total: 15, voters: vec![(1, 10), (4, 5)] }),
						(40, Support { total: 25, voters: vec![(2, 10), (3, 10), (4, 5)] })
					]
				]
				.try_into_bounded_supports_vec()
				.unwrap()
			);

			assert_eq!(
				paged.score,
				ElectionScore { minimal_stake: 30, sum_stake: 70, sum_stake_squared: 2500 }
			);
		})
	}

	#[test]
	fn can_reduce_solution() {
		ExtBuilder::unsigned().build_and_execute(|| {
			roll_to_snapshot_created();
			let full_edges = BaseMiner::<Runtime>::mine_solution(Pages::get(), false)
				.unwrap()
				.solution_pages
				.iter()
				.fold(0, |acc, x| acc + x.edge_count());
			let reduced_edges = BaseMiner::<Runtime>::mine_solution(Pages::get(), true)
				.unwrap()
				.solution_pages
				.iter()
				.fold(0, |acc, x| acc + x.edge_count());

			assert!(reduced_edges < full_edges, "{} < {} not fulfilled", reduced_edges, full_edges);
		})
	}

	#[test]
	fn trim_backings_works() {
		ExtBuilder::unsigned()
			.max_backing_per_target(5)
			.voter_per_page(8)
			.build_and_execute(|| {
				// 10 and 40 are the default winners, we add a lot more votes to them.
				for i in 100..105 {
					VOTERS.with(|v| v.borrow_mut().push((i, i - 96, vec![10].try_into().unwrap())));
				}
				roll_to_snapshot_created();

				ensure_voters(3, 17);

				// now we let the miner mine something for us..
				let paged = mine_full_solution().unwrap();
				load_mock_signed_and_start(paged.clone());

				// this must be correct
				let supports = roll_to_full_verification();

				// 10 has no more than 5 backings, and from the new voters that we added in this
				// test, the most staked ones stayed (103, 104) and the rest trimmed.
				assert_eq!(
					supports,
					vec![
						// 1 backing for 10
						vec![(10, Support { total: 8, voters: vec![(104, 8)] })],
						// 2 backings for 10
						vec![
							(10, Support { total: 17, voters: vec![(10, 10), (103, 7)] }),
							(40, Support { total: 40, voters: vec![(40, 40)] })
						],
						// 20 backings for 10
						vec![
							(10, Support { total: 20, voters: vec![(1, 10), (8, 10)] }),
							(
								40,
								Support {
									total: 40,
									voters: vec![(2, 10), (3, 10), (4, 10), (6, 10)]
								}
							)
						]
					]
					.try_into_bounded_supports_vec()
					.unwrap()
				);
			})
	}
}

#[cfg(test)]
mod offchain_worker_miner {
	use crate::verifier::Verifier;
	use frame_support::traits::Hooks;
	use sp_runtime::offchain::storage_lock::{BlockAndTime, StorageLock};

	use super::*;
	use crate::mock::*;

	#[test]
	fn lock_prevents_frequent_execution() {
		let (mut ext, _) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let offchain_repeat = <Runtime as crate::unsigned::Config>::OffchainRepeat::get();

			// first execution -- okay.
			assert!(OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(25).is_ok());

			// next block: rejected.
			assert_noop!(
				OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(26),
				OffchainMinerError::Lock("recently executed.")
			);

			// allowed after `OFFCHAIN_REPEAT`
			assert!(OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat).into()
			)
			.is_ok());

			// a fork like situation: re-execute last 3.
			assert!(OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 3).into()
			)
			.is_err());
			assert!(OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 2).into()
			)
			.is_err());
			assert!(OffchainWorkerMiner::<Runtime>::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 1).into()
			)
			.is_err());
		})
	}

	#[test]
	fn lock_released_after_successful_execution() {
		// first, ensure that a successful execution releases the lock
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let guard = StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_LOCK);
			let last_block =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_LAST_BLOCK);

			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// initially, the lock is not set.
			assert!(guard.get::<bool>().unwrap().is_none());

			// a successful a-z execution.
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);

			// afterwards, the lock is not set either..
			assert!(guard.get::<bool>().unwrap().is_none());
			assert_eq!(last_block.get::<BlockNumber>().unwrap(), Some(25));
		});
	}

	#[test]
	fn lock_prevents_overlapping_execution() {
		// ensure that if the guard is in hold, a new execution is not allowed.
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// artificially set the value, as if another thread is mid-way.
			let mut lock = StorageLock::<BlockAndTime<System>>::with_block_deadline(
				OffchainWorkerMiner::<Runtime>::OFFCHAIN_LOCK,
				UnsignedPhase::get().saturated_into(),
			);
			let guard = lock.lock();

			// nothing submitted.
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 0);
			UnsignedPallet::offchain_worker(26);
			assert_eq!(pool.read().transactions.len(), 0);

			drop(guard);

			// 🎉 !
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
		});
	}

	#[test]
	fn initial_ocw_runs_and_saves_new_cache() {
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			let last_block =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_LAST_BLOCK);
			let cache =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_CACHED_CALL);

			assert_eq!(last_block.get::<BlockNumber>(), Ok(None));
			assert_eq!(cache.get::<crate::unsigned::Call<Runtime>>(), Ok(None));

			// creates, caches, submits without expecting previous cache value
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);

			assert_eq!(last_block.get::<BlockNumber>(), Ok(Some(25)));
			assert!(matches!(cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));
		})
	}

	#[test]
	fn ocw_pool_submission_works() {
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			roll_to_with_ocw(25, None);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));
			// OCW must have submitted now

			let encoded = pool.read().transactions[0].clone();
			let extrinsic: Extrinsic = codec::Decode::decode(&mut &*encoded).unwrap();
			let call = extrinsic.call;
			assert!(matches!(
				call,
				crate::mock::Call::UnsignedPallet(crate::unsigned::Call::submit_unsigned { .. })
			));
		})
	}

	#[test]
	fn resubmits_after_offchain_repeat() {
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let offchain_repeat = <Runtime as crate::unsigned::Config>::OffchainRepeat::get();
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned(25));

			assert!(OffchainWorkerMiner::<Runtime>::cached_solution().is_none());
			// creates, caches, submits without expecting previous cache value
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// attempts to resubmit the tx after the threshold has expired.
			UnsignedPallet::offchain_worker(25 + 1 + offchain_repeat);
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn regenerates_and_resubmits_after_offchain_repeat_if_no_cache() {
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let offchain_repeat = <Runtime as crate::unsigned::Config>::OffchainRepeat::get();
			roll_to(25);

			assert!(OffchainWorkerMiner::<Runtime>::cached_solution().is_none());
			// creates, caches, submits without expecting previous cache value.
			UnsignedPallet::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// remove the cached submitted tx.
			// this ensures that when the resubmit window rolls around, we're ready to regenerate
			// from scratch if necessary
			let mut call_cache =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));
			call_cache.clear();

			// attempts to resubmit the tx after the threshold has expired
			UnsignedPallet::offchain_worker(25 + 1 + offchain_repeat);
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn altering_snapshot_invalidates_solution_cache() {
		// by infeasible, we mean here that if the snapshot fingerprint has changed.
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let offchain_repeat = <Runtime as crate::unsigned::Config>::OffchainRepeat::get();
			roll_to_with_ocw(25, None);

			// something is submitted..
			assert_eq!(pool.read().transactions.len(), 1);
			pool.try_write().unwrap().transactions.clear();

			// ..and cached
			let call_cache =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));

			// now change the snapshot, ofc this is rare in reality. This makes the cached call
			// infeasible.
			assert_eq!(crate::Snapshot::<Runtime>::targets().unwrap(), vec![10, 20, 30, 40]);
			let pre_fingerprint = crate::Snapshot::<Runtime>::fingerprint();
			crate::Snapshot::<Runtime>::remove_target(0);
			let post_fingerprint = crate::Snapshot::<Runtime>::fingerprint();
			assert_eq!(crate::Snapshot::<Runtime>::targets().unwrap(), vec![20, 30, 40]);
			assert_ne!(pre_fingerprint, post_fingerprint);

			// now run ocw again
			roll_to_with_ocw(25 + offchain_repeat + 1, None);
			// nothing is submitted this time..
			assert_eq!(pool.read().transactions.len(), 0);
			// .. and the cache is gone.
			assert_eq!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(None));

			// upon the next run, we re-generate and submit something fresh again.
			roll_to_with_ocw(25 + offchain_repeat + offchain_repeat + 2, None);
			assert_eq!(pool.read().transactions.len(), 1);
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));
		})
	}

	#[test]
	fn wont_resubmit_if_weak_score() {
		// common case, if the score is weak, don't bother with anything, ideally check from the
		// logs that we don't run feasibility in this call path. Score check must come before.
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			let offchain_repeat = <Runtime as crate::unsigned::Config>::OffchainRepeat::get();
			// unfortunately there's no pretty way to run the ocw code such that it generates a
			// weak, but correct solution. We just write it to cache directly.

			roll_to_with_ocw(25, Some(pool.clone()));

			// something is submitted..
			assert_eq!(pool.read().transactions.len(), 1);

			// ..and cached
			let call_cache =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));

			// and replace it with something weak.
			let weak_solution = raw_paged_from_supports(
				vec![vec![(40, Support { total: 10, voters: vec![(3, 10)] })]],
				0,
			);
			let weak_call =
				crate::unsigned::Call::submit_unsigned { paged_solution: Box::new(weak_solution) };
			call_cache.set(&weak_call);

			// run again
			roll_to_with_ocw(25 + offchain_repeat + 1, Some(pool.clone()));
			// nothing is submitted this time..
			assert_eq!(pool.read().transactions.len(), 0);
			// .. and the cache IS STILL THERE!
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));
		})
	}

	#[test]
	fn ocw_submission_e2e_works() {
		let (mut ext, pool) = ExtBuilder::unsigned().build_offchainify();
		ext.execute_with_sanity_checks(|| {
			assert!(VerifierPallet::queued_score().is_none());
			roll_to_with_ocw(25 + 1, Some(pool.clone()));
			assert!(VerifierPallet::queued_score().is_some());

			// call is cached.
			let call_cache =
				StorageValueRef::persistent(&OffchainWorkerMiner::<Runtime>::OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<crate::unsigned::Call<Runtime>>(), Ok(Some(_))));

			// pool is empty
			assert_eq!(pool.read().transactions.len(), 0);
		})
	}

	#[test]
	fn will_not_mine_if_not_enough_winners() {
		// also see `trim_weight_too_much_makes_solution_invalid`.
		let (mut ext, _) = ExtBuilder::unsigned().desired_targets(77).build_offchainify();
		ext.execute_with_sanity_checks(|| {
			roll_to_unsigned_open();
			ensure_voters(3, 12);

			// beautiful errors, isn't it?
			assert_eq!(
				OffchainWorkerMiner::<Runtime>::mine_checked_call().unwrap_err(),
				OffchainMinerError::BaseMiner(MinerError::SnapshotIndependentChecks(
					crate::Error::<Runtime>::WrongWinnerCount
				))
			);
		});
	}
}
