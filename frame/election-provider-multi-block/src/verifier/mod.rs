// Only these items are public from this pallet.
pub use pallet::{Config, FeasibilityError, Pallet, Verifier};

/// This pallet does one thing: Once a solution is given to it, it will store it
/// `VerifyingSolution`, and it will start verifying it in the coming blocks.
#[frame_support::pallet]
mod pallet {
	use std::{collections::BTreeMap, fmt::Debug};

	use crate::{helpers, ReadySolutionPage, SolutionOf};
	use frame_election_provider_support::{ExtendedBalance, PageIndex, Support, Supports};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_npos_elections::{ElectionScore, EvaluateSupport, NposSolution};
	use sp_runtime::traits::{CheckedSub, One, SaturatedConversion};

	/// Errors that can happen in the feasibility check.
	#[derive(Debug, Eq, PartialEq)]
	pub enum FeasibilityError {
		/// Wrong number of winners presented.
		WrongWinnerCount,
		/// The snapshot is not available.
		///
		/// Kinda defensive: The pallet should technically never attempt to do a feasibility check
		/// when no snapshot is present.
		SnapshotUnavailable,
		/// Internal error from the election crate.
		NposElection(sp_npos_elections::Error),
		/// A vote is invalid.
		InvalidVote,
		/// A voter is invalid.
		InvalidVoter,
		/// A winner is invalid.
		InvalidWinner,
		/// The given score was invalid.
		InvalidScore,
		/// The provided round is incorrect.
		InvalidRound,
		/// Solution does not have a good enough score.
		ScoreTooLow,
	}

	impl From<sp_npos_elections::Error> for FeasibilityError {
		fn from(e: sp_npos_elections::Error) -> Self {
			FeasibilityError::NposElection(e)
		}
	}

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: crate::Config {
		/// Origin that can control this pallet. Note that any action taken by this origin (such)
		/// as providing an emergency solution is not checked. Thus, it must be a trusted origin.
		type ForceOrigin: EnsureOrigin<Self::Origin>;

		/// The minimum amount of improvement to the solution score that defines a solution as
		/// "better".
		#[pallet::constant]
		type SolutionImprovementThreshold: Get<sp_runtime::Perbill>;
	}

	/// The interface of something that cna be the verifier.
	pub trait Verifier {
		type Solution;
		type AccountId;
		/// This is the solution that we want to verify next, store it.
		///
		/// Can only accept a new solution if an ongoing verification is not ongoing. Use [`status`]
		/// to query this.
		fn store_unverified_solution(
			solution_pages: Vec<Self::Solution>,
			claimed_score: ElectionScore,
		) -> Result<(), ()>;

		/// Tell me if you have some queued solution read for use, with what score.
		fn queued_solution() -> Option<ElectionScore>;

		/// Check if this solution would have been sufficiently good, if it were to be a correct
		/// one.
		fn check_claimed_score(claimed_score: ElectionScore) -> bool;

		/// Tell me your status.
		///
		/// Returns `Some(x)` if there's a verification ongoing, and `x` more blocks are needed to
		/// finish it.
		/// Return `None` if there isn't a verification ongoing.
		fn verification_status() -> Option<PageIndex>;

		/// Clear everything, there's nothing else for you to do until further notice.
		fn kill();

		/// Get the best verified solution, if any.
		///
		/// It is the responsibility of the call site to call this function with all appropriate
		/// `page` arguments.
		fn get_verified_solution(page: PageIndex) -> Option<ReadySolutionPage<Self::AccountId>>;

		/// Perform the feasibility check of the given solution page.
		///
		/// This will not check the score and winner-count, since they can only be checked in
		/// context.
		///
		/// Corresponding snapshots are assumed to be available.
		fn feasibility_check_page(
			partial_solution: Self::Solution,
			page: PageIndex,
		) -> Result<Supports<Self::AccountId>, FeasibilityError>;
	}

	#[derive(Encode, Decode, Clone, Copy)]
	enum ValidSolution {
		X,
		Y,
	}

	impl Default for ValidSolution {
		fn default() -> Self {
			ValidSolution::Y
		}
	}

	impl ValidSolution {
		fn other(&self) -> Self {
			match *self {
				ValidSolution::X => ValidSolution::Y,
				ValidSolution::Y => ValidSolution::X,
			}
		}
	}

	// ---- All storage items about the verifying solution.
	struct VerifyingSolution<T: Config>(sp_std::marker::PhantomData<T>);
	impl<T: Config> VerifyingSolution<T> {
		/// Write a new verifying solution. Only works if no other one exists there.
		fn put(solution_pages: Vec<SolutionOf<T>>, claimed_score: ElectionScore) -> Result<(), ()> {
			if Self::exists() {
				return Err(())
			}
			for (page_index, page_solution) in solution_pages.into_iter().enumerate() {
				VerifyingSolutionStorage::<T>::insert(page_index as u8, page_solution);
			}
			VerifyingSolutionScore::<T>::put(claimed_score);
			VerifyingSolutionPage::<T>::put(T::Pages::get().saturating_sub(1));
			Ok(())
		}

		/// `true` if a solution is already exist in the verification queue.
		fn exists() -> bool {
			debug_assert!(
				VerifyingSolutionStorage::<T>::iter().count() == T::Pages::get() as usize
			);
			debug_assert!(VerifyingSolutionPage::<T>::exists());
			VerifyingSolutionScore::<T>::exists()
		}

		/// Remove all associated storage items.
		fn kill() {
			VerifyingSolutionStorage::<T>::remove_all(None);
			VerifyingSolutionPage::<T>::kill();
			VerifyingSolutionScore::<T>::kill();
		}

		fn get_score() -> Option<ElectionScore> {
			VerifyingSolutionScore::<T>::get()
		}

		fn get_page(index: PageIndex) -> Option<SolutionOf<T>> {
			VerifyingSolutionStorage::<T>::get(index)
		}

		fn current_page() -> Option<PageIndex> {
			VerifyingSolutionPage::<T>::get()
		}

		fn proceed_page() -> bool {
			if let Some(mut current) = VerifyingSolutionPage::<T>::get() {
				if let Some(x) = current.checked_sub(One::one()) {
					VerifyingSolutionPage::<T>::put(x);
					true
				} else {
					false
				}
			} else {
				false
			}
		}
	}

	/// A solution that should be verified next.
	#[pallet::storage]
	type VerifyingSolutionStorage<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, SolutionOf<T>>;
	/// Next page that should be verified.
	#[pallet::storage]
	type VerifyingSolutionPage<T: Config> = StorageValue<_, PageIndex>;
	/// The claimed score of the current verifying solution
	#[pallet::storage]
	type VerifyingSolutionScore<T: Config> = StorageValue<_, ElectionScore>;

	// ---- All storage items about the verifying solution.
	struct QueuedSolution<T: Config>(sp_std::marker::PhantomData<T>);
	impl<T: Config> QueuedSolution<T> {
		/// Return the `score` and `winner_count` of verifying solution.
		///
		/// Assumes that all the corresponding pages of `QueuedSolutionBackings` exist, then it
		/// computes the final score of the solution that is currently at the end of its
		/// verification process.
		///
		/// This solution corresponds to whatever is stored in the INVALID variant of
		/// `QueuedSolution`. Recall that the score of this solution is not yet verified, so it
		/// should never become `valid`.
		fn final_score() -> (ElectionScore, u32) {
			// TODO: this could be made into a proper error.
			debug_assert_eq!(QueuedSolutionBackings::<T>::iter().count() as u8, T::Pages::get());

			let mut total_supports: BTreeMap<T::AccountId, ExtendedBalance> = Default::default();
			QueuedSolutionBackings::<T>::iter()
				.map(|(_page, backings)| backings)
				.flatten()
				.for_each(|(who, backing)| {
					let mut entry = total_supports.entry(who).or_default();
					*entry = entry.saturating_add(backing);
				});
			let mock_supports = total_supports
				.into_iter()
				.map(|(who, total)| (who, total.into()))
				.map(|(who, total)| (who, Support { total, ..Default::default() }));
			let count = mock_supports.len() as u32;

			(mock_supports.evaluate(), count)
		}

		/// Finalize a correct solution.
		///
		/// Should be called at the end of a verification process, once we are sure that a certain
		/// solution is 100% correct. It stores its score, flips the pointer to it being the current
		/// best one, and clears all the backings.
		///
		/// NOTE: we don't check if this is a better score, the call site must ensure that.
		fn finalize_correct(score: ElectionScore) {
			QueuedValidVariant::<T>::mutate(|v| *v = v.other());
			QueuedSolutionScore::<T>::put(score);
			QueuedSolutionBackings::<T>::remove_all(None);
		}

		/// Clear all relevant information of an invalid solution.
		///
		/// Should be called at any step, if we encounter an issue which makes the solution
		/// infeasible.
		fn clear_incorrect() {
			let valid = QueuedValidVariant::<T>::get();
			let invalid = valid.other();
			match invalid {
				ValidSolution::X => QueuedSolutionX::<T>::remove_all(None),
				ValidSolution::Y => QueuedSolutionY::<T>::remove_all(None),
			};
			QueuedSolutionBackings::<T>::remove_all(None);
			// defensive-only: this should have not existed anyway.
			debug_assert!(!QueuedSolutionScore::<T>::exists());
			QueuedSolutionScore::<T>::kill();
			// NOTE: we don't flip the variant, this is still the empty slot.
		}

		/// Write a single page of a valid solution into the `valid` variant of the storage.
		///
		/// This should only be called once we are sure that this particular page is 100% correct.
		fn write_valid_page(page: PageIndex, supports: Supports<T::AccountId>) {
			let valid = QueuedValidVariant::<T>::get();

			let backings = supports.iter().map(|(x, s)| (x, s.total)).collect::<Vec<_>>();
			QueuedSolutionBackings::<T>::insert(page, backings);

			match valid {
				ValidSolution::X => QueuedSolutionX::<T>::insert(page, supports),
				ValidSolution::Y => QueuedSolutionY::<T>::insert(page, supports),
			}
		}

		/// Clear all storage items.
		///
		/// Should only be called once everything is done.
		fn kill() {
			QueuedSolutionX::<T>::remove_all(None);
			QueuedSolutionY::<T>::remove_all(None);
			QueuedValidVariant::<T>::kill();
			QueuedSolutionBackings::<T>::remove_all(None);
			QueuedSolutionScore::<T>::kill();
		}

		/// The score of the current best solution, if any.
		fn queued_solution() -> Option<ElectionScore> {
			QueuedSolutionScore::<T>::get()
		}

		fn get_verified_solution(page: PageIndex) -> Option<ReadySolutionPage<T::AccountId>> {
			let valid = QueuedValidVariant::<T>::get();

			match valid {
				ValidSolution::X => QueuedSolutionX::<T>::get(page),
				ValidSolution::Y => QueuedSolutionY::<T>::get(page),
			}
			.map(|supports| ReadySolutionPage { supports, ..Default::default() })
			// TODO: seemingly there's no point in storing this score, dissolve ReadySolutionPage.
		}
	}

	/// The `X` variant of the current queued solution. Might be the valid one or not.
	///
	/// The two variants of this storage item is to avoid the need of copying. Recall that once a
	/// `VerifyingSolution` is being processed, it needs to write its partial supports *somewhere*.
	/// Writing theses supports on top of a *good* queued supports is wrong, since we might bail.
	/// Writing them to a bugger and copying at the ned is slightly better, but expensive. This flag
	/// system is best of both worlds.
	#[pallet::storage]
	type QueuedSolutionX<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, Supports<T::AccountId>>;
	#[pallet::storage]
	/// The `Y` variant of the current queued solution. Might be the valid one or not.
	type QueuedSolutionY<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, Supports<T::AccountId>>;
	/// Pointer to the variant of [`QueuedSolutionX`] or [`QueuedSolutionY`] that is currently
	/// valid.
	#[pallet::storage]
	type QueuedValidVariant<T: Config> = StorageValue<_, ValidSolution, ValueQuery>;
	// This only ever lives for the `invalid` variant.
	#[pallet::storage]
	type QueuedSolutionBackings<T: Config> =
		StorageMap<_, Twox64Concat, PageIndex, Vec<(T::AccountId, ExtendedBalance)>>;
	// This only ever lives for the `valid` variant.
	#[pallet::storage]
	type QueuedSolutionScore<T: Config> = StorageValue<_, ElectionScore>;

	/// The minimum score that each 'untrusted' solution must attain in order to be considered
	/// feasible.
	///
	/// Can be set via `set_minimum_untrusted_score`.
	#[pallet::storage]
	#[pallet::getter(fn minimum_untrusted_score)]
	pub type MinimumUntrustedScore<T: Config> = StorageValue<_, ElectionScore>;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set a new value for `MinimumUntrustedScore`.
		///
		/// Dispatch origin must be aligned with `T::ForceOrigin`.
		///
		/// This check can be turned off by setting the value to `None`.
		#[pallet::weight(T::DbWeight::get().writes(1))]
		pub fn set_minimum_untrusted_score(
			origin: OriginFor<T>,
			maybe_next_score: Option<ElectionScore>,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;
			<MinimumUntrustedScore<T>>::set(maybe_next_score);
			Ok(())
		}

		/// Set a solution in the queue, to be handed out to the client of this pallet in the next
		/// call to [`Verifier::get_verified_solution`].
		///
		/// This can only be set by `T::ForceOrigin`, and only when the phase is `Emergency`.
		///
		/// The solution is not checked for any feasibility and is assumed to be trustworthy, as any
		/// feasibility check itself can in principle cause the election process to fail (due to
		/// memory/weight constrains).
		#[pallet::weight(T::DbWeight::get().reads_writes(1, 1))]
		pub fn set_emergency_solution(
			origin: OriginFor<T>,
			paged_supports: Vec<Supports<T::AccountId>>,
		) -> DispatchResult {
			T::ForceOrigin::ensure_origin(origin)?;

			ensure!(
				crate::Pallet::<T>::current_phase().is_emergency(),
				<crate::Error<T>>::CallNotAllowed
			);
			ensure!(
				paged_supports.len().saturated_into::<PageIndex>() == T::Pages::get(),
				<crate::Error<T>>::WrongPageCount,
			);

			// TODO: something like enumerate for Vec<T> that pagify it.
			for (page_index, supports) in paged_supports.iter().enumerate() {
				QueuedSolution::<T>::write_valid_page(page_index as PageIndex, supports.to_vec());
			}

			Ok(())
		}
	}

	impl<T: Config> Verifier for Pallet<T> {
		type Solution = SolutionOf<T>;
		type AccountId = T::AccountId;

		fn store_unverified_solution(
			solution_pages: Vec<Self::Solution>,
			claimed_score: ElectionScore,
		) -> Result<(), ()> {
			VerifyingSolution::<T>::put(solution_pages, claimed_score)
		}

		fn check_claimed_score(claimed_score: ElectionScore) -> bool {
			Self::ensure_correct_final_score_quality(claimed_score).is_ok()
		}

		fn queued_solution() -> Option<ElectionScore> {
			QueuedSolution::<T>::queued_solution()
		}

		fn verification_status() -> Option<PageIndex> {
			todo!()
		}

		fn kill() {
			VerifyingSolution::<T>::kill();
			QueuedSolution::<T>::kill();
		}

		fn get_verified_solution(page: PageIndex) -> Option<ReadySolutionPage<Self::AccountId>> {
			QueuedSolution::<T>::get_verified_solution(page)
		}

		fn feasibility_check_page(
			partial_solution: Self::Solution,
			page: PageIndex,
		) -> Result<Supports<Self::AccountId>, FeasibilityError> {
			Self::feasibility_check_page(partial_solution, page)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			if let Some(current_page) = VerifyingSolution::<T>::current_page() {
				let solution_page = VerifyingSolution::<T>::get_page(current_page).unwrap();
				let maybe_ready = Self::feasibility_check_page(solution_page, current_page);

				if let Ok(ready) = maybe_ready {
					// this page was noice; write it and check-in the next page.
					QueuedSolution::<T>::write_valid_page(current_page, ready);
					let has_more_pages = VerifyingSolution::<T>::proceed_page();

					if !has_more_pages {
						// this was the last page, we can't gp any further.
						let (final_score, winner_count) = QueuedSolution::<T>::final_score();
						let claimed_score = VerifyingSolution::<T>::get_score().unwrap();
						let desired_targets = crate::Pallet::<T>::desired_targets().unwrap();
						if final_score == claimed_score &&
							Self::ensure_correct_final_score_quality(final_score).is_ok() &&
							winner_count == desired_targets
						{
							// all good, finalize this solution
							VerifyingSolution::<T>::kill();
							QueuedSolution::<T>::finalize_correct(final_score);
						} else {
							VerifyingSolution::<T>::kill();
							QueuedSolution::<T>::clear_incorrect();
						}
					}
				} else {
					VerifyingSolution::<T>::kill();
					QueuedSolution::<T>::clear_incorrect();
				}
			}

			0
		}
	}

	// private functions
	impl<T: Config> Pallet<T> {
		/// Once we know that a claimed score is correct, now we check it further to be:
		///
		/// 1. more than a potentially queued solution
		/// 2. more than the minimum untrusted score
		fn ensure_correct_final_score_quality(
			correct_score: ElectionScore,
		) -> Result<(), FeasibilityError> {
			ensure!(
				<Self as Verifier>::queued_solution().map_or(true, |best_score| {
					sp_npos_elections::is_score_better::<sp_runtime::Perbill>(
						correct_score,
						best_score,
						T::SolutionImprovementThreshold::get(),
					)
				}),
				FeasibilityError::ScoreTooLow,
			);

			ensure!(
				Self::minimum_untrusted_score().map_or(true, |min_score| {
					sp_npos_elections::is_score_better(
						correct_score,
						min_score,
						sp_runtime::Perbill::zero(),
					)
				}),
				FeasibilityError::ScoreTooLow
			);

			Ok(())
		}

		fn feasibility_check_page(
			partial_solution: SolutionOf<T>,
			page: PageIndex,
		) -> Result<Supports<T::AccountId>, FeasibilityError> {
			// Read the corresponding snapshots.
			let snapshot_targets = crate::Pallet::<T>::paged_target_snapshot(0)
				.ok_or(FeasibilityError::SnapshotUnavailable)?;
			let snapshot_voters = crate::Pallet::<T>::paged_voter_snapshot(page)
				.ok_or(FeasibilityError::SnapshotUnavailable)?;

			// ----- Start building. First, we need some closures.
			let cache = helpers::generate_voter_cache::<T>(&snapshot_voters);
			let voter_at = helpers::voter_at_fn::<T>(&snapshot_voters);
			let target_at = helpers::target_at_fn::<T>(&snapshot_targets);
			let voter_index = helpers::voter_index_fn_usize::<T>(&cache);

			// First, make sure that all the winners are sane.
			let winners = partial_solution.unique_targets();
			let winners = winners
				.into_iter()
				.map(|i| target_at(i).ok_or(FeasibilityError::InvalidWinner))
				.collect::<Result<Vec<T::AccountId>, FeasibilityError>>()?;

			// Then convert solution -> assignment. This will fail if any of the indices are
			// gibberish.
			let assignments = partial_solution
				.into_assignment(voter_at, target_at)
				.map_err::<FeasibilityError, _>(Into::into)?;

			// Ensure that assignments are all correct.
			let _ = assignments
				.iter()
				.map(|ref assignment| {
					// Check that assignment.who is actually a voter (defensive-only). NOTE: while
					// using the index map from `voter_index` is better than a blind linear search,
					// this *still* has room for optimization. Note that we had the index when we
					// did `solution -> assignment` and we lost it. Ideal is to keep the index
					// around.

					// Defensive-only: must exist in the snapshot.
					let snapshot_index =
						voter_index(&assignment.who).ok_or(FeasibilityError::InvalidVoter)?;
					// Defensive-only: index comes from the snapshot, must exist.
					let (_voter, _stake, targets) = snapshot_voters
						.get(snapshot_index)
						.ok_or(FeasibilityError::InvalidVoter)?;

					// Check that all of the targets are valid based on the snapshot.
					if assignment.distribution.iter().any(|(t, _)| !targets.contains(t)) {
						return Err(FeasibilityError::InvalidVote)
					}
					Ok(())
				})
				.collect::<Result<(), FeasibilityError>>()?;

			// ----- Start building support. First, we need one more closure.
			let stake_of = helpers::stake_of_fn::<T>(&snapshot_voters, &cache);

			// This might fail if the normalization fails. Very unlikely. See `integrity_test`.
			let staked_assignments =
				sp_npos_elections::assignment_ratio_to_staked_normalized(assignments, stake_of)
					.map_err::<FeasibilityError, _>(Into::into)?;

			// This might fail if one of the voter edges is pointing to a non-winner, which is not
			// really possible anymore because all the winners come from the same
			// `partial_solution`.
			let supports = sp_npos_elections::to_supports(&winners, &staked_assignments)
				.map_err::<FeasibilityError, _>(Into::into)?;

			Ok(supports)
		}
	}
}

#[cfg(test)]
mod feasibility_check {
	use super::*;
	use crate::mock::{
		create_all_snapshots, raw_paged_solution, roll_to, EpochLength, ExtBuilder, MultiPhase,
		Runtime, SignedPhase, TargetIndex, UnsignedPhase, VerifierPallet, VoterIndex,
	};
	use frame_support::{assert_noop, assert_ok};

	#[test]
	fn missing_snapshot() {
		ExtBuilder::default().build_and_execute(|| {
			// create snapshot just so that we can create a solution..
			create_all_snapshots();
			let paged = raw_paged_solution();

			// ..remove the only page of the target snapshot.
			<crate::PagedTargetSnapshot<Runtime>>::remove(0);

			assert_noop!(
				VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0),
				FeasibilityError::SnapshotUnavailable
			);
		});

		ExtBuilder::default().pages(2).build_and_execute(|| {
			// create snapshot just so that we can create a solution..
			create_all_snapshots();
			let paged = raw_paged_solution();

			// ..remove just one of the pages of voter snapshot that is relevant.
			<crate::PagedVoterSnapshot<Runtime>>::remove(0);

			assert_noop!(
				VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0),
				FeasibilityError::SnapshotUnavailable
			);
		});

		ExtBuilder::default().pages(2).build_and_execute(|| {
			// create snapshot just so that we can create a solution..
			create_all_snapshots();
			let paged = raw_paged_solution();

			// ..removing this page is not important.
			<crate::PagedVoterSnapshot<Runtime>>::remove(1);

			assert_ok!(VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0));
		});

		ExtBuilder::default().pages(2).build_and_execute(|| {
			// create snapshot just so that we can create a solution..
			create_all_snapshots();
			let paged = raw_paged_solution();

			// `DesiredTargets` is not checked here.
			<crate::DesiredTargets<Runtime>>::kill();

			assert_ok!(VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0));
		});
	}

	#[test]
	fn winner_indices_single_page() {
		ExtBuilder::default().pages(1).desired_targets(2).build_and_execute(|| {
			create_all_snapshots();
			let mut paged = raw_paged_solution();
			assert_eq!(MultiPhase::paged_target_snapshot(0).unwrap().len(), 4);
			// ----------------------------------------------------^^ valid range is [0..3].

			dbg!(&paged);
			// Swap all votes from 3 to 4.
			paged.solution_pages[0]
				.votes1
				.iter_mut()
				.filter(|(_, t)| *t == TargetIndex::from(3u16))
				.for_each(|(_, t)| *t += 1);
			paged.solution_pages[0].votes2.iter_mut().for_each(|(_, [(t0, _)], t1)| {
				if *t0 == TargetIndex::from(3u16) {
					*t0 += 1
				};
				if *t1 == TargetIndex::from(3u16) {
					*t1 += 1
				};
			});
			assert_noop!(
				VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0),
				FeasibilityError::InvalidWinner
			);
		})
	}

	#[test]
	fn voter_indices_per_page() {
		ExtBuilder::default().pages(1).desired_targets(2).build_and_execute(|| {
			create_all_snapshots();
			let mut paged = raw_paged_solution();

			assert_eq!(MultiPhase::paged_voter_snapshot(0).unwrap().len(), 12);
			// ------------------------------------------------^^ valid range is [0..11] in page 0.

			dbg!(&paged);
			// Check that there is an index 11 in votes1, and flip to 12.
			assert!(
				paged.solution_pages[0]
					.votes1
					.iter_mut()
					.filter(|(v, _)| *v == VoterIndex::from(11u32))
					.map(|(v, _)| *v = 12)
					.count() > 0
			);
			assert_noop!(
				VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0),
				FeasibilityError::NposElection(sp_npos_elections::Error::SolutionInvalidIndex),
			);
		})
	}

	#[test]
	fn voter_votes() {
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			create_all_snapshots();
			let mut paged = raw_paged_solution();

			// First, check that voter at index 11 (40) actually voted for 3 (40) -- this is self
			// vote. Then, change the vote to 2 (30).

			assert_eq!(
				paged.solution_pages[0]
					.votes1
					.iter_mut()
					.filter(|(v, t)| *v == 11 && *t == 3)
					.map(|(_, t)| *t = 2)
					.count(),
				1,
			);
			assert_noop!(
				VerifierPallet::feasibility_check_page(paged.solution_pages[0].clone(), 0),
				FeasibilityError::InvalidVote,
			);
		})
	}

	#[test]
	fn desired_targets() {
		ExtBuilder::default().desired_targets(8).build_and_execute(|| {
			create_all_snapshots();
			let raw = raw_paged_solution();
			todo!()
		})
	}

	#[test]
	fn score() {
		ExtBuilder::default().desired_targets(2).build_and_execute(|| {
			create_all_snapshots();
			let raw = raw_paged_solution();
			todo!()
		})
	}
}
