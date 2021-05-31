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

//! The signed phase implementation.

use crate::{
	CompactOf, Config, ElectionCompute, Pallet, RawSolution, ReadySolution, SolutionOrSnapshotSize,
	Weight, WeightInfo, QueuedSolution, SignedSubmissions,
};
use codec::{Encode, Decode, HasCompact};
use frame_support::traits::{Currency, Get, OnUnbalanced, ReservableCurrency};
use sp_arithmetic::traits::SaturatedConversion;
use sp_npos_elections::{is_score_better, CompactSolution};
use sp_runtime::{Perbill, RuntimeDebug, traits::{Saturating, Zero}};
use sp_std::{cmp::Ordering, vec::Vec};

/// A raw, unchecked signed submission.
///
/// This is just a wrapper around [`RawSolution`] and some additional info.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct SignedSubmission<AccountId, Balance: HasCompact, CompactSolution> {
	/// Who submitted this solution.
	pub who: AccountId,
	/// The deposit reserved for storing this solution.
	pub deposit: Balance,
	/// The reward that should be given to this solution, if chosen the as the final one.
	pub reward: Balance,
	/// The raw solution itself.
	pub solution: RawSolution<CompactSolution>,
}

<<<<<<< HEAD
impl<AccountId, Balance, CompactSolution> Ord
	for SignedSubmission<AccountId, Balance, CompactSolution>
where
	AccountId: Ord,
	Balance: Ord + HasCompact,
	CompactSolution: Ord,
{
	fn cmp(&self, other: &Self) -> Ordering {
		self.solution
			.score
			.cmp(&other.solution.score)
			.and_then(|| self.solution.cmp(&other.solution))
			.and_then(|| self.deposit.cmp(&other.deposit))
			.and_then(|| self.reward.cmp(&other.reward))
			.and_then(|| self.who.cmp(&other.who))
	}
}

impl<AccountId, Balance, CompactSolution> PartialOrd
	for SignedSubmission<AccountId, Balance, CompactSolution>
where
	AccountId: Ord,
	Balance: Ord + HasCompact,
	CompactSolution: Ord,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

=======
>>>>>>> origin/kiz-election-provider-3-signed-phase
pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::PositiveImbalance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

impl<T: Config> Pallet<T> {
	/// Finish the signed phase. Process the signed submissions from best to worse until a valid one
	/// is found, rewarding the best one and slashing the invalid ones along the way.
	///
	/// Returns true if we have a good solution in the signed phase.
	///
	/// This drains the [`SignedSubmissions`], potentially storing the best valid one in
	/// [`QueuedSolution`].
	pub fn finalize_signed_phase() -> (bool, Weight) {
		let mut all_submissions: Vec<SignedSubmission<_, _, _>> = <SignedSubmissions<T>>::take();
		let mut found_solution = false;
		let mut weight = T::DbWeight::get().reads(1);

		// Reverse the ordering of submissions: previously it was ordered such that high-scoring
		// solutions have low indices. Now, the code flows more cleanly if high-scoring solutions
		// have high indices.
		all_submissions.reverse();

		while let Some(best) = all_submissions.pop() {
			let SignedSubmission { solution, who, deposit, reward } = best;
			let active_voters = solution.compact.voter_count() as u32;
			let feasibility_weight = {
				// defensive only: at the end of signed phase, snapshot will exits.
				let SolutionOrSnapshotSize { voters, targets } =
					Self::snapshot_metadata().unwrap_or_default();
				let desired_targets = Self::desired_targets().unwrap_or_default();
				T::WeightInfo::feasibility_check(
					voters,
					targets,
					active_voters,
					desired_targets,
				)
			};
			// the feasibility check itself has some weight
			weight = weight.saturating_add(feasibility_weight);
			match Self::feasibility_check(solution, ElectionCompute::Signed) {
				Ok(ready_solution) => {
					Self::finalize_signed_phase_accept_solution(
						ready_solution,
						&who,
						deposit,
						reward,
					);
					found_solution = true;

					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_accept_solution());
					break;
				}
				Err(_) => {
					Self::finalize_signed_phase_reject_solution(&who, deposit);
					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_reject_solution());
				}
			}
		}

		// Any unprocessed solution is pointless to even consider. Feasible or malicious,
		// they didn't end up being used. Unreserve the bonds.
		for not_processed in all_submissions {
			let SignedSubmission { who, deposit, .. } = not_processed;
			let _remaining = T::Currency::unreserve(&who, deposit);
			weight = weight.saturating_add(T::DbWeight::get().writes(1));
			debug_assert!(_remaining.is_zero());
		};

		(found_solution, weight)
	}

	/// Helper function for the case where a solution is accepted in the signed phase.
	///
	/// Extracted to facilitate with weight calculation.
	///
	/// Infallible
	pub fn finalize_signed_phase_accept_solution(
		ready_solution: ReadySolution<T::AccountId>,
		who: &T::AccountId,
		deposit: BalanceOf<T>,
		reward: BalanceOf<T>,
	) {
		// write this ready solution.
		<QueuedSolution<T>>::put(ready_solution);

		// unreserve deposit.
		let _remaining = T::Currency::unreserve(who, deposit);
		debug_assert!(_remaining.is_zero());

		// Reward.
		let positive_imbalance = T::Currency::deposit_creating(who, reward);
		T::RewardHandler::on_unbalanced(positive_imbalance);
	}

	/// Helper function for the case where a solution is accepted in the rejected phase.
	///
	/// Extracted to facilitate with weight calculation.
	///
	/// Infallible
	pub fn finalize_signed_phase_reject_solution(who: &T::AccountId, deposit: BalanceOf<T>) {
		let (negative_imbalance, _remaining) = T::Currency::slash_reserved(who, deposit);
		debug_assert!(_remaining.is_zero());
		T::SlashHandler::on_unbalanced(negative_imbalance);
	}

	/// Insert a solution into the queue while maintaining an ordering by solution quality.
	///
	/// Solutions are ordered in reverse: strong solutions have low indices.
	///
	/// If insertion was successful, `Some(index)` is returned where index is the
	/// index of the newly inserted item.
	///
	/// Note: this function maintains the invariant that `queue.len() <= T::SignedMaxSubmissions`.
	/// In the event that insertion would violate that invariant, the weakest element is dropped.
	///
	/// Invariant: The returned index is always a valid index in `queue` and can safely be used to
	/// inspect the newly inserted element.
	pub fn insert_submission(
		who: &T::AccountId,
		queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
		solution: RawSolution<CompactOf<T>>,
		size: SolutionOrSnapshotSize,
	) -> Option<usize> {
		// Let's ensure that our input is valid.
		let max_submissions = T::SignedMaxSubmissions::get();
		debug_assert!(queue.len() as u32 <= max_submissions);

		let threshold = T::SolutionImprovementThreshold::get();
		// this insertion logic is a bit unusual in that a new solution which beats an existing
		// solution by less than the threshold is sorted as "greater" than the existing solution.
		// this means that the produced ordering depends on the order of insertion, and that
		// attempts to produce a total ordering using this comparitor are highly unstable.
		//
		// this ordering prioritizes earlier solutions over slightly better later ones.
		let insertion_position = queue.binary_search_by(|s| {
			if is_score_better::<Perbill>(
				solution.score,
				s.solution.score,
				threshold,
			) {
				Ordering::Greater
			} else {
				Ordering::Less
			}
		}).expect_err("comparitor function never returns Ordering::Equal; qed");

		// if this solution is the worst one so far and the queue is full, don't insert
		if insertion_position == queue.len() && queue.len() as u32 >= max_submissions {
			return None;
		}

		// add to the designated spot. If the length is too much, remove one.
		let reward = T::SignedRewardBase::get();
		let deposit = Self::deposit_for(&solution, size);
		let submission =
			SignedSubmission { who: who.clone(), deposit, reward, solution };
		queue.insert(insertion_position, submission);

		// Remove the weakest if queue is overflowing.
		// This doesn't adjust insertion_position: in the event that it might have, we'd have short-
		// circuited above.
		if queue.len() as u32 > max_submissions {
			if let Some(SignedSubmission { who, deposit, .. }) = queue.pop() {
				let _remainder = T::Currency::unreserve(&who, deposit);
				debug_assert!(_remainder.is_zero());
			}
		}
		debug_assert!(queue.len() as u32 <= max_submissions);
		Some(insertion_position)
	}

	/// The feasibility weight of the given raw solution.
	pub fn feasibility_weight_of(
		solution: &RawSolution<CompactOf<T>>,
		size: SolutionOrSnapshotSize,
	) -> Weight {
		T::WeightInfo::feasibility_check(
			size.voters,
			size.targets,
			solution.compact.voter_count() as u32,
			solution.compact.unique_targets().len() as u32,
		)
	}

	/// Collect sufficient deposit to store this solution this chain.
	///
	/// The deposit is composed of 3 main elements:
	///
	/// 1. base deposit, fixed for all submissions.
	/// 2. a per-byte deposit, for renting the state usage.
	/// 3. a per-weight deposit, for the potential weight usage in an upcoming on_initialize
	pub fn deposit_for(
		solution: &RawSolution<CompactOf<T>>,
		size: SolutionOrSnapshotSize,
	) -> BalanceOf<T> {
		let encoded_len: u32 = solution.encoded_size().saturated_into();
		let encoded_len: BalanceOf<T> = encoded_len.into();
		let feasibility_weight = Self::feasibility_weight_of(solution, size);

		let len_deposit = T::SignedDepositByte::get().saturating_mul(encoded_len);
		let weight_deposit = T::SignedDepositWeight::get().saturating_mul(feasibility_weight.saturated_into());

		T::SignedDepositBase::get().saturating_add(len_deposit).saturating_add(weight_deposit)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		Phase, Error,
		mock::{
			balances, ExtBuilder, MultiPhase, Origin, raw_solution, roll_to, Runtime,
			SignedMaxSubmissions, SignedMaxWeight,
		},
	};
	use frame_support::{dispatch::DispatchResult, assert_noop, assert_ok};

	fn submit_with_witness(
		origin: Origin,
		solution: RawSolution<CompactOf<Runtime>>,
	) -> DispatchResult {
		MultiPhase::submit(origin, solution, MultiPhase::signed_submissions().len() as u32)
	}

	#[test]
	fn cannot_submit_too_early() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(2);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// create a temp snapshot only for this test.
			MultiPhase::create_snapshot().unwrap();
			let solution = raw_solution();

			assert_noop!(
				submit_with_witness(Origin::signed(10), solution),
				Error::<Runtime>::PreDispatchEarlySubmission,
			);
		})
	}

	#[test]
	fn wrong_witness_fails() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			// submit this once correctly
			assert_ok!(submit_with_witness(Origin::signed(99), solution.clone()));
			assert_eq!(MultiPhase::signed_submissions().len(), 1);

			// now try and cheat by passing a lower queue length
			assert_noop!(
				MultiPhase::submit(Origin::signed(99), solution, 0),
				Error::<Runtime>::SignedInvalidWitness,
			);
		})
	}

	#[test]
	fn should_pay_deposit() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(submit_with_witness(Origin::signed(99), solution));

			assert_eq!(balances(&99), (95, 5));
			assert_eq!(MultiPhase::signed_submissions().first().unwrap().deposit, 5);
		})
	}

	#[test]
	fn good_solution_is_rewarded() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(MultiPhase::finalize_signed_phase().0);
			assert_eq!(balances(&99), (100 + 7, 0));
		})
	}

	#[test]
	fn bad_solution_is_slashed() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			// make the solution invalid.
			solution.score[0] += 1;

			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			// no good solution was stored.
			assert!(!MultiPhase::finalize_signed_phase().0);
			// and the bond is gone.
			assert_eq!(balances(&99), (95, 0));
		})
	}

	#[test]
	fn suppressed_solution_gets_bond_back() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));

			// submit as correct.
			assert_ok!(submit_with_witness(Origin::signed(99), solution.clone()));

			// make the solution invalid and weaker.
			solution.score[0] -= 1;
			assert_ok!(submit_with_witness(Origin::signed(999), solution));
			assert_eq!(balances(&99), (95, 5));
			assert_eq!(balances(&999), (95, 5));

			// _some_ good solution was stored.
			assert!(MultiPhase::finalize_signed_phase().0);

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7, 0));
			// 999 gets everything back.
			assert_eq!(balances(&999), (100, 0));
		})
	}

	#[test]
	fn cannot_submit_worse_with_full_queue() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(submit_with_witness(Origin::signed(99), solution));
			}

			// weaker.
			let solution = RawSolution { score: [4, 0, 0], ..Default::default() };

			assert_noop!(
				submit_with_witness(Origin::signed(99), solution),
				Error::<Runtime>::SignedQueueFull,
			);
		})
	}

	#[test]
	fn weakest_is_removed_if_better_provided() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(submit_with_witness(Origin::signed(99), solution));
			}

			assert_eq!(
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![9, 8, 7, 6, 5]
			);

			// better.
			let solution = RawSolution { score: [20, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));

			// the one with score 5 was rejected, the new one inserted.
			assert_eq!(
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![20, 9, 8, 7, 6]
			);
		})
	}

	#[test]
	fn weakest_is_removed_if_better_provided_wont_remove_self() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for s in 1..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(submit_with_witness(Origin::signed(99), solution));
			}

			let solution = RawSolution { score: [4, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));

			assert_eq!(
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![9, 8, 7, 6, 4],
			);

			// better.
			let solution = RawSolution { score: [5, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));

			// the one with score 5 was rejected, the new one inserted.
			assert_eq!(
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![9, 8, 7, 6, 5],
			);
		})
	}

	#[test]
	fn early_ejected_solution_gets_bond_back() {
		ExtBuilder::default().signed_deposit(2, 0, 0).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution { score: [(5 + s).into(), 0, 0], ..Default::default() };
				assert_ok!(submit_with_witness(Origin::signed(99), solution));
			}

			assert_eq!(balances(&99).1, 2 * 5);
			assert_eq!(balances(&999).1, 0);

			// better.
			let solution = RawSolution { score: [20, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(999), solution));

			// got one bond back.
			assert_eq!(balances(&99).1, 2 * 4);
			assert_eq!(balances(&999).1, 2);
		})
	}

	#[test]
	fn equally_good_solution_is_not_accepted() {
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for i in 0..SignedMaxSubmissions::get() {
				let solution = RawSolution { score: [(5 + i).into(), 0, 0], ..Default::default() };
				assert_ok!(submit_with_witness(Origin::signed(99), solution));
			}
			assert_eq!(
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![7, 6, 5]
			);

			// 5 is not accepted. This will only cause processing with no benefit.
			let solution = RawSolution { score: [5, 0, 0], ..Default::default() };
			assert_noop!(
				submit_with_witness(Origin::signed(99), solution),
				Error::<Runtime>::SignedQueueFull,
			);
		})
	}

	#[test]
	fn solutions_are_always_sorted() {
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			let scores = || {
				MultiPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>()
			};

			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = RawSolution { score: [5, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![5]);

			let solution = RawSolution { score: [8, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![8, 5]);

			let solution = RawSolution { score: [3, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![8, 5, 3]);

			let solution = RawSolution { score: [6, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![8, 6, 5]);

			let solution = RawSolution { score: [6, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![8, 6, 6]);

			let solution = RawSolution { score: [10, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![10, 8, 6]);

			let solution = RawSolution { score: [12, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![12, 10, 8]);
		})
	}

	#[test]
	fn all_in_one_signed_submission_scenario() {
		// a combination of:
		// - good_solution_is_rewarded
		// - bad_solution_is_slashed
		// - suppressed_solution_gets_bond_back
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));
			assert_eq!(balances(&9999), (100, 0));
			let mut solution = raw_solution();

			// submit a correct one.
			assert_ok!(submit_with_witness(Origin::signed(99), solution.clone()));

			// make the solution invalidly better and submit. This ought to be slashed.
			solution.score[0] += 1;
			assert_ok!(submit_with_witness(Origin::signed(999), solution.clone()));

			// make the solution invalidly worse and submit. This ought to be suppressed and
			// returned.
			solution.score[0] -= 1;
			assert_ok!(submit_with_witness(Origin::signed(9999), solution));

			assert_eq!(
				MultiPhase::signed_submissions().iter().map(|x| x.who).collect::<Vec<_>>(),
				vec![999, 99, 9999]
			);

			// _some_ good solution was stored.
			assert!(MultiPhase::finalize_signed_phase().0);

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7, 0));
			// 999 is slashed.
			assert_eq!(balances(&999), (95, 0));
			// 9999 gets everything back.
			assert_eq!(balances(&9999), (100, 0));
		})
	}

	#[test]
	fn cannot_consume_too_much_future_weight() {
		ExtBuilder::default().signed_weight(40).mock_weight_info(true).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let (solution, witness) = MultiPhase::mine_solution(2).unwrap();
			let solution_weight = <Runtime as Config>::WeightInfo::feasibility_check(
				witness.voters,
				witness.targets,
				solution.compact.voter_count() as u32,
				solution.compact.unique_targets().len() as u32,
			);
			// default solution will have 5 edges (5 * 5 + 10)
			assert_eq!(solution_weight, 35);
			assert_eq!(solution.compact.voter_count(), 5);
			assert_eq!(<Runtime as Config>::SignedMaxWeight::get(), 40);

			assert_ok!(submit_with_witness(Origin::signed(99), solution.clone()));

			<SignedMaxWeight>::set(30);

			// note: resubmitting the same solution is technically okay as long as the queue has
			// space.
			assert_noop!(
				submit_with_witness(Origin::signed(99), solution),
				Error::<Runtime>::SignedTooMuchWeight,
			);
		})
	}
}
