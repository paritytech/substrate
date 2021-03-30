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

use super::*;
use codec::{Encode, HasCompact};
use sp_arithmetic::traits::SaturatedConversion;
use sp_npos_elections::{is_score_better, CompactSolution};
use sp_runtime::Perbill;

/// A raw, unchecked signed submission.
///
/// This is just a wrapper around [`RawSolution`] and some additional info.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, Default)]
pub struct SignedSubmission<A, B: HasCompact, C> {
	/// Who submitted this solution.
	pub(crate) who: A,
	/// The deposit reserved for storing this solution.
	pub(crate) deposit: B,
	/// The reward that should be given to this solution, if chosen the as the final one.
	pub(crate) reward: B,
	/// The raw solution itself.
	pub(crate) solution: RawSolution<C>,
}

pub(crate) type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub(crate) type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::PositiveImbalance;
pub(crate) type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
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
		let mut all_submission: Vec<SignedSubmission<_, _, _>> = <SignedSubmissions<T>>::take();
		let mut found_solution = false;
		let mut weight = T::DbWeight::get().reads(1);

		while let Some(best) = all_submission.pop() {
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
			match Self::feasibility_check(solution, ElectionCompute::Signed) {
				Ok(ready_solution) => {
					Self::finalize_signed_phase_accept_solution(
						ready_solution,
						&who,
						deposit,
						reward,
					);
					found_solution = true;

					weight = weight.saturating_add(feasibility_weight);
					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_accept_solution());
					break;
				}
				Err(_) => {
					// we assume a worse case feasibility check happened anyhow.
					weight = weight.saturating_add(feasibility_weight);
					Self::finalize_signed_phase_reject_solution(&who, deposit);
					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_reject_solution());
				}
			}
		}

		// Any unprocessed solution is pointless to even consider. Feasible or malicious,
		// they didn't end up being used. Unreserve the bonds.
		all_submission.into_iter().for_each(|not_processed| {
			let SignedSubmission { who, deposit, .. } = not_processed;
			let _remaining = T::Currency::unreserve(&who, deposit);
			weight = weight.saturating_add(T::DbWeight::get().writes(1));
			debug_assert!(_remaining.is_zero());
		});

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

	/// Find a proper position in the queue for the signed queue, whilst maintaining the order of
	/// solution quality. If insertion was successful, `Some(index)` is returned where index is the
	/// index of the newly inserted item.
	///
	/// Invariant: The returned index is always a valid index in `queue` and can safely be used to
	/// inspect the newly inserted element.
	pub fn insert_submission(
		who: &T::AccountId,
		queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
		solution: RawSolution<CompactOf<T>>,
		size: SolutionOrSnapshotSize,
	) -> Option<usize> {
		// from the last score, compare and see if the current one is better. If none, then the
		// awarded index is 0.
		let outcome = queue
			.iter()
			.enumerate()
			.rev()
			.find_map(|(i, s)| {
				if is_score_better::<Perbill>(
					solution.score,
					s.solution.score,
					T::SolutionImprovementThreshold::get(),
				) {
					Some(i + 1)
				} else {
					None
				}
			})
			.or(Some(0))
			.and_then(|at| {
				if at == 0 && queue.len() as u32 >= T::SignedMaxSubmissions::get() {
					// if this is worse than all, and the queue is full, don't bother.
					None
				} else {
					// add to the designated spot. If the length is too much, remove one.
					let reward = Self::reward_for(&solution);
					let deposit = Self::deposit_for(&solution, size);
					let submission =
						SignedSubmission { who: who.clone(), deposit, reward, solution };
					// Proof: `at` must always less than or equal queue.len() for this not to panic.
					// It is either 0 (in which case `0 <= queue.len()`) or one of the queue indices
					// + 1. The biggest queue index is `queue.len() - 1`, thus `at <= queue.len()`.
					queue.insert(at, submission);
					Some(at)
				}
			});

		// If the call site is sane and removes the weakest, then this must always be correct.
		debug_assert!(queue.len() as u32 <= T::SignedMaxSubmissions::get() + 1);
		outcome
	}

	/// Removes the weakest element of the queue, namely the first one, should the length of the
	/// queue be enough.
	///
	/// noop if the queue is empty. Bond of the removed solution is returned.
	pub fn remove_weakest(
		queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
	) {
		if queue.len() > 0 {
			let SignedSubmission { who, deposit, .. } = queue.remove(0);
			let _remainder = T::Currency::unreserve(&who, deposit);
			debug_assert!(_remainder.is_zero());
		}
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
	pub fn deposit_for(solution: &RawSolution<CompactOf<T>>, size: SolutionOrSnapshotSize) -> BalanceOf<T> {
		let encoded_len: BalanceOf<T> = solution.using_encoded(|e| e.len() as u32).into();
		let feasibility_weight = Self::feasibility_weight_of(solution, size);

		let len_deposit = T::SignedDepositByte::get() * encoded_len;
		let weight_deposit = T::SignedDepositWeight::get() * feasibility_weight.saturated_into();

		T::SignedDepositBase::get() + len_deposit + weight_deposit
	}

	/// The reward for this solution, if successfully chosen as the best one at the end of the
	/// signed phase.
	pub fn reward_for(solution: &RawSolution<CompactOf<T>>) -> BalanceOf<T> {
		let raw_reward = T::SignedRewardBase::get()
			+ T::SignedRewardFactor::get() * solution.score[0].saturated_into::<BalanceOf<T>>();

		match T::SignedRewardMax::get() {
			Some(cap) => raw_reward.min(cap),
			None => raw_reward,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{
		mock::{Origin, *},
		Error, Phase, *,
	};
	use frame_support::dispatch::DispatchResultWithPostInfo;

	fn submit_with_witness(
		origin: Origin,
		solution: RawSolution<CompactOf<Runtime>>,
	) -> DispatchResultWithPostInfo {
		MultiPhase::submit(origin, solution, MultiPhase::signed_submissions().len() as u32)
	}

	#[test]
	fn cannot_submit_too_early() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(2);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// create a temp snapshot only for this test.
			MultiPhase::create_snapshot();
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
				MultiPhase::submit(Origin::signed(99), solution, 0,),
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
	fn reward_is_capped() {
		ExtBuilder::default().reward(5, Perbill::from_percent(25), 10).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(solution.score[0], 40);
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(MultiPhase::finalize_signed_phase().0);
			// expected reward is 5 + 10
			assert_eq!(balances(&99), (100 + 10, 0));
		});

		ExtBuilder::default().reward(5, Perbill::from_percent(25), 20).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(solution.score[0], 40);
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(MultiPhase::finalize_signed_phase().0);
			// expected reward is 5 + 10
			assert_eq!(balances(&99), (100 + 15, 0));
		});
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
				vec![5, 6, 7, 8, 9]
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
				vec![6, 7, 8, 9, 20]
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
				vec![4, 6, 7, 8, 9]
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
				vec![5, 6, 7, 8, 9]
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
				vec![5, 6, 7]
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
			assert_eq!(scores(), vec![5, 8]);

			let solution = RawSolution { score: [3, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![3, 5, 8]);

			let solution = RawSolution { score: [6, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![5, 6, 8]);

			let solution = RawSolution { score: [6, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![6, 6, 8]);

			let solution = RawSolution { score: [10, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![6, 8, 10]);

			let solution = RawSolution { score: [12, 0, 0], ..Default::default() };
			assert_ok!(submit_with_witness(Origin::signed(99), solution));
			assert_eq!(scores(), vec![8, 10, 12]);
		})
	}

	#[test]
	fn all_in_one_singed_submission_scenario() {
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
				vec![9999, 99, 999]
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
