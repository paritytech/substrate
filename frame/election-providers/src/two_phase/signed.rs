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

use crate::two_phase::*;
use codec::Encode;
use sp_arithmetic::traits::SaturatedConversion;
use sp_npos_elections::is_score_better;
use sp_runtime::Perbill;

impl<T: Trait> Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	/// Start the signed phase.
	///
	/// Upon calling this, auxillary data for election is stored and signed solutions will be
	/// accepted.
	///
	/// The signed phase must always start before the unsigned phase.
	pub fn start_signed_phase() {
		let targets = T::ElectionDataProvider::targets();
		let voters = T::ElectionDataProvider::voters();
		let desired_targets = T::ElectionDataProvider::desired_targets();

		<SnapshotTargets<T>>::put(targets);
		<SnapshotVoters<T>>::put(voters);
		DesiredTargets::put(desired_targets);
	}

	/// Finish the singed phase. Process the signed submissions from best to worse until a valid one
	/// is found, rewarding the best oen and slashing the invalid ones along the way.
	///
	/// Returns true if we have a good solution in the signed phase.
	///
	/// This drains the [`SignedSubmissions`], potentially storing the best valid one in
	/// [`QueuedSolution`].
	pub fn finalize_signed_phase() -> bool {
		let mut all_submission: Vec<SignedSubmission<_, _, _>> = <SignedSubmissions<T>>::take();
		let mut found_solution = false;

		while let Some(best) = all_submission.pop() {
			let SignedSubmission {
				solution,
				who,
				deposit,
				reward,
			} = best;
			match Self::feasibility_check(solution, ElectionCompute::Signed) {
				Ok(ready_solution) => {
					// write this ready solution.
					<QueuedSolution<T>>::put(ready_solution);

					// unreserve deposit.
					let _remaining = T::Currency::unreserve(&who, deposit);
					debug_assert!(_remaining.is_zero());

					// Reward.
					let positive_imbalance = T::Currency::deposit_creating(&who, reward);
					T::RewardHandler::on_unbalanced(positive_imbalance);

					found_solution = true;
					break;
				}
				Err(_) => {
					let (negative_imbalance, _remaining) =
						T::Currency::slash_reserved(&who, deposit);
					debug_assert!(_remaining.is_zero());
					T::SlashHandler::on_unbalanced(negative_imbalance);
				}
			}
		}

		// Any unprocessed solution is not pointless to even ponder upon. Feasible or malicious,
		// they didn't end up being used. Unreserve the bonds.
		all_submission.into_iter().for_each(|not_processed| {
			let SignedSubmission { who, deposit, .. } = not_processed;
			let _remaining = T::Currency::unreserve(&who, deposit);
			debug_assert!(_remaining.is_zero());
		});

		found_solution
	}

	/// Find a proper position in the queue for the signed queue, whilst maintaining the order of
	/// solution quality.
	///
	/// The length of the queue will always be kept less than or equal to `T::MaxSignedSubmissions`.
	pub fn insert_submission(
		who: &T::AccountId,
		queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>, CompactOf<T>>>,
		solution: RawSolution<CompactOf<T>>,
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
				if at == 0 && queue.len() as u32 >= T::MaxSignedSubmissions::get() {
					// if this is worse than all, and the queue is full, don't bother.
					None
				} else {
					// add to the designated spot. If the length is too much, remove one.
					let reward = Self::reward_for(&solution);
					let deposit = Self::deposit_for(&solution);
					let submission = SignedSubmission {
						who: who.clone(),
						deposit,
						reward,
						solution,
					};
					// Proof: `at` must always less than or equal queue.len() for this not to panic.
					// It is either 0 (in which case `0 <= queue.len()`) or one of the queue indices
					// + 1. The biggest queue index is `queue.len() - 1`, thus `at <= queue.len()`.
					queue.insert(at, submission);
					if queue.len() as u32 > T::MaxSignedSubmissions::get() {
						queue.remove(0);
						Some(at - 1)
					} else {
						Some(at)
					}
				}
			});

		debug_assert!(queue.len() as u32 <= T::MaxSignedSubmissions::get());
		outcome
	}

	/// Collect sufficient deposit to store this solution this chain.
	///
	/// The deposit is composed of 3 main elements:
	///
	/// 1. base deposit, fixed for all submissions.
	/// 2. a per-byte deposit, for renting the state usage.
	/// 3. a per-weight deposit, for the potential weight usage in an upcoming on_initialize
	pub fn deposit_for(solution: &RawSolution<CompactOf<T>>) -> BalanceOf<T> {
		let encoded_len: BalanceOf<T> = solution.using_encoded(|e| e.len() as u32).into();
		let feasibility_weight = T::WeightInfo::feasibility_check();

		let len_deposit = T::SignedDepositByte::get() * encoded_len;
		let weight_deposit = T::SignedDepositWeight::get() * feasibility_weight.saturated_into();

		T::SignedDepositBase::get() + len_deposit + weight_deposit
	}

	/// The reward for this solution, if successfully chosen as the best one at the end of the
	/// signed phase.
	pub fn reward_for(solution: &RawSolution<CompactOf<T>>) -> BalanceOf<T> {
		T::SignedRewardBase::get()
			+ T::SignedRewardFactor::get() * solution.score[0].saturated_into::<BalanceOf<T>>()
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, *};

	#[test]
	fn cannot_submit_too_early() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(2);
			assert_eq!(TwoPhase::current_phase(), Phase::Off);

			// create a temp snapshot only for this test.
			TwoPhase::start_signed_phase();
			let solution = raw_solution();

			assert_noop!(
				TwoPhase::submit(Origin::signed(10), solution),
				"EarlySubmission",
			);
		})
	}

	#[test]
	fn should_pay_deposit() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			assert_eq!(balances(&99), (95, 5));
			assert_eq!(TwoPhase::signed_submissions().first().unwrap().deposit, 5);
		})
	}

	#[test]
	fn good_solution_is_rewarded() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(TwoPhase::finalize_signed_phase());
			assert_eq!(balances(&99), (100 + 7, 0));
		})
	}

	#[test]
	fn bad_solution_is_slashed() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			// make the solution invalid.
			solution.score[0] += 1;

			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			// no good solution was stored.
			assert!(!TwoPhase::finalize_signed_phase());
			// and the bond is gone.
			assert_eq!(balances(&99), (95, 0));
		})
	}

	#[test]
	fn suppressed_solution_gets_bond_back() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));

			// submit as correct.
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution.clone()));

			// make the solution invalid and weaker.
			solution.score[0] -= 1;
			assert_ok!(TwoPhase::submit(Origin::signed(999), solution));
			assert_eq!(balances(&99), (95, 5));
			assert_eq!(balances(&999), (95, 5));

			// _some_ good solution was stored.
			assert!(TwoPhase::finalize_signed_phase());

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7, 0));
			// 999 gets everything back.
			assert_eq!(balances(&999), (100, 0));
		})
	}

	#[test]
	fn queue_is_always_sorted() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let solution = RawSolution {
				score: [5, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			// then a worse one.
			let solution = RawSolution {
				score: [4, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			// then a better one.
			let solution = RawSolution {
				score: [6, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			assert_eq!(
				TwoPhase::signed_submissions()
					.iter()
					.map(|x| x.solution.score[0])
					.collect::<Vec<_>>(),
				vec![4, 5, 6]
			);
		})
	}

	#[test]
	fn cannot_submit_worse_with_full_queue() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);

			for s in 0..MaxSignedSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: [(5 + s).into(), 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			}

			// weaker.
			let solution = RawSolution {
				score: [4, 0, 0],
				..Default::default()
			};

			assert_noop!(
				TwoPhase::submit(Origin::signed(99), solution),
				"QueueFull",
			);
		})
	}

	#[test]
	fn weakest_is_removed_if_better_provided() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);

			for s in 0..MaxSignedSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: [(5 + s).into(), 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			}

			assert_eq!(
				TwoPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8, 9]
			);

			// better.
			let solution = RawSolution {
				score: [20, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			// the one with score 5 was rejected, the new one inserted.
			assert_eq!(
				TwoPhase::signed_submissions()
					.into_iter()
					.map(|s| s.solution.score[0])
					.collect::<Vec<_>>(),
				vec![6, 7, 8, 9, 20]
			);
		})
	}

	#[test]
	fn equally_good_is_not_accepted() {
		ExtBuilder::default()
			.max_signed_submission(3)
			.build_and_execute(|| {
				roll_to(5);

				for i in 0..MaxSignedSubmissions::get() {
					let solution = RawSolution {
						score: [(5 + i).into(), 0, 0],
						..Default::default()
					};
					assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				}
				assert_eq!(
					TwoPhase::signed_submissions()
						.into_iter()
						.map(|s| s.solution.score[0])
						.collect::<Vec<_>>(),
					vec![5, 6, 7]
				);

				// 5 is not accepted. This will only cause processing with no benefit.
				let solution = RawSolution {
					score: [5, 0, 0],
					..Default::default()
				};
				assert_noop!(
					TwoPhase::submit(Origin::signed(99), solution),
					"QueueFull",
				);
			})
	}

	#[test]
	fn solutions_are_always_sorted() {
		ExtBuilder::default()
			.max_signed_submission(3)
			.build_and_execute(|| {
				let scores = || TwoPhase::signed_submissions()
						.into_iter()
						.map(|s| s.solution.score[0])
						.collect::<Vec<_>>();
				roll_to(5);

				let solution = RawSolution {
					score: [5, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![5]);

				let solution = RawSolution {
					score: [8, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![5, 8]);

				let solution = RawSolution {
					score: [3, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![3, 5, 8]);

				let solution = RawSolution {
					score: [6, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![5, 6, 8]);

				let solution = RawSolution {
					score: [6, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![6, 6, 8]);

				let solution = RawSolution {
					score: [10, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
				assert_eq!(scores(), vec![6, 8, 10]);

				let solution = RawSolution {
					score: [12, 0, 0],
					..Default::default()
				};
				assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
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
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));
			assert_eq!(balances(&9999), (100, 0));
			let mut solution = raw_solution();

			// submit a correct one.
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution.clone()));

			// make the solution invalidly better and submit. This ought to be slashed.
			solution.score[0] += 1;
			assert_ok!(TwoPhase::submit(Origin::signed(999), solution.clone()));

			// make the solution invalidly worse and submit. This ought to be suppressed and returned.
			solution.score[0] -= 1;
			assert_ok!(TwoPhase::submit(Origin::signed(9999), solution));

			assert_eq!(
				TwoPhase::signed_submissions()
					.iter()
					.map(|x| x.who)
					.collect::<Vec<_>>(),
				vec![9999, 99, 999]
			);

			// _some_ good solution was stored.
			assert!(TwoPhase::finalize_signed_phase());

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7, 0));
			// 999 is slashed.
			assert_eq!(balances(&999), (95, 0));
			// 9999 gets everything back.
			assert_eq!(balances(&9999), (100, 0));
		})
	}
}
