use crate::two_phase::*;
use codec::Encode;
use sp_arithmetic::traits::SaturatedConversion;

impl<T: Trait> Module<T> {
	/// Start the signed phase.
	///
	/// Upon calling this, auxillary data for election is stored and signed solutions will be
	/// accepted.
	///
	/// The signed phase must always start before the unsigned phase.
	pub fn start_signed_phase() {
		let targets = T::ElectionDataProvider::targets();
		// TODO: this module is not aware at all of self-vote. Clarify this.
		let voters = T::ElectionDataProvider::voters();
		let desired_targets = T::ElectionDataProvider::desired_targets();

		<SnapshotTargets<T>>::put(targets);
		<SnapshotVoters<T>>::put(voters);
		DesiredTargets::put(desired_targets);
	}

	/// Finish the singed phase.
	///
	/// Returns true if we have a good solution in the signed phase.
	pub fn finalize_signed_phase() -> bool {
		let mut all_submission: Vec<SignedSubmission<_, _>> = <SignedSubmissions<T>>::take();
		let mut found_solution = false;

		while let Some(best) = all_submission.pop() {
			let SignedSubmission {
				solution,
				who,
				deposit,
				reward,
			} = best;
			match Self::feasibility_check(solution) {
				Ok(ready_solution) => {
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
	pub fn insert_submission(
		who: &T::AccountId,
		queue: &mut Vec<SignedSubmission<T::AccountId, BalanceOf<T>>>,
		solution: RawSolution<T::AccountId>,
	) -> Option<usize> {
		use sp_npos_elections::is_score_better;
		// consider using VecDeQue or sth like that?

		let outcome = queue
			.iter()
			.enumerate()
			.rev()
			.find_map(|(i, s)| {
				if is_score_better(
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
					// add to the designated spo. If the length is too much, remove one.
					let reward = Self::reward_for(&solution);
					let deposit = Self::deposit_for(&solution);
					let submission = SignedSubmission {
						who: who.clone(),
						deposit,
						reward,
						solution,
					};
					// TODO: write proof that this cannot panic
					queue.insert(at, submission);
					if queue.len() as u32 >= T::MaxSignedSubmissions::get() {
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

	pub fn deposit_for(solution: &RawSolution<T::AccountId>) -> BalanceOf<T> {
		let encoded_len: BalanceOf<T> = solution.using_encoded(|e| e.len() as u32).into();
		// TODO
		T::SignedDepositBase::get() + T::SignedDepositByte::get() * encoded_len
	}

	pub fn reward_for(solution: &RawSolution<T::AccountId>) -> BalanceOf<T> {
		T::SignedRewardBase::get()
			+ T::SignedRewardFactor::get() * solution.score[0].saturated_into::<BalanceOf<T>>()
	}
}

#[cfg(test)]
mod tests {
	use super::{mock::*, *};
	use crate::*;

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
				PalletError::<Runtime>::EarlySubmission
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

			let mut solution = raw_solution();
			// cheat here.
			solution.score[0] += 1;
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(TwoPhase::finalize_signed_phase());
			assert_eq!(balances(&99), (100 + 5, 0));
		})
	}

	#[test]
	fn bad_solution_is_slashed() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));
			assert_eq!(balances(&99), (95, 5));

			assert!(TwoPhase::finalize_signed_phase());
			assert_eq!(balances(&99), (95, 0));
		})
	}

	#[test]
	fn queue_is_always_sorted() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);

			let solution = RawSolution {
				winners: vec![1u64],
				score: [5, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			// then a worse one.
			let solution = RawSolution {
				winners: vec![2u64],
				score: [4, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			// then a better one.
			let solution = RawSolution {
				winners: vec![3u64],
				score: [6, 0, 0],
				..Default::default()
			};
			assert_ok!(TwoPhase::submit(Origin::signed(99), solution));

			assert_eq!(
				TwoPhase::signed_submissions()
					.iter()
					.map(|x| x.solution.winners[0])
					.collect::<Vec<_>>(),
				vec![2, 1, 3]
			);
		})
	}

	#[test]
	fn can_submit_until_queue_full() {}

	#[test]
	fn weakest_is_removed_if_better_provided() {}

	#[test]
	fn cannot_submit_worse_with_full_queue() {}

	#[test]
	fn suppressed_solution_gets_bond_back() {}

	#[test]
	fn solutions_are_sorted() {}

	#[test]
	fn all_in_one_singed_submission() {
		// a combination of:
		// - good_solution_is_rewarded
		// - bad_solution_is_slashed
		// - suppressed_solution_gets_bond_back
	}
}
