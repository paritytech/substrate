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

//! The signed phase implementation.

use crate::{
	unsigned::MinerConfig, Config, ElectionCompute, Pallet, QueuedSolution, RawSolution,
	ReadySolution, SignedSubmissionIndices, SignedSubmissionNextIndex, SignedSubmissionsMap,
	SolutionOf, SolutionOrSnapshotSize, Weight, WeightInfo,
};
use codec::{Decode, Encode, HasCompact};
use frame_election_provider_support::NposSolution;
use frame_support::traits::{
	defensive_prelude::*, Currency, Get, OnUnbalanced, ReservableCurrency,
};
use sp_arithmetic::traits::SaturatedConversion;
use sp_core::bounded::BoundedVec;
use sp_npos_elections::ElectionScore;
use sp_runtime::{
	traits::{Saturating, Zero},
	RuntimeDebug,
};
use sp_std::{
	cmp::Ordering,
	collections::{btree_map::BTreeMap, btree_set::BTreeSet},
	vec::Vec,
};

/// A raw, unchecked signed submission.
///
/// This is just a wrapper around [`RawSolution`] and some additional info.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, scale_info::TypeInfo)]
pub struct SignedSubmission<AccountId, Balance: HasCompact, Solution> {
	/// Who submitted this solution.
	pub who: AccountId,
	/// The deposit reserved for storing this solution.
	pub deposit: Balance,
	/// The raw solution itself.
	pub raw_solution: RawSolution<Solution>,
	// The estimated fee `who` paid to submit the solution.
	pub call_fee: Balance,
}

impl<AccountId, Balance, Solution> Ord for SignedSubmission<AccountId, Balance, Solution>
where
	AccountId: Ord,
	Balance: Ord + HasCompact,
	Solution: Ord,
	RawSolution<Solution>: Ord,
{
	fn cmp(&self, other: &Self) -> Ordering {
		self.raw_solution
			.score
			.cmp(&other.raw_solution.score)
			.then_with(|| self.raw_solution.cmp(&other.raw_solution))
			.then_with(|| self.deposit.cmp(&other.deposit))
			.then_with(|| self.who.cmp(&other.who))
	}
}

impl<AccountId, Balance, Solution> PartialOrd for SignedSubmission<AccountId, Balance, Solution>
where
	AccountId: Ord,
	Balance: Ord + HasCompact,
	Solution: Ord,
	RawSolution<Solution>: Ord,
{
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type PositiveImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::PositiveImbalance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
pub type SignedSubmissionOf<T> = SignedSubmission<
	<T as frame_system::Config>::AccountId,
	BalanceOf<T>,
	<<T as crate::Config>::MinerConfig as MinerConfig>::Solution,
>;

/// Always sorted vector of a score, submitted at the given block number, which can be found at the
/// given index (`u32`) of the `SignedSubmissionsMap`.
pub type SubmissionIndicesOf<T> = BoundedVec<
	(ElectionScore, <T as frame_system::Config>::BlockNumber, u32),
	<T as Config>::SignedMaxSubmissions,
>;

/// Outcome of [`SignedSubmissions::insert`].
pub enum InsertResult<T: Config> {
	/// The submission was not inserted because the queue was full and the submission had
	/// insufficient score to eject a prior solution from the queue.
	NotInserted,
	/// The submission was inserted successfully without ejecting a solution.
	Inserted,
	/// The submission was inserted successfully. As the queue was full, this operation ejected a
	/// prior solution, contained in this variant.
	InsertedEjecting(SignedSubmissionOf<T>),
}

/// Mask type which pretends to be a set of `SignedSubmissionOf<T>`, while in fact delegating to the
/// actual implementations in `SignedSubmissionIndices<T>`, `SignedSubmissionsMap<T>`, and
/// `SignedSubmissionNextIndex<T>`.
#[cfg_attr(feature = "std", derive(frame_support::DebugNoBound))]
pub struct SignedSubmissions<T: Config> {
	indices: SubmissionIndicesOf<T>,
	next_idx: u32,
	insertion_overlay: BTreeMap<u32, SignedSubmissionOf<T>>,
	deletion_overlay: BTreeSet<u32>,
}

impl<T: Config> SignedSubmissions<T> {
	/// `true` if the structure is empty.
	pub fn is_empty(&self) -> bool {
		self.indices.is_empty()
	}

	/// Get the length of submitted solutions.
	pub fn len(&self) -> usize {
		self.indices.len()
	}

	/// Get the signed submissions from storage.
	pub fn get() -> Self {
		let submissions = SignedSubmissions {
			indices: SignedSubmissionIndices::<T>::get(),
			next_idx: SignedSubmissionNextIndex::<T>::get(),
			insertion_overlay: BTreeMap::new(),
			deletion_overlay: BTreeSet::new(),
		};

		// validate that the stored state is sane
		debug_assert!(submissions
			.indices
			.iter()
			.map(|(_, _, index)| index)
			.copied()
			.max()
			.map_or(true, |max_idx| submissions.next_idx > max_idx,));
		submissions
	}

	/// Put the signed submissions back into storage.
	pub fn put(mut self) {
		// validate that we're going to write only sane things to storage
		debug_assert!(self
			.insertion_overlay
			.keys()
			.copied()
			.max()
			.map_or(true, |max_idx| self.next_idx > max_idx,));
		debug_assert!(self
			.indices
			.iter()
			.map(|(_, _, index)| index)
			.copied()
			.max()
			.map_or(true, |max_idx| self.next_idx > max_idx,));

		SignedSubmissionIndices::<T>::put(self.indices);
		SignedSubmissionNextIndex::<T>::put(self.next_idx);
		for key in self.deletion_overlay {
			self.insertion_overlay.remove(&key);
			SignedSubmissionsMap::<T>::remove(key);
		}
		for (key, value) in self.insertion_overlay {
			SignedSubmissionsMap::<T>::insert(key, value);
		}
	}

	/// Get the submission at a particular index.
	fn get_submission(&self, index: u32) -> Option<SignedSubmissionOf<T>> {
		if self.deletion_overlay.contains(&index) {
			// Note: can't actually remove the item from the insertion overlay (if present) because
			// we don't want to use `&mut self` here. There may be some kind of `RefCell`
			// optimization possible here in the future.
			None
		} else {
			self.insertion_overlay
				.get(&index)
				.cloned()
				.or_else(|| SignedSubmissionsMap::<T>::get(index))
		}
	}

	/// Perform three operations:
	///
	/// - Remove the solution at the given position of `self.indices`.
	/// - Insert a new submission (identified by score and insertion index), if provided.
	/// - Return the submission which was removed, if any.
	///
	/// The call site must ensure that `remove_pos` is a valid index. If otherwise, `None` is
	/// silently returned.
	///
	/// Note: this doesn't insert into `insertion_overlay`, the optional new insertion must be
	/// inserted into `insertion_overlay` to keep the variable `self` in a valid state.
	fn swap_out_submission(
		&mut self,
		remove_pos: usize,
		insert: Option<(ElectionScore, T::BlockNumber, u32)>,
	) -> Option<SignedSubmissionOf<T>> {
		if remove_pos >= self.indices.len() {
			return None
		}

		// safe: index was just checked in the line above.
		let (_, _, remove_index) = self.indices.remove(remove_pos);

		if let Some((insert_score, block_number, insert_idx)) = insert {
			self.indices
				.try_push((insert_score, block_number, insert_idx))
				.expect("just removed an item, we must be under capacity; qed");
		}

		self.insertion_overlay.remove(&remove_index).or_else(|| {
			(!self.deletion_overlay.contains(&remove_index))
				.then(|| {
					self.deletion_overlay.insert(remove_index);
					SignedSubmissionsMap::<T>::get(remove_index)
				})
				.flatten()
		})
	}

	/// Remove the signed submission with the highest score from the set.
	pub fn pop_last(&mut self) -> Option<SignedSubmissionOf<T>> {
		let best_index = self.indices.len().checked_sub(1)?;
		self.swap_out_submission(best_index, None)
	}

	/// Iterate through the set of signed submissions in order of increasing score.
	pub fn iter(&self) -> impl '_ + Iterator<Item = SignedSubmissionOf<T>> {
		self.indices
			.iter()
			.filter_map(move |(_score, _bn, idx)| self.get_submission(*idx).defensive())
	}

	/// Empty the set of signed submissions, returning an iterator of signed submissions in
	/// order of submission.
	///
	/// Note that if the iterator is dropped without consuming all elements, not all may be removed
	/// from the underlying `SignedSubmissionsMap`, putting the storages into an invalid state.
	///
	/// Note that, like `put`, this function consumes `Self` and modifies storage.
	fn drain_submitted_order(mut self) -> impl Iterator<Item = SignedSubmissionOf<T>> {
		let mut keys = SignedSubmissionsMap::<T>::iter_keys()
			.filter(|k| {
				if self.deletion_overlay.contains(k) {
					// Remove submissions that should be deleted.
					SignedSubmissionsMap::<T>::remove(k);
					false
				} else {
					true
				}
			})
			.chain(self.insertion_overlay.keys().copied())
			.collect::<Vec<_>>();
		keys.sort();

		SignedSubmissionIndices::<T>::kill();
		SignedSubmissionNextIndex::<T>::kill();

		keys.into_iter().filter_map(move |index| {
			SignedSubmissionsMap::<T>::take(index).or_else(|| self.insertion_overlay.remove(&index))
		})
	}

	/// Decode the length of the signed submissions without actually reading the entire struct into
	/// memory.
	///
	/// Note that if you hold an instance of `SignedSubmissions`, this function does _not_
	/// track its current length. This only decodes what is currently stored in memory.
	pub fn decode_len() -> Option<usize> {
		SignedSubmissionIndices::<T>::decode_len()
	}

	/// Insert a new signed submission into the set.
	///
	/// In the event that the new submission is not better than the current weakest according
	/// to `is_score_better`, we do not change anything.
	pub fn insert(&mut self, submission: SignedSubmissionOf<T>) -> InsertResult<T> {
		// verify the expectation that we never reuse an index
		debug_assert!(!self.indices.iter().map(|(_, _, x)| x).any(|&idx| idx == self.next_idx));
		let block_number = frame_system::Pallet::<T>::block_number();

		let maybe_weakest = match self.indices.try_push((
			submission.raw_solution.score,
			block_number,
			self.next_idx,
		)) {
			Ok(_) => None,
			Err(_) => {
				// the queue is full -- if this is better, insert it.
				let weakest_score = match self.indices.iter().next().defensive() {
					None => return InsertResult::NotInserted,
					Some((score, _, _)) => *score,
				};
				let threshold = T::BetterSignedThreshold::get();

				// if we haven't improved on the weakest score, don't change anything.
				if !submission.raw_solution.score.strict_threshold_better(weakest_score, threshold)
				{
					return InsertResult::NotInserted
				}

				self.swap_out_submission(
					0, // swap out the worse one, which is always index 0.
					Some((submission.raw_solution.score, block_number, self.next_idx)),
				)
			},
		};

		// this is the ONLY place that we insert, and we sort post insertion. If scores are the
		// same, we sort based on reverse of submission block number.
		self.indices
			.sort_by(|(score1, bn1, _), (score2, bn2, _)| match score1.cmp(score2) {
				Ordering::Equal => bn1.cmp(&bn2).reverse(),
				x => x,
			});

		// we've taken out the weakest, so update the storage map and the next index
		debug_assert!(!self.insertion_overlay.contains_key(&self.next_idx));
		self.insertion_overlay.insert(self.next_idx, submission);
		debug_assert!(!self.deletion_overlay.contains(&self.next_idx));
		self.next_idx += 1;
		match maybe_weakest {
			Some(weakest) => InsertResult::InsertedEjecting(weakest),
			None => InsertResult::Inserted,
		}
	}
}

impl<T: Config> Pallet<T> {
	/// `Self` accessor for `SignedSubmission<T>`.
	pub fn signed_submissions() -> SignedSubmissions<T> {
		SignedSubmissions::<T>::get()
	}

	/// Finish the signed phase. Process the signed submissions from best to worse until a valid one
	/// is found, rewarding the best one and slashing the invalid ones along the way.
	///
	/// Returns true if we have a good solution in the signed phase.
	///
	/// This drains the [`SignedSubmissions`], potentially storing the best valid one in
	/// [`QueuedSolution`].
	///
	/// This is a *self-weighing* function, it automatically registers its weight internally when
	/// being called.
	pub fn finalize_signed_phase() -> bool {
		let (weight, found_solution) = Self::finalize_signed_phase_internal();
		Self::register_weight(weight);
		found_solution
	}

	/// The guts of [`finalized_signed_phase`], that does everything except registering its weight.
	pub(crate) fn finalize_signed_phase_internal() -> (Weight, bool) {
		let mut all_submissions = Self::signed_submissions();
		let mut found_solution = false;
		let mut weight = T::DbWeight::get().reads(1);

		let SolutionOrSnapshotSize { voters, targets } =
			Self::snapshot_metadata().unwrap_or_default();

		while let Some(best) = all_submissions.pop_last() {
			log!(
				debug,
				"finalized_signed: trying to verify from {:?} score {:?}",
				best.who,
				best.raw_solution.score
			);
			let SignedSubmission { raw_solution, who, deposit, call_fee } = best;
			let active_voters = raw_solution.solution.voter_count() as u32;
			let feasibility_weight = {
				// defensive only: at the end of signed phase, snapshot will exits.
				let desired_targets = Self::desired_targets().defensive_unwrap_or_default();
				T::WeightInfo::feasibility_check(voters, targets, active_voters, desired_targets)
			};

			// the feasibility check itself has some weight
			weight = weight.saturating_add(feasibility_weight);
			match Self::feasibility_check(raw_solution, ElectionCompute::Signed) {
				Ok(ready_solution) => {
					Self::finalize_signed_phase_accept_solution(
						ready_solution,
						&who,
						deposit,
						call_fee,
					);
					found_solution = true;
					log!(debug, "finalized_signed: found a valid solution");

					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_accept_solution());
					break
				},
				Err(_) => {
					log!(warn, "finalized_signed: invalid signed submission found, slashing.");
					Self::finalize_signed_phase_reject_solution(&who, deposit);
					weight = weight
						.saturating_add(T::WeightInfo::finalize_signed_phase_reject_solution());
				},
			}
		}

		// Any unprocessed solution is pointless to even consider. Feasible or malicious,
		// they didn't end up being used. Unreserve the bonds.
		let discarded = all_submissions.len();
		let mut refund_count = 0;
		let max_refunds = T::SignedMaxRefunds::get();

		for SignedSubmission { who, deposit, call_fee, .. } in
			all_submissions.drain_submitted_order()
		{
			if refund_count < max_refunds {
				// Refund fee
				let positive_imbalance = T::Currency::deposit_creating(&who, call_fee);
				T::RewardHandler::on_unbalanced(positive_imbalance);
				refund_count += 1;
			}

			// Unreserve deposit
			let _remaining = T::Currency::unreserve(&who, deposit);
			debug_assert!(_remaining.is_zero());
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 2));
		}

		debug_assert!(!SignedSubmissionIndices::<T>::exists());
		debug_assert!(!SignedSubmissionNextIndex::<T>::exists());
		debug_assert!(SignedSubmissionsMap::<T>::iter().next().is_none());

		log!(
			debug,
			"closed signed phase, found solution? {}, discarded {}",
			found_solution,
			discarded
		);

		(weight, found_solution)
	}
	/// Helper function for the case where a solution is accepted in the signed phase.
	///
	/// Extracted to facilitate with weight calculation.
	///
	/// Infallible
	pub fn finalize_signed_phase_accept_solution(
		ready_solution: ReadySolution<T>,
		who: &T::AccountId,
		deposit: BalanceOf<T>,
		call_fee: BalanceOf<T>,
	) {
		// write this ready solution.
		<QueuedSolution<T>>::put(ready_solution);

		let reward = T::SignedRewardBase::get();
		// emit reward event
		Self::deposit_event(crate::Event::Rewarded { account: who.clone(), value: reward });

		// Unreserve deposit.
		let _remaining = T::Currency::unreserve(who, deposit);
		debug_assert!(_remaining.is_zero());

		// Reward and refund the call fee.
		let positive_imbalance =
			T::Currency::deposit_creating(who, reward.saturating_add(call_fee));
		T::RewardHandler::on_unbalanced(positive_imbalance);
	}

	/// Helper function for the case where a solution is accepted in the rejected phase.
	///
	/// Extracted to facilitate with weight calculation.
	///
	/// Infallible
	pub fn finalize_signed_phase_reject_solution(who: &T::AccountId, deposit: BalanceOf<T>) {
		Self::deposit_event(crate::Event::Slashed { account: who.clone(), value: deposit });
		let (negative_imbalance, _remaining) = T::Currency::slash_reserved(who, deposit);
		debug_assert!(_remaining.is_zero());
		T::SlashHandler::on_unbalanced(negative_imbalance);
	}

	/// The weight of the given raw solution.
	pub fn solution_weight_of(
		raw_solution: &RawSolution<SolutionOf<T::MinerConfig>>,
		size: SolutionOrSnapshotSize,
	) -> Weight {
		T::MinerConfig::solution_weight(
			size.voters,
			size.targets,
			raw_solution.solution.voter_count() as u32,
			raw_solution.solution.unique_targets().len() as u32,
		)
	}

	/// Collect a sufficient deposit to store this solution.
	///
	/// The deposit is composed of 3 main elements:
	///
	/// 1. base deposit, fixed for all submissions.
	/// 2. a per-byte deposit, for renting the state usage.
	/// 3. a per-weight deposit, for the potential weight usage in an upcoming on_initialize
	pub fn deposit_for(
		raw_solution: &RawSolution<SolutionOf<T::MinerConfig>>,
		size: SolutionOrSnapshotSize,
	) -> BalanceOf<T> {
		let encoded_len: u32 = raw_solution.encoded_size().saturated_into();
		let encoded_len: BalanceOf<T> = encoded_len.into();
		let feasibility_weight = Self::solution_weight_of(raw_solution, size);

		let len_deposit = T::SignedDepositByte::get().saturating_mul(encoded_len);
		let weight_deposit = T::SignedDepositWeight::get()
			.saturating_mul(feasibility_weight.ref_time().saturated_into());

		T::SignedDepositBase::get()
			.saturating_add(len_deposit)
			.saturating_add(weight_deposit)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{mock::*, ElectionCompute, ElectionError, Error, Event, Perbill, Phase};
	use frame_support::{assert_noop, assert_ok, assert_storage_noop};

	#[test]
	fn cannot_submit_too_early() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(2);
			assert_eq!(MultiPhase::current_phase(), Phase::Off);

			// create a temp snapshot only for this test.
			MultiPhase::create_snapshot().unwrap();
			let solution = raw_solution();

			assert_noop!(
				MultiPhase::submit(RuntimeOrigin::signed(10), Box::new(solution)),
				Error::<Runtime>::PreDispatchEarlySubmission,
			);
		})
	}

	#[test]
	fn data_provider_should_respect_target_limits() {
		ExtBuilder::default().build_and_execute(|| {
			// given a reduced expectation of maximum electable targets
			MaxElectableTargets::set(2);
			// and a data provider that does not respect limits
			DataProviderAllowBadData::set(true);

			assert_noop!(
				MultiPhase::create_snapshot(),
				ElectionError::DataProvider("Snapshot too big for submission."),
			);
		})
	}

	#[test]
	fn data_provider_should_respect_voter_limits() {
		ExtBuilder::default().build_and_execute(|| {
			// given a reduced expectation of maximum electing voters
			MaxElectingVoters::set(2);
			// and a data provider that does not respect limits
			DataProviderAllowBadData::set(true);

			assert_noop!(
				MultiPhase::create_snapshot(),
				ElectionError::DataProvider("Snapshot too big for submission."),
			);
		})
	}

	#[test]
	fn desired_targets_greater_than_max_winners() {
		ExtBuilder::default().build_and_execute(|| {
			// given desired_targets bigger than MaxWinners
			DesiredTargets::set(4);
			MaxWinners::set(3);

			let (_, _, actual_desired_targets) = MultiPhase::create_snapshot_external().unwrap();

			// snapshot is created with min of desired_targets and MaxWinners
			assert_eq!(actual_desired_targets, 3);
		})
	}

	#[test]
	fn should_pay_deposit() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

			assert_eq!(balances(&99), (95, 5));
			assert_eq!(MultiPhase::signed_submissions().iter().next().unwrap().deposit, 5);

			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false }
				]
			);
		})
	}

	#[test]
	fn good_solution_is_rewarded() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			assert_eq!(balances(&99), (95, 5));

			assert!(MultiPhase::finalize_signed_phase());
			assert_eq!(balances(&99), (100 + 7 + 8, 0));

			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Rewarded { account: 99, value: 7 }
				]
			);
		})
	}

	#[test]
	fn bad_solution_is_slashed() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));

			// make the solution invalid.
			solution.score.minimal_stake += 1;

			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			assert_eq!(balances(&99), (95, 5));

			// no good solution was stored.
			assert!(!MultiPhase::finalize_signed_phase());
			// and the bond is gone.
			assert_eq!(balances(&99), (95, 0));

			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Slashed { account: 99, value: 5 }
				]
			);
		})
	}

	#[test]
	fn suppressed_solution_gets_bond_back() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let mut solution = raw_solution();
			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));

			// submit as correct.
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution.clone())));

			// make the solution invalid and weaker.
			solution.score.minimal_stake -= 1;
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(999), Box::new(solution)));
			assert_eq!(balances(&99), (95, 5));
			assert_eq!(balances(&999), (95, 5));

			// _some_ good solution was stored.
			assert!(MultiPhase::finalize_signed_phase());

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7 + 8, 0));
			// 999 gets everything back, including the call fee.
			assert_eq!(balances(&999), (100 + 8, 0));
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Rewarded { account: 99, value: 7 }
				]
			);
		})
	}

	#[test]
	fn cannot_submit_worse_with_full_queue() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + s).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			}

			// weaker.
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 4, ..Default::default() },
				..Default::default()
			};

			assert_noop!(
				MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)),
				Error::<Runtime>::SignedQueueFull,
			);
		})
	}

	#[test]
	fn call_fee_refund_is_limited_by_signed_max_refunds() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());
			assert_eq!(SignedMaxRefunds::get(), 1);
			assert!(SignedMaxSubmissions::get() > 2);

			for s in 0..SignedMaxSubmissions::get() {
				let account = 99 + s as u64;
				Balances::make_free_balance_be(&account, 100);
				// score is always decreasing
				let mut solution = raw_solution();
				solution.score.minimal_stake -= s as u128;

				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(account), Box::new(solution)));
				assert_eq!(balances(&account), (95, 5));
			}

			assert_ok!(MultiPhase::do_elect());

			for s in 0..SignedMaxSubmissions::get() {
				let account = 99 + s as u64;
				// lower accounts have higher scores
				if s == 0 {
					// winning solution always gets call fee + reward
					assert_eq!(balances(&account), (100 + 8 + 7, 0))
				} else if s == 1 {
					// 1 runner up gets their call fee refunded
					assert_eq!(balances(&account), (100 + 8, 0))
				} else {
					// all other solutions don't get a call fee refund
					assert_eq!(balances(&account), (100, 0));
				}
			}
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Rewarded { account: 99, value: 7 },
					Event::ElectionFinalized {
						compute: ElectionCompute::Signed,
						score: ElectionScore {
							minimal_stake: 40,
							sum_stake: 100,
							sum_stake_squared: 5200
						}
					}
				]
			);
		});
	}

	#[test]
	fn cannot_submit_worse_with_full_queue_depends_on_threshold() {
		ExtBuilder::default()
			.signed_max_submission(1)
			.better_signed_threshold(Perbill::from_percent(20))
			.build_and_execute(|| {
				roll_to_signed();
				assert!(MultiPhase::current_phase().is_signed());

				let mut solution = RawSolution {
					score: ElectionScore {
						minimal_stake: 5u128,
						sum_stake: 0u128,
						sum_stake_squared: 10u128,
					},
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

				// This is 10% better, so does not meet the 20% threshold and is therefore rejected.
				solution = RawSolution {
					score: ElectionScore {
						minimal_stake: 5u128,
						sum_stake: 0u128,
						sum_stake_squared: 9u128,
					},
					..Default::default()
				};

				assert_noop!(
					MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)),
					Error::<Runtime>::SignedQueueFull,
				);

				// This is however 30% better and should therefore be accepted.
				solution = RawSolution {
					score: ElectionScore {
						minimal_stake: 5u128,
						sum_stake: 0u128,
						sum_stake_squared: 7u128,
					},
					..Default::default()
				};

				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
				assert_eq!(
					multi_phase_events(),
					vec![
						Event::SignedPhaseStarted { round: 1 },
						Event::SolutionStored {
							compute: ElectionCompute::Signed,
							prev_ejected: false
						},
						Event::SolutionStored {
							compute: ElectionCompute::Signed,
							prev_ejected: true
						}
					]
				);
			})
	}

	#[test]
	fn weakest_is_removed_if_better_provided() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				let account = 99 + s as u64;
				Balances::make_free_balance_be(&account, 100);
				// score is always getting better
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + s).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(account), Box::new(solution)));
				assert_eq!(balances(&account), (95, 5));
			}

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| s.raw_solution.score.minimal_stake)
					.collect::<Vec<_>>(),
				vec![5, 6, 7, 8, 9]
			);

			// better.
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 20, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(999), Box::new(solution)));

			// the one with score 5 was rejected, the new one inserted.
			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| s.raw_solution.score.minimal_stake)
					.collect::<Vec<_>>(),
				vec![6, 7, 8, 9, 20]
			);

			// the submitter of the ejected solution does *not* get a call fee refund
			assert_eq!(balances(&(99 + 0)), (100, 0));
		})
	}

	#[test]
	fn replace_weakest_by_score_works() {
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for s in 1..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + s).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			}

			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 4, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| s.raw_solution.score.minimal_stake)
					.collect::<Vec<_>>(),
				vec![4, 6, 7],
			);

			// better.
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

			// the one with score 5 was rejected, the new one inserted.
			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| s.raw_solution.score.minimal_stake)
					.collect::<Vec<_>>(),
				vec![5, 6, 7],
			);
		})
	}

	#[test]
	fn early_ejected_solution_gets_bond_back() {
		ExtBuilder::default().signed_deposit(2, 0, 0).build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + s).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			}

			assert_eq!(balances(&99).1, 2 * 5);
			assert_eq!(balances(&999).1, 0);

			// better.
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 20, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(999), Box::new(solution)));

			// got one bond back.
			assert_eq!(balances(&99).1, 2 * 4);
			assert_eq!(balances(&999).1, 2);
		})
	}

	#[test]
	fn equally_good_solution_is_not_accepted_when_queue_full() {
		// because in ordering of solutions, an older solution has higher priority and should stay.
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for i in 0..SignedMaxSubmissions::get() {
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + i).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			}

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| s.raw_solution.score.minimal_stake)
					.collect::<Vec<_>>(),
				vec![5, 6, 7]
			);

			// 5 is not accepted. This will only cause processing with no benefit.
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			assert_noop!(
				MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)),
				Error::<Runtime>::SignedQueueFull,
			);
		})
	}

	#[test]
	fn equally_good_solution_is_accepted_when_queue_not_full() {
		// because in ordering of solutions, an older solution has higher priority and should stay.
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| (s.who, s.raw_solution.score.minimal_stake,))
					.collect::<Vec<_>>(),
				vec![(99, 5)]
			);

			roll_to(16);
			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 5, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(999), Box::new(solution)));

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| (s.who, s.raw_solution.score.minimal_stake,))
					.collect::<Vec<_>>(),
				vec![(999, 5), (99, 5)]
			);

			let solution = RawSolution {
				score: ElectionScore { minimal_stake: 6, ..Default::default() },
				..Default::default()
			};
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(9999), Box::new(solution)));

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| (s.who, s.raw_solution.score.minimal_stake,))
					.collect::<Vec<_>>(),
				vec![(999, 5), (99, 5), (9999, 6)]
			);
		})
	}

	#[test]
	fn all_equal_score() {
		// because in ordering of solutions, an older solution has higher priority and should stay.
		ExtBuilder::default().signed_max_submission(3).build_and_execute(|| {
			roll_to(15);
			assert!(MultiPhase::current_phase().is_signed());

			for i in 0..SignedMaxSubmissions::get() {
				roll_to((15 + i).into());
				let solution = raw_solution();
				assert_ok!(MultiPhase::submit(
					RuntimeOrigin::signed(100 + i as AccountId),
					Box::new(solution)
				));
			}

			assert_eq!(
				MultiPhase::signed_submissions()
					.iter()
					.map(|s| (s.who, s.raw_solution.score.minimal_stake))
					.collect::<Vec<_>>(),
				vec![(102, 40), (101, 40), (100, 40)]
			);

			roll_to(25);

			// The first one that will actually get verified is the last one.
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Rewarded { account: 100, value: 7 },
					Event::UnsignedPhaseStarted { round: 1 }
				]
			);
		})
	}

	#[test]
	fn all_in_one_signed_submission_scenario() {
		// a combination of:
		// - good_solution_is_rewarded
		// - bad_solution_is_slashed
		// - suppressed_solution_gets_bond_back
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			assert_eq!(balances(&99), (100, 0));
			assert_eq!(balances(&999), (100, 0));
			assert_eq!(balances(&9999), (100, 0));

			let solution = raw_solution();

			// submit a correct one.
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution.clone())));

			// make the solution invalidly better and submit. This ought to be slashed.
			let mut solution_999 = solution.clone();
			solution_999.score.minimal_stake += 1;
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(999), Box::new(solution_999)));

			// make the solution invalidly worse and submit. This ought to be suppressed and
			// returned.
			let mut solution_9999 = solution.clone();
			solution_9999.score.minimal_stake -= 1;
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(9999), Box::new(solution_9999)));

			assert_eq!(
				MultiPhase::signed_submissions().iter().map(|x| x.who).collect::<Vec<_>>(),
				vec![9999, 99, 999]
			);

			// _some_ good solution was stored.
			assert!(MultiPhase::finalize_signed_phase());

			// 99 is rewarded.
			assert_eq!(balances(&99), (100 + 7 + 8, 0));
			// 999 is slashed.
			assert_eq!(balances(&999), (95, 0));
			// 9999 gets everything back, including the call fee.
			assert_eq!(balances(&9999), (100 + 8, 0));
			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Slashed { account: 999, value: 5 },
					Event::Rewarded { account: 99, value: 7 }
				]
			);
		})
	}

	#[test]
	fn cannot_consume_too_much_future_weight() {
		ExtBuilder::default()
			.signed_weight(Weight::from_ref_time(40).set_proof_size(u64::MAX))
			.mock_weight_info(MockedWeightInfo::Basic)
			.build_and_execute(|| {
				roll_to_signed();
				assert!(MultiPhase::current_phase().is_signed());

				let (raw, witness) = MultiPhase::mine_solution().unwrap();
				let solution_weight = <Runtime as MinerConfig>::solution_weight(
					witness.voters,
					witness.targets,
					raw.solution.voter_count() as u32,
					raw.solution.unique_targets().len() as u32,
				);
				// default solution will have 5 edges (5 * 5 + 10)
				assert_eq!(solution_weight, Weight::from_ref_time(35));
				assert_eq!(raw.solution.voter_count(), 5);
				assert_eq!(
					<Runtime as Config>::SignedMaxWeight::get(),
					Weight::from_ref_time(40).set_proof_size(u64::MAX)
				);

				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(raw.clone())));

				<SignedMaxWeight>::set(Weight::from_ref_time(30).set_proof_size(u64::MAX));

				// note: resubmitting the same solution is technically okay as long as the queue has
				// space.
				assert_noop!(
					MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(raw)),
					Error::<Runtime>::SignedTooMuchWeight,
				);
			})
	}

	#[test]
	fn insufficient_deposit_does_not_store_submission() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();

			assert_eq!(balances(&123), (0, 0));
			assert_noop!(
				MultiPhase::submit(RuntimeOrigin::signed(123), Box::new(solution)),
				Error::<Runtime>::SignedCannotPayDeposit,
			);

			assert_eq!(balances(&123), (0, 0));
		})
	}

	// given a full queue, and a solution which _should_ be allowed in, but the proposer of this
	// new solution has insufficient deposit, we should not modify storage at all
	#[test]
	fn insufficient_deposit_with_full_queue_works_properly() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			for s in 0..SignedMaxSubmissions::get() {
				// score is always getting better
				let solution = RawSolution {
					score: ElectionScore { minimal_stake: (5 + s).into(), ..Default::default() },
					..Default::default()
				};
				assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));
			}

			// this solution has a higher score than any in the queue
			let solution = RawSolution {
				score: ElectionScore {
					minimal_stake: (5 + SignedMaxSubmissions::get()).into(),
					..Default::default()
				},
				..Default::default()
			};

			assert_eq!(balances(&123), (0, 0));
			assert_noop!(
				MultiPhase::submit(RuntimeOrigin::signed(123), Box::new(solution)),
				Error::<Runtime>::SignedCannotPayDeposit,
			);

			assert_eq!(balances(&123), (0, 0));
		})
	}

	#[test]
	fn finalize_signed_phase_is_idempotent_given_no_submissions() {
		ExtBuilder::default().build_and_execute(|| {
			for block_number in 0..25 {
				roll_to(block_number);

				assert_eq!(SignedSubmissions::<Runtime>::decode_len().unwrap_or_default(), 0);
				assert_storage_noop!(MultiPhase::finalize_signed_phase_internal());
			}
		})
	}

	#[test]
	fn finalize_signed_phase_is_idempotent_given_submissions() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to_signed();
			assert!(MultiPhase::current_phase().is_signed());

			let solution = raw_solution();

			// submit a correct one.
			assert_ok!(MultiPhase::submit(RuntimeOrigin::signed(99), Box::new(solution)));

			// _some_ good solution was stored.
			assert!(MultiPhase::finalize_signed_phase());

			// calling it again doesn't change anything
			assert_storage_noop!(MultiPhase::finalize_signed_phase());

			assert_eq!(
				multi_phase_events(),
				vec![
					Event::SignedPhaseStarted { round: 1 },
					Event::SolutionStored { compute: ElectionCompute::Signed, prev_ejected: false },
					Event::Rewarded { account: 99, value: 7 }
				]
			);
		})
	}
}
