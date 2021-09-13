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

//! The unsigned phase, and its miner.

/// Exports of this pallet
pub use pallet::*;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

/// The miner.
pub mod miner;

#[frame_support::pallet]
mod pallet {
	use crate::{
		types::*,
		unsigned::miner::{self, BaseMiner},
		verifier::Verifier,
	};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use sp_npos_elections::EvaluateSupport;
	use sp_runtime::traits::{One, SaturatedConversion};

	/// convert a DispatchError to a custom InvalidTransaction with the inner code being the error
	/// number.
	fn dispatch_error_to_invalid(error: sp_runtime::DispatchError) -> InvalidTransaction {
		let error_number = match error {
			DispatchError::Module { error, .. } => error,
			_ => 0,
		};
		InvalidTransaction::Custom(error_number)
	}

	pub trait WeightInfo {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight;
	}

	impl WeightInfo for () {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
			Default::default()
		}
	}

	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config:
		crate::Config + frame_system::offchain::SendTransactionTypes<Call<Self>>
	{
		/// The repeat threshold of the offchain worker.
		///
		/// For example, if it is 5, that means that at least 5 blocks will elapse between attempts
		/// to submit the worker's solution.
		type OffchainRepeat: Get<Self::BlockNumber>;

		/// The priority of the unsigned transaction submitted in the unsigned-phase
		type MinerTxPriority: Get<TransactionPriority>;
		/// Maximum number of iteration of balancing that will be executed in the embedded miner of
		/// the pallet.
		type MinerMaxIterations: Get<u32>;
		/// Maximum weight that the miner should consume.
		///
		/// The miner will ensure that the total weight of the unsigned solution will not exceed
		/// this value, based on [`WeightInfo::submit_unsigned`].
		type MinerMaxWeight: Get<Weight>;
		/// Maximum length (bytes) that the mined solution should consume.
		///
		/// The miner will ensure that the total length of the unsigned solution will not exceed
		/// this value.
		type MinerMaxLength: Get<u32>;

		type WeightInfo: super::WeightInfo;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight((0, DispatchClass::Operational))]
		pub fn submit_unsigned(
			origin: OriginFor<T>,
			mut paged_solution: Box<PagedRawSolution<T>>,
			witness: SolutionOrSnapshotSize,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let error_message = "Invalid unsigned submission must produce invalid block and \
				 deprive validator from their authoring reward.";

			// phase, round, claimed score, page-count and hash are checked in pre-dispatch. we
			// don't check them here anymore.
			debug_assert!(Self::validate_unsigned_checks(&paged_solution).is_ok());

			// TODO: ensure correct witness

			let only_page = paged_solution
				.solution_pages
				.pop()
				.expect("length of `solution_pages` is always `T::Pages`, `T::Pages` is always greater than 1, can be popped; qed.");
			let supports = <T::Verifier as Verifier>::feasibility_check_page(
				only_page,
				crate::Pallet::<T>::msp(),
			)
			.expect(error_message);

			// we know that the claimed score is better then what we currently have because of the
			// pre-dispatch checks, now we only check if the claimed score was *valid*.

			let valid_score = supports.clone().evaluate();
			assert_eq!(valid_score, paged_solution.score, "{}", error_message);

			// all good, now we write this to the verifier directly.
			T::Verifier::force_set_single_page_verified_solution(supports, valid_score);

			Ok(None.into())
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			if let Call::submit_unsigned(paged_solution, _) = call {
				match source {
					TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ },
					_ => return InvalidTransaction::Call.into(),
				}

				let _ = Self::validate_unsigned_checks(paged_solution.as_ref())
					.map_err(|err| {
						log!(debug, "unsigned transaction validation failed due to {:?}", err);
						err
					})
					.map_err(dispatch_error_to_invalid)?;

				ValidTransaction::with_tag_prefix("OffchainElection")
					// The higher the score[0], the better a paged_solution is.
					.priority(
						T::MinerTxPriority::get()
							.saturating_add(paged_solution.score[0].saturated_into()),
					)
					// Used to deduplicate unsigned solutions: each validator should produce one
					// paged_solution per round at most, and solutions are not propagate.
					.and_provides(paged_solution.round)
					// Transaction should stay in the pool for the duration of the unsigned phase.
					.longevity(T::UnsignedPhase::get().saturated_into::<u64>())
					// We don't propagate this. This can never be validated at a remote node.
					.propagate(false)
					.build()
			} else {
				InvalidTransaction::Call.into()
			}
		}

		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			if let Call::submit_unsigned(solution, _) = call {
				Self::validate_unsigned_checks(solution.as_ref())
					.map_err(dispatch_error_to_invalid)
					.map_err(Into::into)
			} else {
				Err(InvalidTransaction::Call.into())
			}
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn offchain_worker(now: T::BlockNumber) {
			use sp_runtime::offchain::storage_lock::{BlockAndTime, StorageLock};

			// Create a lock with the maximum deadline of number of blocks in the unsigned phase.
			// This should only come useful in an **abrupt** termination of execution, otherwise the
			// guard will be dropped upon successful execution.
			let mut lock =
				StorageLock::<BlockAndTime<frame_system::Pallet<T>>>::with_block_deadline(
					miner::OffchainWorkerMiner::<T>::OFFCHAIN_LOCK,
					T::UnsignedPhase::get().saturated_into(),
				);

			match lock.try_lock() {
				Ok(_guard) => {
					Self::do_synchronized_offchain_worker(now);
				},
				Err(deadline) => {
					log!(debug, "offchain worker lock not released, deadline is {:?}", deadline);
				},
			};
		}
	}

	#[pallet::error]
	pub enum Error<T> {}

	impl<T: Config> Pallet<T> {
		/// Internal logic of the offchain worker, to be executed only when the offchain lock is
		/// acquired with success.
		fn do_synchronized_offchain_worker(now: T::BlockNumber) {
			use miner::OffchainWorkerMiner;

			let current_phase = crate::Pallet::<T>::current_phase();
			log!(trace, "lock for offchain worker acquired. Phase = {:?}", current_phase);
			match current_phase {
				Phase::Unsigned((true, opened)) if opened == now => {
					// Mine a new solution, cache it, and attempt to submit it
					let initial_output =
						OffchainWorkerMiner::<T>::ensure_offchain_repeat_frequency(now)
							.and_then(|_| OffchainWorkerMiner::<T>::mine_check_save_submit());
					log!(debug, "initial offchain worker output: {:?}", initial_output);
				},
				Phase::Unsigned((true, opened)) if opened < now => {
					// Try and resubmit the cached solution, and recompute ONLY if it is not
					// feasible.
					let resubmit_output =
						OffchainWorkerMiner::<T>::ensure_offchain_repeat_frequency(now).and_then(
							|_| OffchainWorkerMiner::<T>::restore_or_compute_then_maybe_submit(),
						);
					log!(debug, "resubmit offchain worker output: {:?}", resubmit_output);
				},
				_ => {},
			}

			// TODO: we don't clear the cache here. I don't think it has any implications. It will
			// be overwritten sometime in the future. In either case, once we add the snapshot hash
			// check, an outdated cache is never a problem. backport this as well.
		}

		/// The checks that should happen in the `ValidateUnsigned`'s `pre_dispatch` and
		/// `validate_unsigned` functions.
		///
		/// These check both for snapshot independent checks, and some checks that are specific to
		/// the unsigned phase.
		pub(crate) fn validate_unsigned_checks(
			paged_solution: &PagedRawSolution<T>,
		) -> DispatchResult {
			Self::unsigned_specific_checks(paged_solution)
				.and(crate::Pallet::<T>::snapshot_independent_checks(paged_solution))
		}

		/// The checks that are specific to the (this) unsigned pallet.
		///
		/// ensure solution has the correct phase, and it has only 1 page.
		pub fn unsigned_specific_checks(paged_solution: &PagedRawSolution<T>) -> DispatchResult {
			ensure!(
				crate::Pallet::<T>::current_phase().is_unsigned_open(),
				crate::Error::<T>::EarlySubmission
			);

			ensure!(paged_solution.solution_pages.len() == 1, crate::Error::<T>::WrongPageCount);

			Ok(())
		}

		#[cfg(test)]
		pub(crate) fn sanity_check() -> Result<(), &'static str> {
			Ok(())
		}
	}
}

#[cfg(test)]
mod validate_unsigned {
	use frame_support::{
		pallet_prelude::InvalidTransaction,
		unsigned::{TransactionSource, TransactionValidityError, ValidateUnsigned},
	};

	use super::*;
	use crate::{mock::*, types::*, verifier::Verifier, PagedRawSolution};

	#[test]
	fn retracts_weak_score() {
		ExtBuilder::default()
			.solution_improvement_threshold(sp_runtime::Perbill::from_percent(10))
			.build_and_execute(|| {
				roll_to_snapshot_created();

				let solution = mine_full_solution().unwrap();
				load_solution_for_verification(solution.clone());
				roll_to_full_verification();

				// Some good solution is queued now.
				assert_eq!(<VerifierPallet as Verifier>::queued_solution(), Some([55, 130, 8650]));

				roll_to_unsigned_open();

				// this is just worse
				let attempt = fake_unsigned_solution([20, 0, 0]);
				let call = super::Call::submit_unsigned(Box::new(attempt), witness());
				assert_eq!(
					UnsignedPallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err(),
					TransactionValidityError::Invalid(InvalidTransaction::Custom(2)),
				);

				// this is better, but not enough better.
				let insufficient_improvement = 55 * 105 / 100;
				let attempt = fake_unsigned_solution([insufficient_improvement, 0, 0]);
				let call = super::Call::submit_unsigned(Box::new(attempt), witness());
				assert_eq!(
					UnsignedPallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err(),
					TransactionValidityError::Invalid(InvalidTransaction::Custom(2)),
				);

				let sufficient_improvement = 55 * 115 / 100;
				let attempt = fake_unsigned_solution([sufficient_improvement, 0, 0]);
				let call = super::Call::submit_unsigned(Box::new(attempt), witness());
				assert!(UnsignedPallet::validate_unsigned(TransactionSource::Local, &call).is_ok());
			})
	}

	#[test]
	fn retracts_wrong_round() {
		todo!()
	}

	#[test]
	fn retracts_wrong_snapshot_hash() {
		todo!()
	}

	#[test]
	fn retracts_too_many_pages_unsigned() {
		// NOTE: unsigned solutions should have just 1 page, regardless of the configured
		// page count.
		todo!()
	}

	#[test]
	fn retracts_too_many_pages_signed() {
		// TODO: move to base pallet
		todo!()
	}

	#[test]
	fn retracts_wrong_phase() {
		ExtBuilder::default().build_and_execute(|| {
			let solution = fake_unsigned_solution([5, 0, 0]);

			let call = super::Call::submit_unsigned(Box::new(solution.clone()), witness());

			// initial
			assert_eq!(MultiBlock::current_phase(), Phase::Off);
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				// because EarlySubmission is index 0.
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));

			// signed
			roll_to(15);
			assert_eq!(MultiBlock::current_phase(), Phase::Signed);
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));

			// unsigned
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			assert_ok!(<UnsignedPallet as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			));
			assert_ok!(<UnsignedPallet as ValidateUnsigned>::pre_dispatch(&call));

			// unsigned -- but not enabled.
			<crate::CurrentPhase<Runtime>>::put(Phase::Unsigned((false, 25)));
			assert!(MultiBlock::current_phase().is_unsigned());
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
			));
			assert!(matches!(
				<UnsignedPallet as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(0))
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
				assert!(MultiBlock::current_phase().is_unsigned());

				let solution = fake_unsigned_solution([5, 0, 0]);
				let call = super::Call::submit_unsigned(Box::new(solution.clone()), witness());

				assert_eq!(
					<UnsignedPallet as ValidateUnsigned>::validate_unsigned(
						TransactionSource::Local,
						&call
					)
					.unwrap()
					.priority,
					25
				);
			})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{mock::*, AssignmentOf};
	use frame_benchmarking::Zero;
	use frame_support::{assert_noop, assert_ok, dispatch::Dispatchable, traits::OffchainWorker};
	use sp_npos_elections::IndexAssignment;
	use sp_runtime::{
		offchain::storage_lock::{BlockAndTime, StorageLock},
		traits::ValidateUnsigned,
		PerU16,
	};

	type Assignment = AssignmentOf<Runtime>;

	/*
	#[test]
	fn validate_unsigned_retracts_low_score() {
		ExtBuilder::default().desired_targets(0).build_and_execute(|| {
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			let solution =
				RawSolution::<TestNposSolution> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(Box::new(solution.clone()), witness());

			// initial
			assert!(<MultiBlock as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<MultiBlock as ValidateUnsigned>::pre_dispatch(&call).is_ok());

			// set a better score
			let ready = ReadySolution { score: [10, 0, 0], ..Default::default() };
			<QueuedSolution<Runtime>>::put(ready);

			// won't work anymore.
			assert!(matches!(
				<MultiBlock as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(2))
			));
			assert!(matches!(
				<MultiBlock as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(2))
			));
		})
	}

	#[test]
	fn validate_unsigned_retracts_incorrect_winner_count() {
		ExtBuilder::default().desired_targets(1).build_and_execute(|| {
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			let raw = RawSolution::<TestNposSolution> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(Box::new(raw.clone()), witness());
			assert_eq!(raw.solution.unique_targets().len(), 0);

			// won't work anymore.
			assert!(matches!(
				<MultiBlock as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call
				)
				.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(1))
			));
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
			assert!(MultiBlock::current_phase().is_unsigned());

			// This is in itself an invalid BS solution.
			let solution =
				RawSolution::<TestNposSolution> { score: [5, 0, 0], ..Default::default() };
			let call = Call::submit_unsigned(Box::new(solution.clone()), witness());
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
			assert!(MultiBlock::current_phase().is_unsigned());

			// This solution is unfeasible as well, but we won't even get there.
			let solution =
				RawSolution::<TestNposSolution> { score: [5, 0, 0], ..Default::default() };

			let mut correct_witness = witness();
			correct_witness.voters += 1;
			correct_witness.targets -= 1;
			let call = Call::submit_unsigned(Box::new(solution.clone()), correct_witness);
			let outer_call: OuterCall = call.into();
			let _ = outer_call.dispatch(Origin::none());
		})
	}

	#[test]
	fn miner_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// ensure we have snapshots in place.
			assert!(MultiBlock::snapshot().is_some());
			assert_eq!(MultiBlock::desired_targets().unwrap(), 2);

			// mine seq_phragmen solution with 2 iters.
			let (solution, witness) = MultiBlock::mine_solution(2).unwrap();

			// ensure this solution is valid.
			assert!(MultiBlock::queued_solution().is_none());
			assert_ok!(MultiBlock::submit_unsigned(Origin::none(), Box::new(solution), witness));
			assert!(MultiBlock::queued_solution().is_some());
		})
	}

	#[test]
	fn miner_trims_weight() {
		ExtBuilder::default()
			.miner_weight(100)
			.mock_weight_info(true)
			.build_and_execute(|| {
				roll_to(25);
				assert!(MultiBlock::current_phase().is_unsigned());

				let (raw, witness) = MultiBlock::mine_solution(2).unwrap();
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

				let (raw, witness) = MultiBlock::mine_solution(2).unwrap();
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
			assert!(MultiBlock::current_phase().is_unsigned());

			assert_eq!(
				MultiBlock::mine_check_save_submit().unwrap_err(),
				MinerError::PreDispatchChecksFailed(DispatchError::Module {
					index: 2,
					error: 1,
					message: Some("PreDispatchWrongWinnerCount"),
				}),
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
				assert!(MultiBlock::current_phase().is_unsigned());
				assert_eq!(MultiBlock::desired_targets().unwrap(), 1);

				// an initial solution
				let result = ElectionResult {
					// note: This second element of backing stake is not important here.
					winners: vec![(10, 10)],
					assignments: vec![Assignment {
						who: 10,
						distribution: vec![(10, PerU16::one())],
					}],
				};
				let (solution, witness) = MultiBlock::prepare_election_result(result).unwrap();
				assert_ok!(MultiBlock::unsigned_pre_dispatch_checks(&solution));
				assert_ok!(MultiBlock::submit_unsigned(
					Origin::none(),
					Box::new(solution),
					witness
				));
				assert_eq!(MultiBlock::queued_solution().unwrap().score[0], 10);

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
				let (solution, _) = MultiBlock::prepare_election_result(result).unwrap();
				// 12 is not 50% more than 10
				assert_eq!(solution.score[0], 12);
				assert_noop!(
					MultiBlock::unsigned_pre_dispatch_checks(&solution),
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
				let (solution, witness) = MultiBlock::prepare_election_result(result).unwrap();
				assert_eq!(solution.score[0], 17);

				// and it is fine
				assert_ok!(MultiBlock::unsigned_pre_dispatch_checks(&solution));
				assert_ok!(MultiBlock::submit_unsigned(
					Origin::none(),
					Box::new(solution),
					witness
				));
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
			MultiBlock::trim_assignments_length(encoded_len, &mut assignments, encoded_size_of)
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
			MultiBlock::trim_assignments_length(
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
			MultiBlock::trim_assignments_length(encoded_len - 1, &mut assignments, encoded_size_of)
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
			MultiBlock::trim_assignments_length(0, &mut assignments, encoded_size_of.clone())
				.unwrap();
			MultiBlock::trim_assignments_length(1, &mut assignments, encoded_size_of.clone())
				.unwrap();
			MultiBlock::trim_assignments_length(
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
			MultiBlock::trim_assignments_length(
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
			let solution = MultiBlock::mine_solution(0).unwrap();
			let max_length = <Runtime as Config>::MinerMaxLength::get();
			let solution_size = solution.0.solution.encoded_size();
			assert!(solution_size <= max_length as usize);

			// now set the max size to less than the actual size and regenerate
			<Runtime as Config>::MinerMaxLength::set(solution_size as u32 - 1);
			let solution = MultiBlock::mine_solution(0).unwrap();
			let max_length = <Runtime as Config>::MinerMaxLength::get();
			let solution_size = solution.0.solution.encoded_size();
			assert!(solution_size <= max_length as usize);
		});
	}

	*/
}
