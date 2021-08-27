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
pub use pallet::{
	Call, Config, Pallet, WeightInfo, __substrate_call_check, __substrate_validate_unsigned_check,
};

/// The miner.
pub mod miner;

#[frame_support::pallet]
mod pallet {
	use crate::{
		types::*,
		unsigned::miner::{self, BaseMiner},
		Verifier,
	};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::weights::Weight;
	use sp_npos_elections::EvaluateSupport;
	use sp_runtime::traits::{One, SaturatedConversion};

	pub trait WeightInfo {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight;
	}

	impl WeightInfo for () {
		fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
			Default::default()
		}
	}

	/// convert a DispatchError to a custom InvalidTransaction with the inner code being the error
	/// number.
	fn dispatch_error_to_invalid(error: DispatchError) -> InvalidTransaction {
		let error_number = match error {
			DispatchError::Module { error, .. } => error,
			_ => 0,
		};
		InvalidTransaction::Custom(error_number)
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
		#[pallet::constant]
		type OffchainRepeat: Get<Self::BlockNumber>;

		/// The priority of the unsigned transaction submitted in the unsigned-phase
		#[pallet::constant]
		type MinerTxPriority: Get<TransactionPriority>;
		/// Maximum number of iteration of balancing that will be executed in the embedded miner of
		/// the pallet.
		#[pallet::constant]
		type MinerMaxIterations: Get<u32>;

		/// Maximum weight that the miner should consume.
		///
		/// The miner will ensure that the total weight of the unsigned solution will not exceed
		/// this value, based on [`WeightInfo::submit_unsigned`].
		#[pallet::constant]
		type MinerMaxWeight: Get<Weight>;

		/// Maximum length (bytes) that the mined solution should consume.
		///
		/// The miner will ensure that the total length of the unsigned solution will not exceed
		/// this value.
		#[pallet::constant]
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
			mut paged_solution: Box<PagedRawSolution<SolutionOf<T>>>,
			witness: SolutionOrSnapshotSize,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;
			let error_message = "Invalid unsigned submission must produce invalid block and \
				 deprive validator from their authoring reward.";

			// phase, round, claimed score, page-count and hash are checked in pre-dispatch. we
			// don't check them here anymore.
			debug_assert!(Self::pre_dispatch_checks(&paged_solution).is_ok());

			// TODO: ensure correct witness
			// TODO: NOT GOOD, we start everything from high index to low, which means that we first
			// process our least staked nominators. we MUST change this to such that the index 0 of
			// the snapshot is the most important one, and is the one that is filled at first.

			let only_page = paged_solution
				.solution_pages
				.pop()
				.expect("length of solution_pages is checked to be 1, can be popped, qed;");
			let supports = <T::Verifier as Verifier>::feasibility_check_page(
				only_page,
				crate::Pallet::<T>::msp(),
			)
			.expect(error_message);

			// we know that the claimed score is better then what we currently have because of the
			// pre-dispatch checks, now we only check if the claimed score was *valid*.

			// TODO: make `evaluate` not consume self, I really dk why I initially wrote it as such.

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
				// Discard a paged_solution not coming from the local OCW.
				match source {
					TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ },
					_ => return InvalidTransaction::Call.into(),
				}

				let _ = Self::pre_dispatch_checks(paged_solution.as_ref())
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
				Self::pre_dispatch_checks(solution.as_ref())
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
					log!(debug, "initial offchain thread output: {:?}", initial_output);
				},
				Phase::Unsigned((true, opened)) if opened < now => {
					// Try and resubmit the cached solution, and recompute ONLY if it is not
					// feasible.
					let resubmit_output =
						OffchainWorkerMiner::<T>::ensure_offchain_repeat_frequency(now).and_then(
							|_| OffchainWorkerMiner::<T>::restore_or_compute_then_maybe_submit(),
						);
					log!(debug, "resubmit offchain thread output: {:?}", resubmit_output);
				},
				_ => {},
			}

			// After election finalization, clear OCW solution storage.
			// TODO: this is a bad pattern anyways, find another way for it.
			// if <frame_system::Pallet<T>>::events()
			// 	.into_iter()
			// 	.filter_map(|event_record| {
			// 		let local_event = <T as Config>::Event::from(event_record.event);
			// 		local_event.try_into().ok()
			// 	})
			// 	.any(|event| matches!(event, Event::ElectionFinalized(_)))
			// {
			// 	unsigned::kill_ocw_solution::<T>();
			// }
		}

		pub(crate) fn pre_dispatch_checks(
			paged_solution: &PagedRawSolution<SolutionOf<T>>,
		) -> DispatchResult {
			Self::unsigned_specific_checks(paged_solution)
				.and(crate::Pallet::<T>::snapshot_independent_checks(paged_solution))
		}

		pub fn unsigned_specific_checks(
			paged_solution: &PagedRawSolution<SolutionOf<T>>,
		) -> DispatchResult {
			// ensure solution is timely, and it has only 1 page..
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
	use crate::{mock::*, types::*, PagedRawSolution};

	#[test]
	fn retracts_weak_score() {
		todo!()
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
			let solution = PagedRawSolution::<TestNposSolution> {
				score: [5, 0, 0],
				solution_pages: vec![TestNposSolution::default()],
				..Default::default()
			};

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
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		mock::{
			roll_to, roll_to_with_ocw, BlockNumber, Call as OuterCall, ExtBuilder, Extrinsic,
			MinerMaxWeight, MultiBlock, Origin, Runtime, System, TestNposSolution, UnsignedPhase,
		},
		AssignmentOf, CurrentPhase, Phase,
	};
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
	fn priority_is_set() {
		ExtBuilder::default()
			.miner_tx_priority(20)
			.desired_targets(0)
			.build_and_execute(|| {
				roll_to(25);
				assert!(MultiBlock::current_phase().is_unsigned());

				let solution =
					RawSolution::<TestNposSolution> { score: [5, 0, 0], ..Default::default() };
				let call = Call::submit_unsigned(Box::new(solution.clone()), witness());

				assert_eq!(
					<MultiBlock as ValidateUnsigned>::validate_unsigned(
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
	fn ocw_lock_prevents_frequent_execution() {
		let (mut ext, _) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// first execution -- okay.
			assert!(MultiBlock::ensure_offchain_repeat_frequency(25).is_ok());

			// next block: rejected.
			assert_noop!(
				MultiBlock::ensure_offchain_repeat_frequency(26),
				MinerError::Lock("recently executed.")
			);

			// allowed after `OFFCHAIN_REPEAT`
			assert!(
				MultiBlock::ensure_offchain_repeat_frequency((26 + offchain_repeat).into()).is_ok()
			);

			// a fork like situation: re-execute last 3.
			assert!(MultiBlock::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 3).into()
			)
			.is_err());
			assert!(MultiBlock::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 2).into()
			)
			.is_err());
			assert!(MultiBlock::ensure_offchain_repeat_frequency(
				(26 + offchain_repeat - 1).into()
			)
			.is_err());
		})
	}

	#[test]
	fn ocw_lock_released_after_successful_execution() {
		// first, ensure that a successful execution releases the lock
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			let guard = StorageValueRef::persistent(&OFFCHAIN_LOCK);
			let last_block = StorageValueRef::persistent(OFFCHAIN_LAST_BLOCK);

			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// initially, the lock is not set.
			assert!(guard.get::<bool>().unwrap().is_none());

			// a successful a-z execution.
			MultiBlock::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);

			// afterwards, the lock is not set either..
			assert!(guard.get::<bool>().unwrap().is_none());
			assert_eq!(last_block.get::<BlockNumber>().unwrap(), Some(25));
		});
	}

	#[test]
	fn ocw_lock_prevents_overlapping_execution() {
		// ensure that if the guard is in hold, a new execution is not allowed.
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert!(MultiBlock::current_phase().is_unsigned());

			// artificially set the value, as if another thread is mid-way.
			let mut lock = StorageLock::<BlockAndTime<System>>::with_block_deadline(
				OFFCHAIN_LOCK,
				UnsignedPhase::get().saturated_into(),
			);
			let guard = lock.lock();

			// nothing submitted.
			MultiBlock::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 0);
			MultiBlock::offchain_worker(26);
			assert_eq!(pool.read().transactions.len(), 0);

			drop(guard);

			// 🎉 !
			MultiBlock::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
		});
	}

	#[test]
	fn ocw_only_runs_when_unsigned_open_now() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiBlock::offchain_worker(24);
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiBlock::offchain_worker(25);
			assert_eq!(pool.read().transactions.len(), 1);
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// locked, but also, has previously cached.
			MultiBlock::offchain_worker(26);
			assert!(pool.read().transactions.len().is_zero());
		})
	}

	#[test]
	fn ocw_clears_cache_after_election() {
		let (mut ext, _pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);
			storage.clear();

			assert!(
				!ocw_solution_exists::<Runtime>(),
				"no solution should be present before we mine one",
			);

			// creates and cache a solution
			MultiBlock::offchain_worker(25);
			assert!(
				ocw_solution_exists::<Runtime>(),
				"a solution must be cached after running the worker",
			);

			// after an election, the solution must be cleared
			// we don't actually care about the result of the election
			roll_to(26);
			let _ = MultiBlock::do_elect();
			MultiBlock::offchain_worker(26);
			assert!(!ocw_solution_exists::<Runtime>(), "elections must clear the ocw cache");
		})
	}

	#[test]
	fn ocw_resubmits_after_offchain_repeat() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			const BLOCK: u64 = 25;
			let block_plus = |delta: i32| ((BLOCK as i32) + delta) as u64;
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(BLOCK);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, BLOCK)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiBlock::offchain_worker(block_plus(-1));
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiBlock::offchain_worker(BLOCK);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// attempts to resubmit the tx after the threshold has expired
			// note that we have to add 1: the semantics forbid resubmission at
			// BLOCK + offchain_repeat
			MultiBlock::offchain_worker(block_plus(1 + offchain_repeat as i32));
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn ocw_regenerates_and_resubmits_after_offchain_repeat() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			const BLOCK: u64 = 25;
			let block_plus = |delta: i32| ((BLOCK as i32) + delta) as u64;
			let offchain_repeat = <Runtime as Config>::OffchainRepeat::get();

			roll_to(BLOCK);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, BLOCK)));

			// we must clear the offchain storage to ensure the offchain execution check doesn't get
			// in the way.
			let mut storage = StorageValueRef::persistent(&OFFCHAIN_LAST_BLOCK);

			MultiBlock::offchain_worker(block_plus(-1));
			assert!(pool.read().transactions.len().is_zero());
			storage.clear();

			// creates, caches, submits without expecting previous cache value
			MultiBlock::offchain_worker(BLOCK);
			assert_eq!(pool.read().transactions.len(), 1);
			let tx_cache = pool.read().transactions[0].clone();
			// assume that the tx has been processed
			pool.try_write().unwrap().transactions.clear();

			// remove the cached submitted tx
			// this ensures that when the resubmit window rolls around, we're ready to regenerate
			// from scratch if necessary
			let mut call_cache = StorageValueRef::persistent(&OFFCHAIN_CACHED_CALL);
			assert!(matches!(call_cache.get::<Call<Runtime>>(), Ok(Some(_call))));
			call_cache.clear();

			// attempts to resubmit the tx after the threshold has expired
			// note that we have to add 1: the semantics forbid resubmission at
			// BLOCK + offchain_repeat
			MultiBlock::offchain_worker(block_plus(1 + offchain_repeat as i32));
			assert_eq!(pool.read().transactions.len(), 1);

			// resubmitted tx is identical to first submission
			let tx = &pool.read().transactions[0];
			assert_eq!(&tx_cache, tx);
		})
	}

	#[test]
	fn ocw_can_submit_to_pool() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to_with_ocw(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			// OCW must have submitted now

			let encoded = pool.read().transactions[0].clone();
			let extrinsic: Extrinsic = Decode::decode(&mut &*encoded).unwrap();
			let call = extrinsic.call;
			assert!(matches!(call, OuterCall::MultiBlock(Call::submit_unsigned(..))));
		})
	}

	#[test]
	fn ocw_solution_must_have_correct_round() {
		let (mut ext, pool) = ExtBuilder::default().build_offchainify(0);
		ext.execute_with(|| {
			roll_to_with_ocw(25);
			assert_eq!(MultiBlock::current_phase(), Phase::Unsigned((true, 25)));
			// OCW must have submitted now
			// now, before we check the call, update the round
			<crate::Round<Runtime>>::mutate(|round| *round += 1);

			let encoded = pool.read().transactions[0].clone();
			let extrinsic = Extrinsic::decode(&mut &*encoded).unwrap();
			let call = match extrinsic.call {
				OuterCall::MultiBlock(call @ Call::submit_unsigned(..)) => call,
				_ => panic!("bad call: unexpected submission"),
			};

			// Custom(7) maps to PreDispatchChecksFailed
			let pre_dispatch_check_error =
				TransactionValidityError::Invalid(InvalidTransaction::Custom(7));
			assert_eq!(
				<MultiBlock as ValidateUnsigned>::validate_unsigned(
					TransactionSource::Local,
					&call,
				)
				.unwrap_err(),
				pre_dispatch_check_error,
			);
			assert_eq!(
				<MultiBlock as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				pre_dispatch_check_error,
			);
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
