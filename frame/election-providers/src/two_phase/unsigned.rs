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

//! The unsigned phase implementation.

use crate::two_phase::*;
use frame_support::{dispatch::DispatchResult, unsigned::ValidateUnsigned};
use sp_npos_elections::{seq_phragmen, CompactSolution, ElectionResult};
use sp_runtime::{
	traits::TrailingZeroInput,
	transaction_validity::{
		InvalidTransaction, TransactionSource, TransactionValidity, TransactionValidityError,
		ValidTransaction,
	},
	PerU16, SaturatedConversion,
};
use sp_std::cmp::Ordering;

/// Witness data about the size of the election.
///
/// This is needed for proper weight calculation.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug, Default)]
pub struct WitnessData {
	/// Number of all voters.
	///
	/// This must match the on-chain snapshot.
	#[codec(compact)]
	voters: u32,
	/// Number of all targets.
	///
	/// This must match the on-chain snapshot.
	#[codec(compact)]
	target: u32,
}

/// Storage key used to store the persistent offchain worker status.
pub(crate) const OFFCHAIN_HEAD_DB: &[u8] = b"parity/unsigned-election/";
/// The repeat threshold of the offchain worker. This means we won't run the offchain worker twice
/// within a window of 5 blocks.
pub(crate) const OFFCHAIN_REPEAT: u32 = 5;
/// Default number of blocks for which the unsigned transaction should stay in the pool
pub(crate) const DEFAULT_LONGEVITY: u64 = 25;

impl<T: Trait> Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	/// Min a new npos solution.
	pub fn mine_solution(iters: usize) -> Result<RawSolution<CompactOf<T>>, Error> {
		let desired_targets = Self::desired_targets() as usize;
		let voters = Self::snapshot_voters().ok_or(Error::SnapshotUnAvailable)?;
		let targets = Self::snapshot_targets().ok_or(Error::SnapshotUnAvailable)?;

		seq_phragmen::<_, CompactAccuracyOf<T>>(desired_targets, targets, voters, Some((iters, 0)))
			.map_err(Into::into)
			.and_then(Self::prepare_election_result)
	}

	/// Convert a raw solution from [`sp_npos_elections::ElectionResult`] to [`RawSolution`], which
	/// is ready to be submitted to the chain.
	///
	/// Will always reduce the solution as well.
	pub fn prepare_election_result(
		election_result: ElectionResult<T::AccountId, CompactAccuracyOf<T>>,
	) -> Result<RawSolution<CompactOf<T>>, Error> {
		// storage items.
		let voters = Self::snapshot_voters().ok_or(Error::SnapshotUnAvailable)?;
		let targets = Self::snapshot_targets().ok_or(Error::SnapshotUnAvailable)?;

		// closures.
		let voter_index = crate::voter_index_fn!(voters, T::AccountId, T);
		let target_index = crate::target_index_fn!(targets, T::AccountId, T);
		let voter_at = crate::voter_at_fn!(voters, T::AccountId, T);
		let target_at = crate::target_at_fn!(targets, T::AccountId, T);
		let stake_of = crate::stake_of_fn!(voters, T::AccountId);

		let ElectionResult {
			assignments,
			winners,
		} = election_result;

		// convert to staked and reduce.
		let mut staked =
			sp_npos_elections::assignment_ratio_to_staked_normalized(assignments, &stake_of)
				.map_err::<Error, _>(Into::into)?;
		sp_npos_elections::reduce(&mut staked);

		// convert back to ration and make compact.
		let ratio = sp_npos_elections::assignment_staked_to_ratio_normalized(staked)?;
		let compact = <CompactOf<T>>::from_assignment(ratio, &voter_index, &target_index)?;

		// TODO
		let maximum_allowed_voters =
			Self::maximum_compact_len::<T::WeightInfo>(0, Default::default(), 0);
		let compact = Self::trim_compact(compact.len() as u32, compact, &voter_index)?;

		// re-calc score.
		let winners = sp_npos_elections::to_without_backing(winners);
		let score = compact
			.clone()
			.score(&winners, stake_of, voter_at, target_at)?;

		Ok(RawSolution { compact, score })
	}

	/// Get a random number of iterations to run the balancing in the OCW.
	///
	/// Uses the offchain seed to generate a random number, maxed with `T::UnsignedMaxIterations`.
	pub fn get_balancing_iters() -> usize {
		match T::UnsignedMaxIterations::get() {
			0 => 0,
			max @ _ => {
				let seed = sp_io::offchain::random_seed();
				let random = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
					.expect("input is padded with zeroes; qed")
					% max.saturating_add(1);
				random as usize
			}
		}
	}

	/// Greedily reduce the size of the a solution to fit into the block, w.r.t. weight.
	///
	/// The weight of the solution is foremost a function of the number of voters (i.e.
	/// `compact.len()`). Aside from this, the other components of the weight are invariant. The
	/// number of winners shall not be changed (otherwise the solution is invalid) and the
	/// `ElectionSize` is merely a representation of the total number of stakers.
	///
	/// Thus, we reside to stripping away some voters. This means only changing the `compact`
	/// struct.
	///
	/// Note that the solution is already computed, and the winners are elected based on the merit
	/// of teh entire stake in the system. Nonetheless, some of the voters will be removed further
	/// down the line.
	///
	/// Indeed, the score must be computed **after** this step. If this step reduces the score too
	/// much, then the solution will be discarded.
	pub fn trim_compact<FN>(
		maximum_allowed_voters: u32,
		mut compact: CompactOf<T>,
		nominator_index: FN,
	) -> Result<CompactOf<T>, Error>
	where
		for<'r> FN: Fn(&'r T::AccountId) -> Option<CompactVoterIndexOf<T>>,
	{
		match compact.len().checked_sub(maximum_allowed_voters as usize) {
			Some(to_remove) if to_remove > 0 => {
				// grab all voters and sort them by least stake.
				let voters = Self::snapshot_voters().ok_or(Error::SnapshotUnAvailable)?;
				let mut voters_sorted = voters
					.into_iter()
					.map(|(who, stake, _)| (who.clone(), stake))
					.collect::<Vec<_>>();
				voters_sorted.sort_by_key(|(_, y)| *y);

				// start removing from the least stake. Iterate until we know enough have been
				// removed.
				let mut removed = 0;
				for (maybe_index, _stake) in voters_sorted
					.iter()
					.map(|(who, stake)| (nominator_index(&who), stake))
				{
					let index = maybe_index.ok_or(Error::SnapshotUnAvailable)?;
					if compact.remove_voter(index) {
						removed += 1
					}

					if removed >= to_remove {
						break;
					}
				}

				Ok(compact)
			}
			_ => {
				// nada, return as-is
				Ok(compact)
			}
		}
	}

	/// Find the maximum `len` that a compact can have in order to fit into the block weight.
	///
	/// This only returns a value between zero and `size.nominators`.
	pub fn maximum_compact_len<W: WeightInfo>(
		_winners_len: u32,
		witness: WitnessData,
		max_weight: Weight,
	) -> u32 {
		if witness.voters < 1 {
			return witness.voters;
		}

		let max_voters = witness.voters.max(1);
		let mut voters = max_voters;

		// helper closures.
		let weight_with = |_voters: u32| -> Weight { W::submit_unsigned() };

		let next_voters = |current_weight: Weight, voters: u32, step: u32| -> Result<u32, ()> {
			match current_weight.cmp(&max_weight) {
				Ordering::Less => {
					let next_voters = voters.checked_add(step);
					match next_voters {
						Some(voters) if voters < max_voters => Ok(voters),
						_ => Err(()),
					}
				}
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
				}
				// we are out of bounds, break out of the loop.
				Err(()) => {
					break;
				}
				// we found the right value - early exit the function.
				Ok(next) => return next,
			}
			step = step / 2;
			current_weight = weight_with(voters);
		}

		// Time to finish. We might have reduced less than expected due to rounding error. Increase
		// one last time if we have any room left, the reduce until we are sure we are below limit.
		while voters + 1 <= max_voters && weight_with(voters + 1) < max_weight {
			voters += 1;
		}
		while voters.checked_sub(1).is_some() && weight_with(voters) > max_weight {
			voters -= 1;
		}

		debug_assert!(
			weight_with(voters.min(witness.voters)) <= max_weight,
			"weight_with({}) <= {}",
			voters.min(witness.voters),
			max_weight,
		);
		voters.min(witness.voters)
	}

	/// Checks if an execution of the offchain worker is permitted at the given block number, or not.
	///
	/// This essentially makes sure that we don't run on previous blocks in case of a re-org, and we
	/// don't run twice within a window of length [`OFFCHAIN_REPEAT`].
	///
	/// Returns `Ok(())` if offchain worker should happen, `Err(reason)` otherwise.
	pub(crate) fn set_check_offchain_execution_status(
		now: T::BlockNumber,
	) -> Result<(), &'static str> {
		let storage = sp_runtime::offchain::storage::StorageValueRef::persistent(&OFFCHAIN_HEAD_DB);
		let threshold = T::BlockNumber::from(OFFCHAIN_REPEAT);

		let mutate_stat =
			storage.mutate::<_, &'static str, _>(|maybe_head: Option<Option<T::BlockNumber>>| {
				match maybe_head {
					Some(Some(head)) if now < head => Err("fork."),
					Some(Some(head)) if now >= head && now <= head + threshold => {
						Err("recently executed.")
					}
					Some(Some(head)) if now > head + threshold => {
						// we can run again now. Write the new head.
						Ok(now)
					}
					_ => {
						// value doesn't exists. Probably this node just booted up. Write, and run
						Ok(now)
					}
				}
			});

		match mutate_stat {
			// all good
			Ok(Ok(_)) => Ok(()),
			// failed to write.
			Ok(Err(_)) => Err("failed to write to offchain db."),
			// fork etc.
			Err(why) => Err(why),
		}
	}

	/// Mine a new solution, and submit it back to the chian as an unsigned transaction.
	pub(crate) fn mine_and_submit() -> Result<(), Error> {
		let balancing = Self::get_balancing_iters();
		Self::mine_solution(balancing).map(|raw_solution| {
			// submit the raw solution to the pool.
			()
		})
	}

	pub(crate) fn pre_dispatch_checks(solution: &RawSolution<CompactOf<T>>) -> DispatchResult {
		// ensure solution is timely. Don't panic yet. This is a cheap check.
		ensure!(
			Self::current_phase().is_unsigned_open(),
			"UnsignedPhaseClosed"
		);

		// ensure score is being improved. Panic henceforth.
		ensure!(
			Self::queued_solution().map_or(true, |q: ReadySolution<_>| is_score_better::<Perbill>(
				solution.score,
				q.score,
				T::SolutionImprovementThreshold::get()
			)),
			"WeakSolution"
		);

		Ok(())
	}
}

#[allow(deprecated)]
impl<T: Trait> ValidateUnsigned for Module<T>
where
	ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>>,
{
	type Call = Call<T>;
	fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
		if let Call::submit_unsigned(solution) = call {
			// discard solution not coming from the local OCW.
			match source {
				TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ }
				_ => {
					return InvalidTransaction::Call.into();
				}
			}

			if let Err(_why) = Self::pre_dispatch_checks(solution) {
				return InvalidTransaction::Custom(99).into(); // TODO
			}

			ValidTransaction::with_tag_prefix("OffchainElection")
				// The higher the score[0], the better a solution is.
				.priority(
					T::UnsignedPriority::get().saturating_add(solution.score[0].saturated_into()),
				)
				// TODO: need some provides to de-duplicate.
				// TODO: we can do this better.
				.longevity(DEFAULT_LONGEVITY)
				// We don't propagate this. This can never the validated at a remote node.
				.propagate(false)
				.build()
		} else {
			InvalidTransaction::Call.into()
		}
	}

	fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
		if let Call::submit_unsigned(solution) = call {
			Self::pre_dispatch_checks(solution).map_err(|_| InvalidTransaction::Custom(99).into())
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}

// #[cfg(test)]
// mod test {
// 	#![allow(unused_variables)]
// 	use super::*;
// 	use crate::ElectionSize;

// 	struct Staking;

// 	impl crate::WeightInfo for Staking {
// 		fn bond() -> Weight {
// 			unimplemented!()
// 		}
// 		fn bond_extra() -> Weight {
// 			unimplemented!()
// 		}
// 		fn unbond() -> Weight {
// 			unimplemented!()
// 		}
// 		fn withdraw_unbonded_update(s: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn withdraw_unbonded_kill(s: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn validate() -> Weight {
// 			unimplemented!()
// 		}
// 		fn nominate(n: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn chill() -> Weight {
// 			unimplemented!()
// 		}
// 		fn set_payee() -> Weight {
// 			unimplemented!()
// 		}
// 		fn set_controller() -> Weight {
// 			unimplemented!()
// 		}
// 		fn set_validator_count() -> Weight {
// 			unimplemented!()
// 		}
// 		fn force_no_eras() -> Weight {
// 			unimplemented!()
// 		}
// 		fn force_new_era() -> Weight {
// 			unimplemented!()
// 		}
// 		fn force_new_era_always() -> Weight {
// 			unimplemented!()
// 		}
// 		fn set_invulnerables(v: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn force_unstake(s: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn cancel_deferred_slash(s: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn payout_stakers_dead_controller(n: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn payout_stakers_alive_staked(n: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn rebond(l: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn set_history_depth(e: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn reap_stash(s: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn new_era(v: u32, n: u32) -> Weight {
// 			unimplemented!()
// 		}
// 		fn submit_solution_better(v: u32, n: u32, a: u32, w: u32) -> Weight {
// 			(0 * v + 0 * n + 1000 * a + 0 * w) as Weight
// 		}
// 	}

// 	#[test]
// 	fn find_max_voter_binary_search_works() {
// 		let size = ElectionSize {
// 			validators: 0,
// 			nominators: 10,
// 		};

// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1990), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2990), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2999), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 3000), 3);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 3);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 5500), 5);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 7777), 7);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 9999), 9);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 10_000), 10);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 10_999), 10);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 11_000), 10);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 22_000), 10);

// 		let size = ElectionSize {
// 			validators: 0,
// 			nominators: 1,
// 		};

// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1990), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 1);

// 		let size = ElectionSize {
// 			validators: 0,
// 			nominators: 2,
// 		};

// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 2);
// 		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 2);
// 	}
// }

#[cfg(test)]
mod tests {
	use super::{mock::*, *};

	#[test]
	fn validate_unsigned_retracts_wrong_phase() {
		ExtBuilder::default().build_and_execute(|| {
			let solution = RawSolution::<TestCompact> {
				score: [5, 0, 0],
				..Default::default()
			};
			let call = Call::submit_unsigned(solution.clone());

			// initial
			assert_eq!(TwoPhase::current_phase(), Phase::Off);
			matches!(
				<TwoPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
					.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);
			matches!(
				<TwoPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);

			// signed
			roll_to(5);
			assert_eq!(TwoPhase::current_phase(), Phase::Signed);
			matches!(
				<TwoPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
					.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);
			matches!(
				<TwoPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);

			// unsigned
			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

			assert!(<TwoPhase as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<TwoPhase as ValidateUnsigned>::pre_dispatch(&call).is_ok());
		})
	}

	#[test]
	fn validate_unsigned_retracts_low_score() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

			let solution = RawSolution::<TestCompact> {
				score: [5, 0, 0],
				..Default::default()
			};
			let call = Call::submit_unsigned(solution.clone());

			// initial
			assert!(<TwoPhase as ValidateUnsigned>::validate_unsigned(
				TransactionSource::Local,
				&call
			)
			.is_ok());
			assert!(<TwoPhase as ValidateUnsigned>::pre_dispatch(&call).is_ok());

			// set a better score
			let ready = ReadySolution {
				score: [10, 0, 0],
				..Default::default()
			};
			<QueuedSolution<Runtime>>::put(ready);

			// won't work anymore.
			matches!(
				<TwoPhase as ValidateUnsigned>::validate_unsigned(TransactionSource::Local, &call)
					.unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);
			matches!(
				<TwoPhase as ValidateUnsigned>::pre_dispatch(&call).unwrap_err(),
				TransactionValidityError::Invalid(InvalidTransaction::Custom(99))
			);
		})
	}

	#[test]
	fn priority_is_set() {
		ExtBuilder::default()
			.unsigned_priority(20)
			.build_and_execute(|| {
				roll_to(15);
				assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

				let solution = RawSolution::<TestCompact> {
					score: [5, 0, 0],
					..Default::default()
				};
				let call = Call::submit_unsigned(solution.clone());

				// initial
				assert_eq!(
					<TwoPhase as ValidateUnsigned>::validate_unsigned(
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
	#[should_panic(
		expected = "Invalid unsigned submission must produce invalid block and deprive \
		validator from their authoring reward.: FeasibilityError::WrongWinnerCount"
	)]
	fn invalid_solution_panics() {
		ExtBuilder::default().build_and_execute(|| {
			use frame_support::dispatch::Dispatchable;
			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

			// This is in itself an invalid BS solution..
			let solution = RawSolution::<TestCompact> {
				score: [5, 0, 0],
				..Default::default()
			};
			let call = Call::submit_unsigned(solution.clone());
			let outer_call: OuterCall = call.into();
			let _ = outer_call.dispatch(Origin::none());
		})
	}

	#[test]
	fn miner_works() {
		ExtBuilder::default().build_and_execute(|| {
			roll_to(15);
			assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));

			// ensure we have snapshots in place.
			assert!(TwoPhase::snapshot_voters().is_some());
			assert!(TwoPhase::snapshot_targets().is_some());
			assert_eq!(TwoPhase::desired_targets(), 2);

			// mine seq_phragmen solution with 2 iters.
			let solution = TwoPhase::mine_solution(2).unwrap();

			// ensure this solution is valid.
			assert!(TwoPhase::queued_solution().is_none());
			assert_ok!(TwoPhase::submit_unsigned(Origin::none(), solution));
			assert!(TwoPhase::queued_solution().is_some());
		})
	}

	#[test]
	fn can_only_submit_threshold_better() {
		ExtBuilder::default()
			.desired_targets(1)
			.add_voter(7, 2, vec![10])
			.add_voter(8, 5, vec![10])
			.solution_improvement_threshold(Perbill::from_percent(50))
			.build_and_execute(|| {
				use sp_npos_elections::{Assignment, ElectionResult};
				roll_to(15);
				assert_eq!(TwoPhase::current_phase(), Phase::Unsigned((true, 15)));
				assert_eq!(TwoPhase::desired_targets(), 1);

				// an initial solution
				let result = ElectionResult {
					// note: This second element of backing stake is not important here.
					winners: vec![(10, 10)],
					assignments: vec![Assignment {
						who: 10,
						distribution: vec![(10, PerU16::one())],
					}],
				};
				assert_ok!(TwoPhase::submit_unsigned(
					Origin::none(),
					TwoPhase::prepare_election_result(result).unwrap(),
				));
				assert_eq!(TwoPhase::queued_solution().unwrap().score[0], 10);

				// trial 1: a solution who's score is only 2, i.e. 20% better in the first element.
				let result = ElectionResult {
					winners: vec![(10, 12)],
					assignments: vec![
						Assignment {
							who: 10,
							distribution: vec![(10, PerU16::one())],
						},
						Assignment {
							who: 7,
							// note: this percent doesn't even matter, in compact it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let solution = TwoPhase::prepare_election_result(result).unwrap();
				// 12 is not 50% more than 10
				assert_eq!(solution.score[0], 12);

				assert_noop!(
					TwoPhase::submit_unsigned(Origin::none(), solution),
					"WeakSolution"
				);

				// trial 2: a solution who's score is only 7, i.e. 70% better in the first element.
				let result = ElectionResult {
					winners: vec![(10, 12)],
					assignments: vec![
						Assignment {
							who: 10,
							distribution: vec![(10, PerU16::one())],
						},
						Assignment {
							who: 7,
							distribution: vec![(10, PerU16::one())],
						},
						Assignment {
							who: 8,
							// note: this percent doesn't even matter, in compact it is 100%.
							distribution: vec![(10, PerU16::one())],
						},
					],
				};
				let solution = TwoPhase::prepare_election_result(result).unwrap();
				assert_eq!(solution.score[0], 17);

				// and it is fine
				assert_ok!(TwoPhase::submit_unsigned(Origin::none(), solution));
			})
	}
}
