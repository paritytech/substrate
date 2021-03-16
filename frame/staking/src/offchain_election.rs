// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Helpers for offchain worker election.

use crate::{
	Call, CompactAssignments, ElectionSize, Module, NominatorIndex, Nominators, OffchainAccuracy,
	Config, ValidatorIndex, WeightInfo,
};
use codec::Decode;
use frame_support::{traits::Get, weights::Weight, IterableStorageMap};
use frame_system::offchain::SubmitTransaction;
use sp_npos_elections::{
	to_supports, EvaluateSupport, reduce, Assignment, ElectionResult, ElectionScore,
	ExtendedBalance, CompactSolution,
};
use sp_runtime::{
	offchain::storage::StorageValueRef, traits::TrailingZeroInput, RuntimeDebug,
};
use sp_std::{convert::TryInto, prelude::*};

/// Error types related to the offchain election machinery.
#[derive(RuntimeDebug)]
pub enum OffchainElectionError {
	/// election returned None. This means less candidate that minimum number of needed
	/// validators were present. The chain is in trouble and not much that we can do about it.
	ElectionFailed,
	/// Submission to the transaction pool failed.
	PoolSubmissionFailed,
	/// The snapshot data is not available.
	SnapshotUnavailable,
	/// Error from npos-election crate. This usually relates to compact operation.
	InternalElectionError(sp_npos_elections::Error),
	/// One of the computed winners is invalid.
	InvalidWinner,
	/// A nominator is not available in the snapshot.
	NominatorSnapshotCorrupt,
}

impl From<sp_npos_elections::Error> for OffchainElectionError {
	fn from(e: sp_npos_elections::Error) -> Self {
		Self::InternalElectionError(e)
	}
}

/// Storage key used to store the persistent offchain worker status.
pub(crate) const OFFCHAIN_HEAD_DB: &[u8] = b"parity/staking-election/";
/// The repeat threshold of the offchain worker. This means we won't run the offchain worker twice
/// within a window of 5 blocks.
pub(crate) const OFFCHAIN_REPEAT: u32 = 5;
/// Default number of blocks for which the unsigned transaction should stay in the pool
pub(crate) const DEFAULT_LONGEVITY: u64 = 25;

/// Checks if an execution of the offchain worker is permitted at the given block number, or not.
///
/// This essentially makes sure that we don't run on previous blocks in case of a re-org, and we
/// don't run twice within a window of length [`OFFCHAIN_REPEAT`].
///
/// Returns `Ok(())` if offchain worker should happen, `Err(reason)` otherwise.
pub(crate) fn set_check_offchain_execution_status<T: Config>(
	now: T::BlockNumber,
) -> Result<(), &'static str> {
	let storage = StorageValueRef::persistent(&OFFCHAIN_HEAD_DB);
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

/// The internal logic of the offchain worker of this module. This runs the phragmen election,
/// compacts and reduces the solution, computes the score and submits it back to the chain as an
/// unsigned transaction, without any signature.
pub(crate) fn compute_offchain_election<T: Config>() -> Result<(), OffchainElectionError> {
	let iters = get_balancing_iters::<T>();
	// compute raw solution. Note that we use `OffchainAccuracy`.
	let ElectionResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>(iters)
		.ok_or(OffchainElectionError::ElectionFailed)?;

	// process and prepare it for submission.
	let (winners, compact, score, size) = prepare_submission::<T>(
		assignments,
		winners,
		true,
		T::OffchainSolutionWeightLimit::get(),
	)?;

	crate::log!(
		info,
		"prepared a seq-phragmen solution with {} balancing iterations and score {:?}",
		iters,
		score,
	);

	// defensive-only: current era can never be none except genesis.
	let current_era = <Module<T>>::current_era().unwrap_or_default();

	// send it.
	let call = Call::submit_election_solution_unsigned(
		winners,
		compact,
		score,
		current_era,
		size,
	).into();

	SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call)
		.map_err(|_| OffchainElectionError::PoolSubmissionFailed)
}

/// Get a random number of iterations to run the balancing.
///
/// Uses the offchain seed to generate a random number.
pub fn get_balancing_iters<T: Config>() -> usize {
	match T::MaxIterations::get() {
		0 => 0,
		max @ _ => {
			let seed = sp_io::offchain::random_seed();
			let random = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
				.expect("input is padded with zeroes; qed") % max.saturating_add(1);
			random as usize
		}
	}
}

/// Find the maximum `len` that a compact can have in order to fit into the block weight.
///
/// This only returns a value between zero and `size.nominators`.
pub fn maximum_compact_len<W: crate::WeightInfo>(
	winners_len: u32,
	size: ElectionSize,
	max_weight: Weight,
) -> u32 {
	use sp_std::cmp::Ordering;

	if size.nominators < 1 {
		return size.nominators;
	}

	let max_voters = size.nominators.max(1);
	let mut voters = max_voters;

	// helper closures.
	let weight_with = |voters: u32| -> Weight {
		W::submit_solution_better(
			size.validators.into(),
			size.nominators.into(),
			voters,
			winners_len,
		)
	};

	let next_voters = |current_weight: Weight, voters: u32, step: u32| -> Result<u32, ()> {
		match current_weight.cmp(&max_weight) {
			Ordering::Less => {
				let next_voters = voters.checked_add(step);
				match next_voters {
					Some(voters) if voters < max_voters => Ok(voters),
					_ => Err(()),
				}
			},
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
			},
			// we are out of bounds, break out of the loop.
			Err(()) => {
				break;
			},
			// we found the right value - early exit the function.
			Ok(next) => return next
		}
		step = step / 2;
		current_weight = weight_with(voters);
	}


	// Time to finish.
	// We might have reduced less than expected due to rounding error. Increase one last time if we
	// have any room left, the reduce until we are sure we are below limit.
	while voters + 1 <= max_voters && weight_with(voters + 1) < max_weight {
		voters += 1;
	}
	while voters.checked_sub(1).is_some() && weight_with(voters) > max_weight {
		voters -= 1;
	}

	debug_assert!(
		weight_with(voters.min(size.nominators)) <= max_weight,
		"weight_with({}) <= {}", voters.min(size.nominators), max_weight,
	);
	voters.min(size.nominators)
}

/// Greedily reduce the size of the a solution to fit into the block, w.r.t. weight.
///
/// The weight of the solution is foremost a function of the number of voters (i.e.
/// `compact.len()`). Aside from this, the other components of the weight are invariant. The number
/// of winners shall not be changed (otherwise the solution is invalid) and the `ElectionSize` is
/// merely a representation of the total number of stakers.
///
/// Thus, we reside to stripping away some voters. This means only changing the `compact` struct.
///
/// Note that the solution is already computed, and the winners are elected based on the merit of
/// teh entire stake in the system. Nonetheless, some of the voters will be removed further down the
/// line.
///
/// Indeed, the score must be computed **after** this step. If this step reduces the score too much,
/// then the solution will be discarded.
pub fn trim_to_weight<T: Config, FN>(
	maximum_allowed_voters: u32,
	mut compact: CompactAssignments,
	nominator_index: FN,
) -> Result<CompactAssignments, OffchainElectionError>
where
	for<'r> FN: Fn(&'r T::AccountId) -> Option<NominatorIndex>,
{
	match compact.voter_count().checked_sub(maximum_allowed_voters as usize) {
		Some(to_remove) if to_remove > 0 => {
			// grab all voters and sort them by least stake.
			let balance_of = <Module<T>>::slashable_balance_of_fn();
			let mut voters_sorted = <Nominators<T>>::iter()
				.map(|(who, _)| (who.clone(), balance_of(&who)))
				.collect::<Vec<_>>();
			voters_sorted.sort_by_key(|(_, y)| *y);

			// start removing from the least stake. Iterate until we know enough have been removed.
			let mut removed = 0;
			for (maybe_index, _stake) in voters_sorted
				.iter()
				.map(|(who, stake)| (nominator_index(&who), stake))
			{
				let index = maybe_index.ok_or(OffchainElectionError::NominatorSnapshotCorrupt)?;
				if compact.remove_voter(index) {
					crate::log!(
						trace,
						"removed a voter at index {} with stake {:?} from compact to reduce the size",
						index,
						_stake,
					);
					removed += 1
				}

				if removed >= to_remove {
					break;
				}
			}

			crate::log!(
				warn,
				"{} nominators out of {} had to be removed from compact solution due to size \
				 limits.",
				removed,
				compact.voter_count() + removed,
			);
			Ok(compact)
		}
		_ => {
			// nada, return as-is
			crate::log!(info, "Compact solution did not get trimmed due to block weight limits.",);
			Ok(compact)
		}
	}
}

/// Takes an election result and spits out some data that can be submitted to the chain.
///
/// This does a lot of stuff; read the inline comments.
pub fn prepare_submission<T: Config>(
	assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	winners: Vec<(T::AccountId, ExtendedBalance)>,
	do_reduce: bool,
	maximum_weight: Weight,
) -> Result<
	(Vec<ValidatorIndex>, CompactAssignments, ElectionScore, ElectionSize),
	OffchainElectionError,
> {
	// make sure that the snapshot is available.
	let snapshot_validators =
		<Module<T>>::snapshot_validators().ok_or(OffchainElectionError::SnapshotUnavailable)?;
	let snapshot_nominators =
		<Module<T>>::snapshot_nominators().ok_or(OffchainElectionError::SnapshotUnavailable)?;

	// all helper closures that we'd ever need.
	let nominator_index = |a: &T::AccountId| -> Option<NominatorIndex> {
		snapshot_nominators
			.iter()
			.position(|x| x == a)
			.and_then(|i| <usize as TryInto<NominatorIndex>>::try_into(i).ok())
	};
	let validator_index = |a: &T::AccountId| -> Option<ValidatorIndex> {
		snapshot_validators
			.iter()
			.position(|x| x == a)
			.and_then(|i| <usize as TryInto<ValidatorIndex>>::try_into(i).ok())
	};
	let nominator_at = |i: NominatorIndex| -> Option<T::AccountId> {
		snapshot_nominators.get(i as usize).cloned()
	};

	let validator_at = |i: ValidatorIndex| -> Option<T::AccountId> {
		snapshot_validators.get(i as usize).cloned()
	};

	// both conversions are safe; snapshots are not created if they exceed.
	let size = ElectionSize {
		validators: snapshot_validators.len() as ValidatorIndex,
		nominators: snapshot_nominators.len() as NominatorIndex,
	};

	// Clean winners.
	let winners = sp_npos_elections::to_without_backing(winners);

	// convert into absolute value and to obtain the reduced version.
	let mut staked = sp_npos_elections::assignment_ratio_to_staked(
		assignments,
		<Module<T>>::slashable_balance_of_fn(),
	);

	// reduce
	if do_reduce {
		reduce(&mut staked);
	}

	// Convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment = sp_npos_elections::assignment_staked_to_ratio_normalized(staked)
		.map_err(|e| OffchainElectionError::from(e))?;

	// compact encode the assignment.
	let compact = CompactAssignments::from_assignment(
		low_accuracy_assignment,
		nominator_index,
		validator_index,
	)
	.map_err(|e| OffchainElectionError::from(e))?;

	// potentially reduce the size of the compact to fit weight.
	let maximum_allowed_voters =
		maximum_compact_len::<T::WeightInfo>(winners.len() as u32, size, maximum_weight);

	crate::log!(
		debug,
		"Maximum weight = {:?} // current weight = {:?} // maximum voters = {:?} // current votes \
		 = {:?}",
		maximum_weight,
		T::WeightInfo::submit_solution_better(
			size.validators.into(),
			size.nominators.into(),
			compact.voter_count() as u32,
			winners.len() as u32,
		),
		maximum_allowed_voters,
		compact.voter_count(),
	);

	let compact = trim_to_weight::<T, _>(maximum_allowed_voters, compact, &nominator_index)?;

	// re-compute the score. We re-create what the chain will do. This is a bit verbose and wastes
	// CPU time, but it is necessary to ensure that the score that we claim is the same as the one
	// calculated by the chain.
	let score = {
		let compact = compact.clone();
		let assignments = compact.into_assignment(nominator_at, validator_at).unwrap();
		let staked = sp_npos_elections::assignment_ratio_to_staked(
			assignments.clone(),
			<Module<T>>::slashable_balance_of_fn(),
		);

		let support_map = to_supports::<T::AccountId>(&winners, &staked)
			.map_err(|_| OffchainElectionError::ElectionFailed)?;
		support_map.evaluate()
	};

	// winners to index. Use a simple for loop for a more expressive early exit in case of error.
	let mut winners_indexed: Vec<ValidatorIndex> = Vec::with_capacity(winners.len());
	for w in winners {
		if let Some(idx) = snapshot_validators.iter().position(|v| *v == w) {
			let compact_index: ValidatorIndex = idx
				.try_into()
				.map_err(|_| OffchainElectionError::InvalidWinner)?;
			winners_indexed.push(compact_index);
		} else {
			return Err(OffchainElectionError::InvalidWinner);
		}
	}

	Ok((winners_indexed, compact, score, size))
}

#[cfg(test)]
mod test {
	#![allow(unused_variables)]
	use super::*;
	use crate::ElectionSize;

	struct Staking;

	impl crate::WeightInfo for Staking {
		fn bond() -> Weight {
			unimplemented!()
		}
		fn bond_extra() -> Weight {
			unimplemented!()
		}
		fn unbond() -> Weight {
			unimplemented!()
		}
		fn withdraw_unbonded_update(s: u32) -> Weight {
			unimplemented!()
		}
		fn withdraw_unbonded_kill(s: u32) -> Weight {
			unimplemented!()
		}
		fn validate() -> Weight {
			unimplemented!()
		}
		fn nominate(n: u32) -> Weight {
			unimplemented!()
		}
		fn chill() -> Weight {
			unimplemented!()
		}
		fn set_payee() -> Weight {
			unimplemented!()
		}
		fn set_controller() -> Weight {
			unimplemented!()
		}
		fn set_validator_count() -> Weight {
			unimplemented!()
		}
		fn force_no_eras() -> Weight {
			unimplemented!()
		}
		fn force_new_era() -> Weight {
			unimplemented!()
		}
		fn force_new_era_always() -> Weight {
			unimplemented!()
		}
		fn set_invulnerables(v: u32) -> Weight {
			unimplemented!()
		}
		fn force_unstake(s: u32) -> Weight {
			unimplemented!()
		}
		fn cancel_deferred_slash(s: u32) -> Weight {
			unimplemented!()
		}
		fn payout_stakers_dead_controller(n: u32) -> Weight {
			unimplemented!()
		}
		fn payout_stakers_alive_staked(n: u32) -> Weight {
			unimplemented!()
		}
		fn rebond(l: u32) -> Weight {
			unimplemented!()
		}
		fn set_history_depth(e: u32) -> Weight {
			unimplemented!()
		}
		fn reap_stash(s: u32) -> Weight {
			unimplemented!()
		}
		fn new_era(v: u32, n: u32) -> Weight {
			unimplemented!()
		}
		fn submit_solution_better(v: u32, n: u32, a: u32, w: u32) -> Weight {
			(0 * v + 0 * n + 1000 * a + 0 * w) as Weight
		}
		fn kick(w: u32) -> Weight {
			unimplemented!()
		}
		fn get_npos_voters(v: u32, n: u32, s: u32) -> Weight {
			unimplemented!()
		}
		fn get_npos_targets(v: u32) -> Weight {
			unimplemented!()
		}
	}

	#[test]
	fn find_max_voter_binary_search_works() {
		let size = ElectionSize {
			validators: 0,
			nominators: 10,
		};

		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1990), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2990), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2999), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 3000), 3);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 3);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 5500), 5);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 7777), 7);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 9999), 9);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 10_000), 10);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 10_999), 10);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 11_000), 10);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 22_000), 10);

		let size = ElectionSize {
			validators: 0,
			nominators: 1,
		};

		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1990), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 1);

		let size = ElectionSize {
			validators: 0,
			nominators: 2,
		};

		assert_eq!(maximum_compact_len::<Staking>(0, size, 0), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 999), 0);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1000), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1001), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 1999), 1);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2000), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2001), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 2010), 2);
		assert_eq!(maximum_compact_len::<Staking>(0, size, 3333), 2);
	}
}
