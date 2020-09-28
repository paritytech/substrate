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

//! Helpers for offchain worker election.

use crate::{
	Call, CompactAssignments, ElectionSize, Module, NominatorIndex, Nominators, OffchainAccuracy,
	Trait, ValidatorIndex, WeightInfo,
};
use codec::Decode;
use frame_support::{traits::Get, weights::Weight};
use frame_system::offchain::SubmitTransaction;
use sp_npos_elections::{
	build_support_map, evaluate_support, reduce, Assignment, ElectionResult, ElectionScore,
	ExtendedBalance,
};
use sp_runtime::{
	offchain::storage::StorageValueRef, traits::TrailingZeroInput, PerThing, RuntimeDebug,
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
pub(crate) fn set_check_offchain_execution_status<T: Trait>(
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
pub(crate) fn compute_offchain_election<T: Trait>() -> Result<(), OffchainElectionError> {
	let iters = get_balancing_iters::<T>();
	// compute raw solution. Note that we use `OffchainAccuracy`.
	let ElectionResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>(iters)
		.ok_or(OffchainElectionError::ElectionFailed)?;

	// process and prepare it for submission.
	let (winners, compact, score, size) =
		prepare_submission::<T>(assignments, winners, true, T::MaximumUnsignedWeight::get())?;

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

/// A greedy effort to reduce the size if a solution.
// pub fn trim_solution_to_fit(
// 	winners: Vec<ValidatorIndex>,
// 	compact: CompactAssignments,
// 	size: ElectionSize,
// ) -> (Vec<ValidatorIndex>, CompactAssignments, ElectionSize) {

// }

/// Get a random number of iterations to run the balancing.
///
/// Uses the offchain seed to generate a random number.
pub fn get_balancing_iters<T: Trait>() -> usize {
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
pub fn maximum_compact_len<T: Trait>(
	winners_len: u32,
	size: ElectionSize,
	max_weight: Weight,
) -> u32 {
	// TODO: ofc we can do this nicer, if we rely on the internals of the weight function :\
	// TODO: check infinite loop is not possible.
	let mut voters = 0;
	loop {
		let weight = T::WeightInfo::submit_solution_better(
			size.validators.into(),
			size.nominators.into(),
			voters,
			winners_len,
		);
		if weight < max_weight {
			voters += 1;
		} else {
			break;
		}
	}
	voters
}

/// Greedily reduce the size of the a solution to fit into the block, wrt weight.
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
pub fn trim_to_weight<T: Trait, FN>(
	maximum_allowed_voters: u32,
	mut compact: CompactAssignments,
	nominator_index: FN,
) -> CompactAssignments
where
	for<'r> FN: Fn(&'r T::AccountId) -> Option<NominatorIndex>,
{
	use frame_support::IterableStorageMap;

	if let Some(to_remove) = compact.len().checked_sub(maximum_allowed_voters as usize) {
		// grab all voters and sort them by least stake.
		let mut voters_sorted = <Nominators<T>>::iter()
			.map(|(who, _)| {
				(
					who.clone(),
					<Module<T>>::slashable_balance_of_vote_weight(&who),
				)
			})
			.collect::<Vec<_>>();
		voters_sorted.sort_by_key(|(_, y)| *y);

		// start removing from the least stake. Iterate until we know enough have been removed.
		let mut removed = 0;
		for (i, _stake) in voters_sorted
			.iter()
			.map(|(who, stake)| (nominator_index(&who).unwrap(), stake))
		{
			if compact.remove_voter(i) {
				crate::log!(
					debug,
					"removed a voter at index {} with stake {:?} from compact to reduce the size",
					i,
					_stake,
				);
				removed += 1
			}

			if removed > to_remove {
				break;
			}
		}

		crate::log!(
			warn,
			"{} voters had to be removed from compact solution due to size limits.",
			removed
		);
		compact
	} else {
		// nada, return as-is
		crate::log!(
			info,
			"Compact solution did not get trimmed due to block weight limits.",
		);
		compact
	}
}

/// Takes an election result and spits out some data that can be submitted to the chain.
///
/// This does a lot of stuff; read the inline comments.
pub fn prepare_submission<T: Trait>(
	assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	winners: Vec<(T::AccountId, ExtendedBalance)>,
	do_reduce: bool,
	maximum_weight: Weight,
) -> Result<
	(
		Vec<ValidatorIndex>,
		CompactAssignments,
		ElectionScore,
		ElectionSize,
	),
	OffchainElectionError,
>
where
	ExtendedBalance: From<<OffchainAccuracy as PerThing>::Inner>,
{
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
		<Module<T>>::slashable_balance_of_vote_weight,
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
		maximum_compact_len::<T>(winners.len() as u32, size, maximum_weight);

	crate::log!(info, "Maximum weight = {:?} // current weight = {:?} // maximum voters = {:?} // current votes = {:?}",
		maximum_weight,
		T::WeightInfo::submit_solution_better(
				size.validators.into(),
				size.nominators.into(),
				compact.len() as u32,
				winners.len() as u32,
		),
		maximum_allowed_voters,
		compact.len(),
	);

	let compact = trim_to_weight::<T, _>(maximum_allowed_voters, compact, &nominator_index);

	// re-compute the score. We re-create what the chain will do.
	let score = {
		let compact = compact.clone();
		let assignments = compact.into_assignment(nominator_at, validator_at).unwrap();
		let staked = sp_npos_elections::assignment_ratio_to_staked(
			assignments,
			<Module<T>>::slashable_balance_of_vote_weight,
		);

		let support_map = build_support_map::<T::AccountId>(&winners, &staked)
			.map_err(|_| OffchainElectionError::ElectionFailed)?;
		evaluate_support::<T::AccountId>(&support_map)
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
