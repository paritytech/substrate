// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Helpers for offchain worker election.

use crate::{
	Call, CompactAssignments, Module, NominatorIndex, OffchainAccuracy, Trait, ValidatorIndex,
};
use frame_system::offchain::SubmitTransaction;
use sp_phragmen::{
	build_support_map, evaluate_support, reduce, Assignment, ExtendedBalance, PhragmenResult,
	PhragmenScore,
};
use sp_runtime::offchain::storage::StorageValueRef;
use sp_runtime::PerThing;
use sp_runtime::RuntimeDebug;
use sp_std::{convert::TryInto, prelude::*};

/// Error types related to the offchain election machinery.
#[derive(RuntimeDebug)]
pub enum OffchainElectionError {
	/// Phragmen election returned None. This means less candidate that minimum number of needed
	/// validators were present. The chain is in trouble and not much that we can do about it.
	ElectionFailed,
	/// Submission to the transaction pool failed.
	PoolSubmissionFailed,
	/// The snapshot data is not available.
	SnapshotUnavailable,
	/// Error from phragmen crate. This usually relates to compact operation.
	PhragmenError(sp_phragmen::Error),
	/// One of the computed winners is invalid.
	InvalidWinner,
}

impl From<sp_phragmen::Error> for OffchainElectionError {
	fn from(e: sp_phragmen::Error) -> Self {
		Self::PhragmenError(e)
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
	// compute raw solution. Note that we use `OffchainAccuracy`.
	let PhragmenResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>()
		.ok_or(OffchainElectionError::ElectionFailed)?;

	// process and prepare it for submission.
	let (winners, compact, score) = prepare_submission::<T>(assignments, winners, true)?;

	// defensive-only: current era can never be none except genesis.
	let current_era = <Module<T>>::current_era().unwrap_or_default();

	// send it.
	let call = Call::submit_election_solution_unsigned(
		winners,
		compact,
		score,
		current_era,
	).into();

	SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call)
		.map_err(|_| OffchainElectionError::PoolSubmissionFailed)
}

/// Takes a phragmen result and spits out some data that can be submitted to the chain.
///
/// This does a lot of stuff; read the inline comments.
pub fn prepare_submission<T: Trait>(
	assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	winners: Vec<(T::AccountId, ExtendedBalance)>,
	do_reduce: bool,
) -> Result<(Vec<ValidatorIndex>, CompactAssignments, PhragmenScore), OffchainElectionError> where
	ExtendedBalance: From<<OffchainAccuracy as PerThing>::Inner>,
{
	// make sure that the snapshot is available.
	let snapshot_validators =
		<Module<T>>::snapshot_validators().ok_or(OffchainElectionError::SnapshotUnavailable)?;
	let snapshot_nominators =
		<Module<T>>::snapshot_nominators().ok_or(OffchainElectionError::SnapshotUnavailable)?;

	// all helper closures
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

	// Clean winners.
	let winners = winners
		.into_iter()
		.map(|(w, _)| w)
		.collect::<Vec<T::AccountId>>();

	// convert into absolute value and to obtain the reduced version.
	let mut staked = sp_phragmen::assignment_ratio_to_staked(
		assignments,
		<Module<T>>::slashable_balance_of_vote_weight,
	);

	if do_reduce {
		reduce(&mut staked);
	}

	// Convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment = sp_phragmen::assignment_staked_to_ratio(staked);

	// convert back to staked to compute the score in the receiver's accuracy. This can be done
	// nicer, for now we do it as such since this code is not time-critical. This ensure that the
	// score _predicted_ here is the same as the one computed on chain and you will not get a
	// `PhragmenBogusScore` error. This is totally NOT needed if we don't do reduce. This whole
	// _accuracy glitch_ happens because reduce breaks that assumption of rounding and **scale**.
	// The initial phragmen results are computed in `OffchainAccuracy` and the initial `staked`
	// assignment set is also all multiples of this value. After reduce, this no longer holds. Hence
	// converting to ratio thereafter is not trivially reversible.
	let score = {
		let staked = sp_phragmen::assignment_ratio_to_staked(
			low_accuracy_assignment.clone(),
			<Module<T>>::slashable_balance_of_vote_weight,
		);

		let (support_map, _) = build_support_map::<T::AccountId>(&winners, &staked);
		evaluate_support::<T::AccountId>(&support_map)
	};

	// compact encode the assignment.
	let compact = CompactAssignments::from_assignment(
		low_accuracy_assignment,
		nominator_index,
		validator_index,
	).map_err(|e| OffchainElectionError::from(e))?;

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

	Ok((winners_indexed, compact, score))
}
