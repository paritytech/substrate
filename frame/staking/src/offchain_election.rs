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

use codec::Decode;
use crate::{
	Call, CompactAssignments, Module, NominatorIndex, OffchainAccuracy, Trait, ValidatorIndex,
	ElectionSize,
};
use frame_system::offchain::SubmitTransaction;
use sp_npos_elections::{
	build_support_map, evaluate_support, reduce, Assignment, ExtendedBalance, ElectionResult,
	ElectionScore, balance_solution,
};
use sp_runtime::offchain::storage::StorageValueRef;
use sp_runtime::{PerThing, RuntimeDebug, traits::{TrailingZeroInput, Zero}};
use frame_support::traits::Get;
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
	// compute raw solution. Note that we use `OffchainAccuracy`.
	let ElectionResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>()
		.ok_or(OffchainElectionError::ElectionFailed)?;

	// process and prepare it for submission.
	let (winners, compact, score, size) = prepare_submission::<T>(assignments, winners, true)?;

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


/// Takes an election result and spits out some data that can be submitted to the chain.
///
/// This does a lot of stuff; read the inline comments.
pub fn prepare_submission<T: Trait>(
	assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	winners: Vec<(T::AccountId, ExtendedBalance)>,
	do_reduce: bool,
) -> Result<(
	Vec<ValidatorIndex>,
	CompactAssignments,
	ElectionScore,
	ElectionSize,
), OffchainElectionError> where
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
	let winners = sp_npos_elections::to_without_backing(winners);

	// convert into absolute value and to obtain the reduced version.
	let mut staked = sp_npos_elections::assignment_ratio_to_staked(
		assignments,
		<Module<T>>::slashable_balance_of_vote_weight,
	);

	let (mut support_map, _) = build_support_map::<T::AccountId>(&winners, &staked);
	// balance a random number of times.
	let iterations_executed = match T::MaxIterations::get() {
		0 => {
			// Don't run balance_solution at all
			0
		}
		iterations @ _ => {
			let seed = sp_io::offchain::random_seed();
			let iterations = <u32>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
				.expect("input is padded with zeroes; qed") % iterations.saturating_add(1);
			balance_solution(
				&mut staked,
				&mut support_map,
				Zero::zero(),
				iterations as usize,
			)
		}
	};

	// reduce
	if do_reduce {
		reduce(&mut staked);
	}

	// Convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment = sp_npos_elections::assignment_staked_to_ratio_normalized(staked)
		.map_err(|e| OffchainElectionError::from(e))?;

	// convert back to staked to compute the score in the receiver's accuracy. This can be done
	// nicer, for now we do it as such since this code is not time-critical. This ensure that the
	// score _predicted_ here is the same as the one computed on chain and you will not get a
	// `PhragmenBogusScore` error. This is totally NOT needed if we don't do reduce. This whole
	// _accuracy glitch_ happens because reduce breaks that assumption of rounding and **scale**.
	// The initial phragmen results are computed in `OffchainAccuracy` and the initial `staked`
	// assignment set is also all multiples of this value. After reduce, this no longer holds. Hence
	// converting to ratio thereafter is not trivially reversible.
	let score = {
		let staked = sp_npos_elections::assignment_ratio_to_staked(
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

	// both conversions are safe; snapshots are not created if they exceed.
	let size = ElectionSize {
		validators: snapshot_validators.len() as ValidatorIndex,
		nominators: snapshot_nominators.len() as NominatorIndex,
	};

	crate::log!(
		info,
		"prepared solution after {} equalization iterations with score {:?}",
		iterations_executed,
		score,
	);

	Ok((winners_indexed, compact, score, size))
}
