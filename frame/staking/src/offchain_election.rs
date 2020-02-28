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
	Call, Module, Trait, ValidatorIndex, NominatorIndex, Compact, OffchainAccuracy,
};
use codec::Encode;
use frame_system::offchain::{SubmitUnsignedTransaction};
use frame_support::debug;
use sp_phragmen::{
	reduce, ExtendedBalance, PhragmenResult, Assignment, PhragmenScore,
	build_support_map, evaluate_support,
};
use sp_std::{prelude::*, convert::TryInto};
use sp_runtime::{RuntimeAppPublic, RuntimeDebug};
use sp_runtime::offchain::storage::StorageValueRef;
use sp_runtime::PerThing;

#[derive(RuntimeDebug)]
pub enum OffchainElectionError {
	/// No signing key has been found on the current node that maps to a validators. This node
	/// should not run the offchain election code.
	NoSigningKey,
	/// Signing operation failed.
	SigningFailed,
	/// Phragmen election returned None. This means less candidate that minimum number of needed
	/// validators were present. The chain is in trouble and not much that we can do about it.
	ElectionFailed,
	/// The snapshot data is not available.
	SnapshotUnavailable,
	/// Failed to create the compact type.
	CompactFailed,
}

/// The type of signature data encoded with the unsigned submission
pub(crate) type SignaturePayload<'a> = (
	&'a [ValidatorIndex],
	&'a Compact,
	&'a PhragmenScore,
	&'a u32,
);

pub(crate) const OFFCHAIN_HEAD_DB: &[u8] = b"parity/staking-election/";
const OFFCHAIN_REPEAT: u32 = 5;

pub(crate) fn set_check_offchain_execution_status<T: Trait>(
	now: T::BlockNumber,
) -> Result<(), &'static str> {
	let storage = StorageValueRef::persistent(&OFFCHAIN_HEAD_DB);
	let threshold = T::BlockNumber::from(OFFCHAIN_REPEAT);

	let mutate_stat = storage.mutate::<
		_,
		&'static str,
		_,
	>(|maybe_head: Option<Option<T::BlockNumber>>| {
		match maybe_head {
			Some(Some(head)) if now < head => Err("fork."),
			Some(Some(head)) if now >= head && now <= head + threshold => Err("recently executed."),
			Some(Some(head)) if now > head + threshold =>
				// we can run again now. Write the new head.
				Ok(now),
			_ =>
				// value doesn't exists. Probably this node just booted up. Write, and run
				Ok(now),
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

/// The internal logic of the offchain worker of this module.
pub(crate) fn compute_offchain_election<T: Trait>() -> Result<(), OffchainElectionError> {
	let keys = <Module<T>>::keys();
	let local_keys = T::KeyType::all();

	// For each local key is in the stored authority keys, try and submit. Breaks out after first
	// successful submission.
	for (index, ref pubkey) in local_keys.into_iter().filter_map(|key|
		keys.iter().enumerate().find(|(_, val_key)| **val_key == key)
	) {

		// compute raw solution.
		let PhragmenResult {
			winners,
			assignments,
		} = <Module<T>>::do_phragmen::<OffchainAccuracy>()
			.ok_or(OffchainElectionError::ElectionFailed)?;

		// process and prepare it for submission.
		let (winners, compact, score) = prepare_submission::<T>(
			assignments,
			winners,
			true,
		)?;

		// sign it.
		let signature_payload: SignaturePayload =
			(&winners, &compact, &score, &(index as u32));
		let signature = pubkey.sign(&signature_payload.encode())
			.ok_or(OffchainElectionError::SigningFailed)?;

		// send it.
		let call: <T as Trait>::Call = Call::submit_election_solution_unsigned(
			winners,
			compact,
			score,
			index as u32,
			signature,
		).into();

		let ok = T::SubmitTransaction::submit_unsigned(call).map_err(|_| {
			debug::native::warn!(
				target: "staking",
				"failed to submit offchain solution with key {:?}",
				pubkey,
			);
		}).is_ok();
		if ok { return Ok(()) }
	}

	// no key left and no submission.
	Err(OffchainElectionError::NoSigningKey)
}

/// Takes a phragmen result and the snapshot data and spits out some data that can be submitted to
/// the chain.
///
/// This does a lot of stuff; read the inline comments.
pub fn prepare_submission<T: Trait>(
	assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	winners: Vec<(T::AccountId, ExtendedBalance)>,
	do_reduce: bool,
) -> Result<(Vec<ValidatorIndex>, Compact, PhragmenScore), OffchainElectionError>
where
	ExtendedBalance: From<<OffchainAccuracy as PerThing>::Inner>,
{
	// make sure that the snapshot is available.
	let snapshot_validators = <Module<T>>::snapshot_validators()
		.ok_or(OffchainElectionError::SnapshotUnavailable)?;
	let snapshot_nominators = <Module<T>>::snapshot_nominators()
		.ok_or(OffchainElectionError::SnapshotUnavailable)?;

	// all helper closures
	let nominator_index = |a: &T::AccountId| -> Option<NominatorIndex> {
		snapshot_nominators.iter().position(|x| x == a).and_then(|i|
			<usize as TryInto<NominatorIndex>>::try_into(i).ok()
		)
	};
	let validator_index = |a: &T::AccountId| -> Option<ValidatorIndex> {
		snapshot_validators.iter().position(|x| x == a).and_then(|i|
			<usize as TryInto<ValidatorIndex>>::try_into(i).ok()
		)
	};

	// Clean winners.
	let winners = winners.into_iter().map(|(w, _)| w).collect::<Vec<T::AccountId>>();

	// convert into absolute value and to obtain the reduced version.
	let mut staked = sp_phragmen::assignment_ratio_to_staked(
		assignments,
		<Module<T>>::slashable_balance_of_extended,
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
	// accuracy glitch happens because reduce breaks that assumption of _scale_. The initial
	// phragmen results are computed in `OffchainAccuracy` and the initial `staked` assignment set
	// is also all multiples of this value. After reduce, this no longer holds. Hence converting to
	// ratio thereafter is not trivially reversible.
	let score = {
		let staked = sp_phragmen::assignment_ratio_to_staked(
			low_accuracy_assignment.clone(),
			<Module<T>>::slashable_balance_of_extended,
		);

		let (support_map, _) = build_support_map::<T::AccountId>(
			winners.as_slice(),
			staked.as_slice(),
		);
		evaluate_support::<T::AccountId>(&support_map)
	};

	// compact encode the assignment.
	let compact = Compact::from_assignment(
		low_accuracy_assignment,
		nominator_index,
		validator_index,
	).unwrap();

	// winners to index.
	let winners = winners.into_iter().map(|w|
		snapshot_validators.iter().position(|v| *v == w).unwrap().try_into().unwrap()
	).collect::<Vec<ValidatorIndex>>();

	Ok((winners, compact, score))
}
