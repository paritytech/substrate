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

use crate::{Call, CompactAssignments, Module, SessionInterface, Trait};
use codec::Encode;
use frame_system::offchain::{SubmitUnsignedTransaction};
use sp_phragmen::{reduce, ExtendedBalance, PhragmenResult, StakedAssignment};
use sp_std::{prelude::*, cmp::Ordering};
use sp_runtime::{RuntimeAppPublic, RuntimeDebug};

#[derive(RuntimeDebug)]
pub(crate) enum OffchainElectionError {
	/// No signing key has been found on the current node that maps to a validators. This node
	/// should not run the offchain election code.
	NoSigningKey,
	/// Phragmen election returned None. This means less candidate that minimum number of needed
	/// validators were present. The chain is in trouble and not much that we can do about it.
	FailedElection,
}

/// Compares two sets of phragmen scores based on desirability and returns true if `that` is
/// better `this`.
///
/// Evaluation is done in a lexicographic manner.
///
/// Note that the third component should be minimized.
pub(crate) fn is_score_better(this: [ExtendedBalance; 3], that: [ExtendedBalance; 3]) -> bool {
	match that
		.iter()
		.enumerate()
		.map(|(i, e)| e.cmp(&this[i]))
		.collect::<Vec<Ordering>>()
		.as_slice()
	{
		[Ordering::Greater, _, _] => true,
		[Ordering::Equal, Ordering::Greater, _] => true,
		[Ordering::Equal, Ordering::Equal, Ordering::Less] => true,
		_ => false,
	}
}

/// The internal logic of the offchain worker of this module.
pub(crate) fn compute_offchain_election<T: Trait>() -> Result<(), OffchainElectionError> {
	let validator_keys = T::SessionInterface::keys::<T::KeyType>();
	let local_keys = T::KeyType::all();

	if let Some((index, ref pubkey)) = local_keys
		.into_iter()
		.find_map(|k|
			validator_keys
				.iter()
				.enumerate()
				.find_map(|(index, (_acc, maybe_vk))|
					maybe_vk.as_ref()
						.and_then(|vk| if *vk == k { Some((index, vk)) } else { None })
				)
		) {
			// k is a local key who is also among the validators.
			let PhragmenResult {
				winners,
				assignments,
			} = <Module<T>>::do_phragmen().ok_or(OffchainElectionError::FailedElection)?;

			// convert winners into just account ids.
			let winners: Vec<T::AccountId> = winners.into_iter().map(|(w, _)| w).collect();

			// convert into staked. This is needed to be able to reduce.
			let mut staked: Vec<StakedAssignment<T::AccountId>> = assignments
				.into_iter()
				.map(|a| a.into_staked::<_, _, T::CurrencyToVote>(
					<Module<T>>::slashable_balance_of,
					true,
				))
				.collect();

			// reduce the assignments. This will remove some additional edges.
			reduce(&mut staked);

			// get support and score.
			let (support, _) = sp_phragmen::build_support_map::<T::AccountId>(&winners, &staked);
			let score = sp_phragmen::evaluate_support(&support);

			// compact encode the assignment.
			let compact = <CompactAssignments<T::AccountId, ExtendedBalance>>::from_staked(staked);

			#[cfg(feature = "signed")]
			{
				unimplemented!();
			}

			#[cfg(not(feature = "signed"))]
			{
				let signature_payload =
					(winners.clone(), compact.clone(), score, index as u32).encode();
				let signature = pubkey.sign(&signature_payload).unwrap();
				let call: <T as Trait>::Call = Call::submit_election_solution_unsigned(
					winners,
					compact,
					score,
					index as u32,
					signature,
				)
				.into();
				let _result = T::SubmitTransaction::submit_unsigned(call);
			}

			Ok(())
		} else {
			Err(OffchainElectionError::NoSigningKey)
		}
}
