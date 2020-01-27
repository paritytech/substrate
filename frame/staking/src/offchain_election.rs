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
use frame_system::offchain::{
	Signer, SubmitSignedTransaction, SubmitUnsignedTransaction, SignAndSubmitTransaction,
	CreateTransaction,
};
use sp_phragmen::{reduce, ExtendedBalance, PhragmenResult, StakedAssignment};
use sp_std::cmp::Ordering;
use sp_runtime::RuntimeAppPublic;

type SignAndSubmitOf<T> =
<
	<T as Trait>::SubmitTransaction
	as
	SubmitSignedTransaction<T, <T as Trait>::Call>
>::SignAndSubmit;

pub(crate) type PublicOf<T> =
<
	<SignAndSubmitOf<T> as SignAndSubmitTransaction<T, <T as Trait>::Call>>::CreateTransaction
	as
	CreateTransaction<
		T,
		<SignAndSubmitOf<T> as SignAndSubmitTransaction<T, <T as Trait>::Call>>::Extrinsic
	>
>::Public;

#[derive(Debug)]
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
pub(super) fn is_score_better(this: [ExtendedBalance; 3], that: [ExtendedBalance; 3]) -> bool {
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
pub(crate) fn compute_offchain_election<T: Trait>() -> Result<(), OffchainElectionError>
where
	<T as Trait>::KeyType: From<PublicOf<T>>
{
	let validators = T::SessionInterface::validators();

	// Check if current node can sign with any of the keys which correspond to a
	// validator. This basically says: proceed if the node is a validator.
	if T::SubmitTransaction::can_sign_with(Some(validators.clone())) {
		let PhragmenResult {
			winners,
			assignments,
		} = <Module<T>>::do_phragmen().ok_or(OffchainElectionError::FailedElection)?;

		// convert winners into just account ids.
		let winners: Vec<T::AccountId> = winners.into_iter().map(|(w, _)| w).collect();

		// convert into staked. This is needed to be able to reduce.
		let mut staked: Vec<StakedAssignment<T::AccountId>> = assignments
			.into_iter()
			.map(|a| a.into_staked::<_, _, T::CurrencyToVote>(<Module<T>>::slashable_balance_of))
			.collect();

		// reduce the assignments. This will remove some additional edges.
		reduce(&mut staked);

		// compact encode the assignment.
		let compact = <CompactAssignments<T::AccountId, ExtendedBalance>>::from_staked(staked);

		#[cfg(feature = "signed")]
		{
			// TODO: maybe we want to send from just one of them? we'll see.
			let call: <T as Trait>::Call = Call::submit_election_solution(winners, compact).into();
			let _result = T::SubmitTransaction::submit_signed_from(call, validators);
			dbg!(_result);
		}
		#[cfg(not(feature = "signed"))]
		{
			// TODO: this call is really not needed, we can do it manually instead
			// of `can_sign_with`.
			// TODO: we could use some error handling here.
			let local_keys = T::SubmitTransaction::find_all_local_keys();
			// loop for at least one account in the validators to sign with.
			local_keys
				.into_iter()
				.enumerate()
				.find(|(_, (acc, _))| validators.contains(&acc))
				.map(|(index, (_, pubkey))| {
					let signature_payload =
						(winners.clone(), compact.clone(), index as u32).encode();
					let pubkey: T::KeyType = pubkey.into();
					let signature = pubkey.sign(&signature_payload).unwrap();
					let call: <T as Trait>::Call = Call::submit_election_solution_unsigned(
						winners,
						compact,
						index as u32,
						signature,
					)
					.into();
					let _result = T::SubmitTransaction::submit_unsigned(call);
					dbg!(_result);
				});
		}
	} else {
		Err(OffchainElectionError::NoSigningKey)?;
	}

	Ok(())
}
