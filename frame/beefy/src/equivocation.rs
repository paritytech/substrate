// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! An opt-in utility module for reporting equivocations.
//!
//! This module defines an offence type for BEEFY equivocations
//! and some utility traits to wire together:
//! - a key ownership proof system (e.g. to prove that a given authority was part of a session);
//! - a system for reporting offences;
//! - a system for signing and submitting transactions;
//! - a way to get the current block author;
//!
//! These can be used in an offchain context in order to submit equivocation
//! reporting extrinsics (from the client that's running the BEEFY protocol).
//! And in a runtime context, so that the BEEFY pallet can validate the
//! equivocation proofs in the extrinsic and report the offences.
//!
//! IMPORTANT:
//! When using this module for enabling equivocation reporting it is required
//! that the `ValidateUnsigned` for the BEEFY pallet is used in the runtime
//! definition.

use codec::{self as codec, Decode, Encode};
use frame_support::{
	log,
	traits::{Get, KeyOwnerProofSystem},
};
use log::{error, info};
use sp_consensus_beefy::{EquivocationProof, ValidatorSetId, KEY_TYPE};
use sp_runtime::{
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		TransactionValidityError, ValidTransaction,
	},
	DispatchError, KeyTypeId, Perbill, RuntimeAppPublic,
};
use sp_session::{GetSessionNumber, GetValidatorCount};
use sp_staking::{
	offence::{Kind, Offence, OffenceReportSystem, ReportOffence},
	SessionIndex,
};
use sp_std::prelude::*;

use super::{Call, Config, Error, Pallet, LOG_TARGET};

/// A round number and set id which point on the time of an offence.
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Encode, Decode)]
pub struct TimeSlot<N: Copy + Clone + PartialOrd + Ord + Eq + PartialEq + Encode + Decode> {
	// The order of these matters for `derive(Ord)`.
	/// BEEFY Set ID.
	pub set_id: ValidatorSetId,
	/// Round number.
	pub round: N,
}

/// BEEFY equivocation offence report.
pub struct EquivocationOffence<Offender, N>
where
	N: Copy + Clone + PartialOrd + Ord + Eq + PartialEq + Encode + Decode,
{
	/// Time slot at which this incident happened.
	pub time_slot: TimeSlot<N>,
	/// The session index in which the incident happened.
	pub session_index: SessionIndex,
	/// The size of the validator set at the time of the offence.
	pub validator_set_count: u32,
	/// The authority which produced this equivocation.
	pub offender: Offender,
}

impl<Offender: Clone, N> Offence<Offender> for EquivocationOffence<Offender, N>
where
	N: Copy + Clone + PartialOrd + Ord + Eq + PartialEq + Encode + Decode,
{
	const ID: Kind = *b"beefy:equivocati";
	type TimeSlot = TimeSlot<N>;

	fn offenders(&self) -> Vec<Offender> {
		vec![self.offender.clone()]
	}

	fn session_index(&self) -> SessionIndex {
		self.session_index
	}

	fn validator_set_count(&self) -> u32 {
		self.validator_set_count
	}

	fn time_slot(&self) -> Self::TimeSlot {
		self.time_slot
	}

	// The formula is min((3k / n)^2, 1)
	// where k = offenders_number and n = validators_number
	fn slash_fraction(&self, offenders_count: u32) -> Perbill {
		// Perbill type domain is [0, 1] by definition
		Perbill::from_rational(3 * offenders_count, self.validator_set_count).square()
	}
}

/// BEEFY equivocation offence report system.
///
/// This type implements `OffenceReportSystem` such that:
/// - Equivocation reports are published on-chain as unsigned extrinsic via
///   `offchain::SendTransactionTypes`.
/// - On-chain validity checks and processing are mostly delegated to the user provided generic
///   types implementing `KeyOwnerProofSystem` and `ReportOffence` traits.
/// - Offence reporter for unsigned transactions is fetched via the the authorship pallet.
pub struct EquivocationReportSystem<T, R, P, L>(sp_std::marker::PhantomData<(T, R, P, L)>);

/// Equivocation evidence convenience alias.
pub type EquivocationEvidenceFor<T> = (
	EquivocationProof<
		<T as frame_system::Config>::BlockNumber,
		<T as Config>::BeefyId,
		<<T as Config>::BeefyId as RuntimeAppPublic>::Signature,
	>,
	<T as Config>::KeyOwnerProof,
);

impl<T, R, P, L> OffenceReportSystem<Option<T::AccountId>, EquivocationEvidenceFor<T>>
	for EquivocationReportSystem<T, R, P, L>
where
	T: Config + pallet_authorship::Config + frame_system::offchain::SendTransactionTypes<Call<T>>,
	R: ReportOffence<
		T::AccountId,
		P::IdentificationTuple,
		EquivocationOffence<P::IdentificationTuple, T::BlockNumber>,
	>,
	P: KeyOwnerProofSystem<(KeyTypeId, T::BeefyId), Proof = T::KeyOwnerProof>,
	P::IdentificationTuple: Clone,
	L: Get<u64>,
{
	type Longevity = L;

	fn publish_evidence(evidence: EquivocationEvidenceFor<T>) -> Result<(), ()> {
		use frame_system::offchain::SubmitTransaction;
		let (equivocation_proof, key_owner_proof) = evidence;

		let call = Call::report_equivocation_unsigned {
			equivocation_proof: Box::new(equivocation_proof),
			key_owner_proof,
		};

		let res = SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into());
		match res {
			Ok(_) => info!(target: LOG_TARGET, "Submitted equivocation report."),
			Err(e) => error!(target: LOG_TARGET, "Error submitting equivocation report: {:?}", e),
		}
		res
	}

	fn check_evidence(
		evidence: EquivocationEvidenceFor<T>,
	) -> Result<(), TransactionValidityError> {
		let (equivocation_proof, key_owner_proof) = evidence;

		// Check the membership proof to extract the offender's id
		let key = (KEY_TYPE, equivocation_proof.offender_id().clone());
		let offender = P::check_proof(key, key_owner_proof).ok_or(InvalidTransaction::BadProof)?;

		// Check if the offence has already been reported, and if so then we can discard the report.
		let time_slot = TimeSlot {
			set_id: equivocation_proof.set_id(),
			round: *equivocation_proof.round_number(),
		};

		if R::is_known_offence(&[offender], &time_slot) {
			Err(InvalidTransaction::Stale.into())
		} else {
			Ok(())
		}
	}

	fn process_evidence(
		reporter: Option<T::AccountId>,
		evidence: EquivocationEvidenceFor<T>,
	) -> Result<(), DispatchError> {
		let (equivocation_proof, key_owner_proof) = evidence;
		let reporter = reporter.or_else(|| <pallet_authorship::Pallet<T>>::author());
		let offender = equivocation_proof.offender_id().clone();

		// We check the equivocation within the context of its set id (and
		// associated session) and round. We also need to know the validator
		// set count at the time of the offence since it is required to calculate
		// the slash amount.
		let set_id = equivocation_proof.set_id();
		let round = *equivocation_proof.round_number();
		let session_index = key_owner_proof.session();
		let validator_set_count = key_owner_proof.validator_count();

		// Validate the key ownership proof extracting the id of the offender.
		let offender = P::check_proof((KEY_TYPE, offender), key_owner_proof)
			.ok_or(Error::<T>::InvalidKeyOwnershipProof)?;

		// Validate equivocation proof (check votes are different and signatures are valid).
		if !sp_consensus_beefy::check_equivocation_proof(&equivocation_proof) {
			return Err(Error::<T>::InvalidEquivocationProof.into())
		}

		// Check that the session id for the membership proof is within the
		// bounds of the set id reported in the equivocation.
		let set_id_session_index =
			crate::SetIdSession::<T>::get(set_id).ok_or(Error::<T>::InvalidEquivocationProof)?;
		if session_index != set_id_session_index {
			return Err(Error::<T>::InvalidEquivocationProof.into())
		}

		let offence = EquivocationOffence {
			time_slot: TimeSlot { set_id, round },
			session_index,
			validator_set_count,
			offender,
		};

		R::report_offence(reporter.into_iter().collect(), offence)
			.map_err(|_| Error::<T>::DuplicateOffenceReport)?;

		Ok(())
	}
}

/// Methods for the `ValidateUnsigned` implementation:
/// It restricts calls to `report_equivocation_unsigned` to local calls (i.e. extrinsics generated
/// on this node) or that already in a block. This guarantees that only block authors can include
/// unsigned equivocation reports.
impl<T: Config> Pallet<T> {
	pub fn validate_unsigned(source: TransactionSource, call: &Call<T>) -> TransactionValidity {
		if let Call::report_equivocation_unsigned { equivocation_proof, key_owner_proof } = call {
			// discard equivocation report not coming from the local node
			match source {
				TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ },
				_ => {
					log::warn!(
						target: LOG_TARGET,
						"rejecting unsigned report equivocation transaction because it is not local/in-block."
					);
					return InvalidTransaction::Call.into()
				},
			}

			let evidence = (*equivocation_proof.clone(), key_owner_proof.clone());
			T::EquivocationReportSystem::check_evidence(evidence)?;

			let longevity =
				<T::EquivocationReportSystem as OffenceReportSystem<_, _>>::Longevity::get();

			ValidTransaction::with_tag_prefix("BeefyEquivocation")
				// We assign the maximum priority for any equivocation report.
				.priority(TransactionPriority::MAX)
				// Only one equivocation report for the same offender at the same slot.
				.and_provides((
					equivocation_proof.offender_id().clone(),
					equivocation_proof.set_id(),
					*equivocation_proof.round_number(),
				))
				.longevity(longevity)
				// We don't propagate this. This can never be included on a remote node.
				.propagate(false)
				.build()
		} else {
			InvalidTransaction::Call.into()
		}
	}

	pub fn pre_dispatch(call: &Call<T>) -> Result<(), TransactionValidityError> {
		if let Call::report_equivocation_unsigned { equivocation_proof, key_owner_proof } = call {
			let evidence = (*equivocation_proof.clone(), key_owner_proof.clone());
			T::EquivocationReportSystem::check_evidence(evidence)
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}
