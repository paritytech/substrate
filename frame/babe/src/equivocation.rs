// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
//! This module defines an offence type for BABE equivocations
//! and some utility traits to wire together:
//! - a system for reporting offences;
//! - a system for submitting unsigned transactions;
//! - a way to get the current block author;
//!
//! These can be used in an offchain context in order to submit equivocation
//! reporting extrinsics (from the client that's import BABE blocks).
//! And in a runtime context, so that the BABE pallet can validate the
//! equivocation proofs in the extrinsic and report the offences.
//!
//! IMPORTANT:
//! When using this module for enabling equivocation reporting it is required
//! that the `ValidateUnsigned` for the BABE pallet is used in the runtime
//! definition.

use frame_support::traits::{Get, KeyOwnerProofSystem};
use sp_consensus_babe::{EquivocationProof, Slot};
use sp_runtime::{
	transaction_validity::{
		InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
		TransactionValidityError, ValidTransaction,
	},
	DispatchResult, Perbill,
};
use sp_staking::{
	equivocation::EquivocationHandler as EquivocationHandlerT,
	offence::{Kind, Offence, ReportOffence},
	SessionIndex,
};
use sp_std::prelude::*;

use crate::{Call, Config, Pallet, LOG_TARGET};

/// Generic equivocation handler. This type implements `HandleEquivocation`
/// using existing subsystems that are part of frame (type bounds described
/// below) and will dispatch to them directly, it's only purpose is to wire all
/// subsystems together.
pub struct EquivocationHandler<I, R, L> {
	_phantom: sp_std::marker::PhantomData<(I, R, L)>,
}

impl<I, R, L> Default for EquivocationHandler<I, R, L> {
	fn default() -> Self {
		Self { _phantom: Default::default() }
	}
}

impl<T, R, L> EquivocationHandlerT for EquivocationHandler<T, R, L>
where
	// We use the authorship pallet
	// to fetch the current block
	// author and use
	// `offchain::SendTransactionTypes`
	// for unsigned extrinsic
	// creation and submission.
	T: Config + pallet_authorship::Config + frame_system::offchain::SendTransactionTypes<Call<T>>,

	// A system for reporting offences after valid equivocation reports are
	// processed.
	R: ReportOffence<
		T::AccountId,
		T::KeyOwnerIdentification,
		BabeEquivocationOffence<T::KeyOwnerIdentification>,
	>,
	// The longevity (in blocks) that the equivocation report is valid for. When using the staking
	// pallet this should be the bonding duration.
	L: Get<u64>,
{
	type ReportLongevity = L;

	type AccountId = T::AccountId;

	type KeyOwnerIdentification = T::KeyOwnerIdentification;

	type Offence = BabeEquivocationOffence<Self::KeyOwnerIdentification>;

	type EquivocationProof = EquivocationProof<T::Header>;

	type KeyOwnerProof = T::KeyOwnerProof;

	type ReportOffence = R;

	fn submit_unsigned_equivocation_report(
		equivocation_proof: Self::EquivocationProof,
		key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		use frame_system::offchain::SubmitTransaction;

		let call = Call::report_equivocation_unsigned {
			equivocation_proof: Box::new(equivocation_proof),
			key_owner_proof,
		};

		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(()) => log::info!(target: LOG_TARGET, "Submitted BABE equivocation report.",),
			Err(e) =>
				log::error!(target: LOG_TARGET, "Error submitting equivocation report: {:?}", e,),
		}

		Ok(())
	}

	fn block_author() -> Option<T::AccountId> {
		<pallet_authorship::Pallet<T>>::author()
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
						"rejecting unsigned report equivocation transaction because it is not local/in-block.",
					);

					return InvalidTransaction::Call.into()
				},
			}

			// check report staleness
			is_known_offence::<T>(equivocation_proof, key_owner_proof)?;

			let longevity = <T::HandleEquivocation as EquivocationHandlerT>::ReportLongevity::get();

			ValidTransaction::with_tag_prefix("BabeEquivocation")
				// We assign the maximum priority for any equivocation report.
				.priority(TransactionPriority::max_value())
				// Only one equivocation report for the same offender at the same slot.
				.and_provides((equivocation_proof.offender.clone(), *equivocation_proof.slot))
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
			is_known_offence::<T>(equivocation_proof, key_owner_proof)
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}

fn is_known_offence<T: Config>(
	equivocation_proof: &EquivocationProof<T::Header>,
	key_owner_proof: &T::KeyOwnerProof,
) -> Result<(), TransactionValidityError> {
	// check the membership proof to extract the offender's id
	let key = (sp_consensus_babe::KEY_TYPE, equivocation_proof.offender.clone());

	let offender = T::KeyOwnerProofSystem::check_proof(key, key_owner_proof.clone())
		.ok_or(InvalidTransaction::BadProof)?;

	// check if the offence has already been reported, and if so then we can discard the report.
	if T::HandleEquivocation::is_known_offence(&[offender], &equivocation_proof.slot) {
		Err(InvalidTransaction::Stale.into())
	} else {
		Ok(())
	}
}

/// A BABE equivocation offence report.
///
/// When a validator released two or more blocks at the same slot.
pub struct BabeEquivocationOffence<FullIdentification> {
	/// A babe slot in which this incident happened.
	pub slot: Slot,
	/// The session index in which the incident happened.
	pub session_index: SessionIndex,
	/// The size of the validator set at the time of the offence.
	pub validator_set_count: u32,
	/// The authority that produced the equivocation.
	pub offender: FullIdentification,
}

impl<FullIdentification: Clone> Offence<FullIdentification>
	for BabeEquivocationOffence<FullIdentification>
{
	const ID: Kind = *b"babe:equivocatio";
	type TimeSlot = Slot;

	fn offenders(&self) -> Vec<FullIdentification> {
		vec![self.offender.clone()]
	}

	fn session_index(&self) -> SessionIndex {
		self.session_index
	}

	fn validator_set_count(&self) -> u32 {
		self.validator_set_count
	}

	fn time_slot(&self) -> Self::TimeSlot {
		self.slot
	}

	fn slash_fraction(&self, offenders_count: u32) -> Perbill {
		// the formula is min((3k / n)^2, 1)
		let x = Perbill::from_rational(3 * offenders_count, self.validator_set_count);
		// _ ^ 2
		x.square()
	}
}
