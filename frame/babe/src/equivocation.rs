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

//!
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
//!

use frame_support::{debug, traits::KeyOwnerProofSystem};
use sp_consensus_babe::{EquivocationProof, SlotNumber};
use sp_runtime::transaction_validity::{
	InvalidTransaction, TransactionPriority, TransactionSource, TransactionValidity,
	TransactionValidityError, ValidTransaction,
};
use sp_runtime::{DispatchResult, Perbill};
use sp_staking::{
	offence::{Kind, Offence, OffenceError, ReportOffence},
	SessionIndex,
};
use sp_std::prelude::*;

use crate::{Call, Module, Config};

/// A trait with utility methods for handling equivocation reports in BABE.
/// The trait provides methods for reporting an offence triggered by a valid
/// equivocation report, checking the current block author (to declare as the
/// reporter), and also for creating and submitting equivocation report
/// extrinsics (useful only in offchain context).
pub trait HandleEquivocation<T: Config> {
	/// Report an offence proved by the given reporters.
	fn report_offence(
		reporters: Vec<T::AccountId>,
		offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError>;

	/// Returns true if all of the offenders at the given time slot have already been reported.
	fn is_known_offence(offenders: &[T::KeyOwnerIdentification], time_slot: &SlotNumber) -> bool;

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult;

	/// Fetch the current block author id, if defined.
	fn block_author() -> Option<T::AccountId>;
}

impl<T: Config> HandleEquivocation<T> for () {
	fn report_offence(
		_reporters: Vec<T::AccountId>,
		_offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError> {
		Ok(())
	}

	fn is_known_offence(_offenders: &[T::KeyOwnerIdentification], _time_slot: &SlotNumber) -> bool {
		true
	}

	fn submit_unsigned_equivocation_report(
		_equivocation_proof: EquivocationProof<T::Header>,
		_key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}

	fn block_author() -> Option<T::AccountId> {
		None
	}
}

/// Generic equivocation handler. This type implements `HandleEquivocation`
/// using existing subsystems that are part of frame (type bounds described
/// below) and will dispatch to them directly, it's only purpose is to wire all
/// subsystems together.
pub struct EquivocationHandler<I, R> {
	_phantom: sp_std::marker::PhantomData<(I, R)>,
}

impl<I, R> Default for EquivocationHandler<I, R> {
	fn default() -> Self {
		Self {
			_phantom: Default::default(),
		}
	}
}

impl<T, R> HandleEquivocation<T> for EquivocationHandler<T::KeyOwnerIdentification, R>
where
	// We use the authorship pallet to fetch the current block author and use
	// `offchain::SendTransactionTypes` for unsigned extrinsic creation and
	// submission.
	T: Config + pallet_authorship::Config + frame_system::offchain::SendTransactionTypes<Call<T>>,
	// A system for reporting offences after valid equivocation reports are
	// processed.
	R: ReportOffence<
		T::AccountId,
		T::KeyOwnerIdentification,
		BabeEquivocationOffence<T::KeyOwnerIdentification>,
	>,
{
	fn report_offence(
		reporters: Vec<T::AccountId>,
		offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError> {
		R::report_offence(reporters, offence)
	}

	fn is_known_offence(offenders: &[T::KeyOwnerIdentification], time_slot: &SlotNumber) -> bool {
		R::is_known_offence(offenders, time_slot)
	}

	fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		use frame_system::offchain::SubmitTransaction;

		let call = Call::report_equivocation_unsigned(equivocation_proof, key_owner_proof);

		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(()) => debug::info!("Submitted BABE equivocation report."),
			Err(e) => debug::error!("Error submitting equivocation report: {:?}", e),
		}

		Ok(())
	}

	fn block_author() -> Option<T::AccountId> {
		Some(<pallet_authorship::Module<T>>::author())
	}
}

/// A `ValidateUnsigned` implementation that restricts calls to `report_equivocation_unsigned`
/// to local calls (i.e. extrinsics generated on this node) or that already in a block. This
/// guarantees that only block authors can include unsigned equivocation reports.
impl<T: Config> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;
	fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
		if let Call::report_equivocation_unsigned(equivocation_proof, _) = call {
			// discard equivocation report not coming from the local node
			match source {
				TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ }
				_ => {
					debug::warn!(
						target: "babe",
						"rejecting unsigned report equivocation transaction because it is not local/in-block."
					);

					return InvalidTransaction::Call.into();
				}
			}

			ValidTransaction::with_tag_prefix("BabeEquivocation")
				// We assign the maximum priority for any equivocation report.
				.priority(TransactionPriority::max_value())
				// Only one equivocation report for the same offender at the same slot.
				.and_provides((
					equivocation_proof.offender.clone(),
					equivocation_proof.slot_number,
				))
				// We don't propagate this. This can never be included on a remote node.
				.propagate(false)
				.build()
		} else {
			InvalidTransaction::Call.into()
		}
	}

	fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
		if let Call::report_equivocation_unsigned(equivocation_proof, key_owner_proof) = call {
			// check the membership proof to extract the offender's id
			let key = (
				sp_consensus_babe::KEY_TYPE,
				equivocation_proof.offender.clone(),
			);

			let offender = T::KeyOwnerProofSystem::check_proof(key, key_owner_proof.clone())
				.ok_or(InvalidTransaction::BadProof)?;

			// check if the offence has already been reported,
			// and if so then we can discard the report.
			let is_known_offence = T::HandleEquivocation::is_known_offence(
				&[offender],
				&equivocation_proof.slot_number,
			);

			if is_known_offence {
				Err(InvalidTransaction::Stale.into())
			} else {
				Ok(())
			}
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}

/// A BABE equivocation offence report.
///
/// When a validator released two or more blocks at the same slot.
pub struct BabeEquivocationOffence<FullIdentification> {
	/// A babe slot number in which this incident happened.
	pub slot: SlotNumber,
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
	type TimeSlot = SlotNumber;

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

	fn slash_fraction(offenders_count: u32, validator_set_count: u32) -> Perbill {
		// the formula is min((3k / n)^2, 1)
		let x = Perbill::from_rational_approximation(3 * offenders_count, validator_set_count);
		// _ ^ 2
		x.square()
	}
}
