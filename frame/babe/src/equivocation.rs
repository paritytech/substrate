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

use frame_support::traits::KeyOwnerProofSystem;
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

use crate::{Call, Module, Trait};

impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;
	fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
		if let Call::report_equivocation_unsigned(equivocation_proof, _) = call {
			// discard equivocation report not coming from the local node
			match source {
				TransactionSource::Local | TransactionSource::InBlock => { /* allowed */ }
				_ => {
					frame_support::debug::warn!(
						target: "babe",
						"rejecting unsigned report equivocation transaction because it is not local/in-block."
					);

					return InvalidTransaction::Call.into();
				}
			}

			ValidTransaction::with_tag_prefix("BabeEquivocation")
				// We assign the maximum priority for any equivocation report.
				.priority(TransactionPriority::max_value())
				// FIXME: tag with slot and offender
				.and_provides(equivocation_proof.offender.clone())
				// We don't propagate this. This can never be included on a remote node.
				.propagate(false)
				.build()
		} else {
			InvalidTransaction::Call.into()
		}
	}

	fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
		if let Call::report_equivocation_unsigned(equivocation_proof, key_owner_proof) = call {
			// check the membership and extract the offender's id
			let offender = T::KeyOwnerProofSystem::check_proof(
				(
					sp_consensus_babe::KEY_TYPE,
					equivocation_proof.offender.clone(),
				),
				key_owner_proof.clone(),
			)
			.ok_or(InvalidTransaction::Call)?;

			if T::HandleEquivocation::is_known_offence(&[offender], &equivocation_proof.slot_number)
			{
				Err(InvalidTransaction::Stale.into())
			} else {
				Ok(())
			}
		} else {
			Err(InvalidTransaction::Call.into())
		}
	}
}

/// A trait with utility methods for handling equivocation reports in GRANDPA.
/// The offence type is generic, and the trait provides , reporting an offence
/// triggered by a valid equivocation report, and also for creating and
/// submitting equivocation report extrinsics (useful only in offchain context).
pub trait HandleEquivocation<T: Trait> {
	/// The offence type used for reporting offences on valid equivocation reports.
	// type Offence: GrandpaOffence<T::KeyOwnerIdentification>;

	/// Report an offence proved by the given reporters.
	fn report_offence(
		reporters: Vec<T::AccountId>,
		// offence: Self::Offence,
		offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError>;

	fn is_known_offence(_offenders: &[T::KeyOwnerIdentification], _time_slot: &SlotNumber) -> bool;

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult;

	fn block_author() -> Option<T::AccountId>;
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
	T: Trait + pallet_authorship::Trait + frame_system::offchain::SendTransactionTypes<Call<T>>,
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
		// offence: Self::Offence,
		offence: BabeEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError> {
		R::report_offence(reporters, offence)
	}

	fn is_known_offence(offenders: &[T::KeyOwnerIdentification], time_slot: &SlotNumber) -> bool {
		R::is_known_offence(offenders, time_slot)
	}

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<T::Header>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		use frame_system::offchain::SubmitTransaction;

		let call = Call::report_equivocation_unsigned(equivocation_proof, key_owner_proof);

		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into())
			.map_err(|_| "")?;

		Ok(())
	}

	fn block_author() -> Option<T::AccountId> {
		Some(<pallet_authorship::Module<T>>::author())
	}
}

/// A BABE equivocation offence report.
///
/// When a validator released two or more blocks at the same slot.
pub struct BabeEquivocationOffence<FullIdentification> {
	/// A babe slot number in which this incident happened.
	pub slot: u64,
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
