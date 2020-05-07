// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//!
//! An opt-in utility module for reporting equivocations.
//!
//! This module defines an offence type for GRANDPA equivocations
//! and some utility traits to wire together:
//! - a key ownership proof system (e.g. to prove that a given authority was
//! part of a session);
//! - a system for reporting offences;
//! - a system for signing and submitting transactions;
//!
//! These can be used in an offchain context in order to submit equivocation
//! reporting extrinsics (from the client that's running the GRANDPA protocol).
//! And in a runtime context, so that the GRANDPA module can validate the
//! equivocation proofs in the extrinsic and report the offences.
//!
//! IMPORTANT:
//! When using this module for enabling equivocation reporting it is required
//! that the `ValidateEquivocationReport` signed extension is used in the runtime
//! definition. Failure to do so will allow invalid equivocation reports to be
//! accepted by the runtime.
//!

use sp_std::prelude::*;

use codec::{self as codec, Decode, Encode};
use frame_support::{debug, dispatch::IsSubType, traits::KeyOwnerProofSystem};
use frame_system::offchain::{AppCrypto, CreateSignedTransaction, Signer};
use sp_finality_grandpa::{EquivocationProof, RoundNumber, SetId};
use sp_runtime::{
	traits::{DispatchInfoOf, SignedExtension},
	transaction_validity::{
		InvalidTransaction, TransactionValidity, TransactionValidityError, ValidTransaction,
	},
	DispatchResult, Perbill,
};
use sp_staking::{
	offence::{Kind, Offence, OffenceError, ReportOffence},
	SessionIndex,
};

/// Ensure that equivocation reports are only processed if valid.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct ValidateEquivocationReport<T>(sp_std::marker::PhantomData<T>);

impl<T> Default for ValidateEquivocationReport<T> {
	fn default() -> ValidateEquivocationReport<T> {
		ValidateEquivocationReport::new()
	}
}

impl<T> ValidateEquivocationReport<T> {
	pub fn new() -> ValidateEquivocationReport<T> {
		ValidateEquivocationReport(Default::default())
	}
}

impl<T> sp_std::fmt::Debug for ValidateEquivocationReport<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "ValidateEquivocationReport<T>")
	}
}

/// Custom validity error used when validating equivocation reports.
#[derive(Debug)]
#[repr(u8)]
pub enum ReportEquivocationValidityError {
	/// The proof provided in the report is not valid.
	InvalidEquivocationProof = 1,
	/// The proof provided in the report is not valid.
	InvalidKeyOwnershipProof = 2,
	/// The set id provided in the report is not valid.
	InvalidSetId = 3,
	/// The session index provided in the report is not valid.
	InvalidSession = 4,
}

impl From<ReportEquivocationValidityError> for TransactionValidityError {
	fn from(e: ReportEquivocationValidityError) -> TransactionValidityError {
		TransactionValidityError::from(InvalidTransaction::Custom(e as u8))
	}
}

impl<T: super::Trait + Send + Sync> SignedExtension for ValidateEquivocationReport<T>
where
	<T as frame_system::Trait>::Call: IsSubType<super::Module<T>, T>,
{
	const IDENTIFIER: &'static str = "ValidateEquivocationReport";
	type AccountId = T::AccountId;
	type Call = <T as frame_system::Trait>::Call;
	type AdditionalSigned = ();
	type Pre = ();

	fn additional_signed(
		&self,
	) -> sp_std::result::Result<Self::AdditionalSigned, TransactionValidityError> {
		Ok(())
	}

	fn validate(
		&self,
		_who: &Self::AccountId,
		call: &Self::Call,
		_info: &DispatchInfoOf<Self::Call>,
		_len: usize,
	) -> TransactionValidity {
		let (equivocation_proof, key_owner_proof) = match call.is_sub_type() {
			Some(super::Call::report_equivocation(equivocation_proof, key_owner_proof)) => {
				(equivocation_proof, key_owner_proof)
			}
			_ => return Ok(ValidTransaction::default()),
		};

		// validate the key ownership proof extracting the id of the offender.
		if let None = T::KeyOwnerProofSystem::check_proof(
			(
				sp_finality_grandpa::KEY_TYPE,
				equivocation_proof.offender().clone(),
			),
			key_owner_proof.clone(),
		) {
			return Err(ReportEquivocationValidityError::InvalidKeyOwnershipProof.into());
		}

		// we check the equivocation within the context of its set id (and
		// associated session).
		let set_id = equivocation_proof.set_id();
		let session_index = key_owner_proof.session();

		// validate equivocation proof (check votes are different and
		// signatures are valid).
		if let Err(_) = sp_finality_grandpa::check_equivocation_proof(equivocation_proof.clone()) {
			return Err(ReportEquivocationValidityError::InvalidEquivocationProof.into());
		}

		// fetch the current and previous sets last session index. on the
		// genesis set there's no previous set.
		let previous_set_id_session_index = if set_id == 0 {
			None
		} else {
			let session_index =
				if let Some(session_id) = <super::Module<T>>::session_for_set(set_id - 1) {
					session_id
				} else {
					return Err(ReportEquivocationValidityError::InvalidSetId.into());
				};

			Some(session_index)
		};

		let set_id_session_index =
			if let Some(session_id) = <super::Module<T>>::session_for_set(set_id) {
				session_id
			} else {
				return Err(ReportEquivocationValidityError::InvalidSetId.into());
			};

		// check that the session id for the membership proof is within the
		// bounds of the set id reported in the equivocation.
		if session_index > set_id_session_index ||
			previous_set_id_session_index
				.map(|previous_index| session_index <= previous_index)
				.unwrap_or(false)
		{
			return Err(ReportEquivocationValidityError::InvalidSession.into());
		}

		Ok(ValidTransaction::default())
	}
}

/// A trait with utility methods for handling equivocation reports in GRANDPA.
/// The offence type is generic, and the trait provides , reporting an offence
/// triggered by a valid equivocation report, and also for creating and
/// submitting equivocation report extrinsics (useful only in offchain context).
pub trait HandleEquivocation<T: super::Trait> {
	/// The offence type used for reporting offences on valid equivocation reports.
	type Offence: GrandpaOffence<T::KeyOwnerIdentification>;

	/// Report an offence proved by the given reporters.
	fn report_offence(
		reporters: Vec<T::AccountId>,
		offence: Self::Offence,
	) -> Result<(), OffenceError>;

	/// Create and dispatch an equivocation report extrinsic.
	fn submit_equivocation_report(
		equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult;
}

impl<T: super::Trait> HandleEquivocation<T> for () {
	type Offence = GrandpaEquivocationOffence<T::KeyOwnerIdentification>;

	fn report_offence(
		_reporters: Vec<T::AccountId>,
		_offence: GrandpaEquivocationOffence<T::KeyOwnerIdentification>,
	) -> Result<(), OffenceError> {
		Ok(())
	}

	fn submit_equivocation_report(
		_equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		_key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}
}

/// Generic equivocation handler. This type implements `HandleEquivocation`
/// using existing subsystems that are part of frame (type bounds described
/// below) and will dispatch to them directly, it's only purpose is to wire all
/// subsystems together.
pub struct EquivocationHandler<I, C, S, R, O = GrandpaEquivocationOffence<I>> {
	_phantom: sp_std::marker::PhantomData<(I, C, S, R, O)>,
}

impl<I, C, S, R, O> Default for EquivocationHandler<I, C, S, R, O> {
	fn default() -> Self {
		Self {
			_phantom: Default::default(),
		}
	}
}

impl<T, C, S, R, O> HandleEquivocation<T>
	for EquivocationHandler<T::KeyOwnerIdentification, C, S, R, O>
where
	// A signed transaction creator. Used for signing and submitting equivocation reports.
	T: super::Trait + CreateSignedTransaction<super::Call<T>>,
	// Application-specific crypto bindings.
	C: AppCrypto<T::Public, T::Signature>,
	// The offence type that should be used when reporting.
	O: GrandpaOffence<T::KeyOwnerIdentification>,
	// A system for reporting offences after valid equivocation reports are
	// processed.
	R: ReportOffence<T::AccountId, T::KeyOwnerIdentification, O>,
{
	type Offence = O;

	fn report_offence(reporters: Vec<T::AccountId>, offence: O) -> Result<(), OffenceError> {
		R::report_offence(reporters, offence)
	}

	fn submit_equivocation_report(
		equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		use frame_system::offchain::SendSignedTransaction;

		let signer = Signer::<T, C>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC.",
			)?;
		}

		let results = signer.send_signed_transaction(|_account| {
			super::Call::report_equivocation(equivocation_proof.clone(), key_owner_proof.clone())
		});

		for (acc, res) in &results {
			match res {
				Ok(()) => debug::info!("[{:?}] Submitted GRANDPA equivocation report.", acc.id),
				Err(e) => debug::error!(
					"[{:?}] Error submitting equivocation report: {:?}",
					acc.id,
					e
				),
			}
		}

		Ok(())
	}
}

/// A round number and set id which point on the time of an offence.
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Encode, Decode)]
pub struct GrandpaTimeSlot {
	// The order of these matters for `derive(Ord)`.
	/// Grandpa Set ID.
	pub set_id: SetId,
	/// Round number.
	pub round: RoundNumber,
}

/// A grandpa equivocation offence report.
#[allow(dead_code)]
pub struct GrandpaEquivocationOffence<FullIdentification> {
	/// Time slot at which this incident happened.
	pub time_slot: GrandpaTimeSlot,
	/// The session index in which the incident happened.
	pub session_index: SessionIndex,
	/// The size of the validator set at the time of the offence.
	pub validator_set_count: u32,
	/// The authority which produced this equivocation.
	pub offender: FullIdentification,
}

/// An interface for types that will be used as GRANDPA offences and must also
/// implement the `Offence` trait. This trait provides a constructor that is
/// provided all available data during processing of GRANDPA equivocations.
pub trait GrandpaOffence<FullIdentification>: Offence<FullIdentification> {
	/// Create a new GRANDPA offence using the given equivocation details.
	fn new(
		session_index: SessionIndex,
		validator_set_count: u32,
		offender: FullIdentification,
		set_id: SetId,
		round: RoundNumber,
	) -> Self;
}

impl<FullIdentification: Clone> GrandpaOffence<FullIdentification>
	for GrandpaEquivocationOffence<FullIdentification>
{
	fn new(
		session_index: SessionIndex,
		validator_set_count: u32,
		offender: FullIdentification,
		set_id: SetId,
		round: RoundNumber,
	) -> Self {
		GrandpaEquivocationOffence {
			session_index,
			validator_set_count,
			offender,
			time_slot: GrandpaTimeSlot { set_id, round },
		}
	}
}

impl<FullIdentification: Clone> Offence<FullIdentification>
	for GrandpaEquivocationOffence<FullIdentification>
{
	const ID: Kind = *b"grandpa:equivoca";
	type TimeSlot = GrandpaTimeSlot;

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
		self.time_slot
	}

	fn slash_fraction(offenders_count: u32, validator_set_count: u32) -> Perbill {
		// the formula is min((3k / n)^2, 1)
		let x = Perbill::from_rational_approximation(3 * offenders_count, validator_set_count);
		// _ ^ 2
		x.square()
	}
}

/// A trait to get a session number the `MembershipProof` belongs to.
pub trait GetSessionNumber {
	fn session(&self) -> SessionIndex;
}

/// A trait to get the validator count at the session the `MembershipProof`
/// belongs to.
pub trait GetValidatorCount {
	fn validator_count(&self) -> sp_session::ValidatorCount;
}

impl GetSessionNumber for frame_support::Void {
	fn session(&self) -> SessionIndex {
		Default::default()
	}
}

impl GetValidatorCount for frame_support::Void {
	fn validator_count(&self) -> sp_session::ValidatorCount {
		Default::default()
	}
}

impl GetSessionNumber for sp_session::MembershipProof {
	fn session(&self) -> SessionIndex {
		self.session
	}
}

impl GetValidatorCount for sp_session::MembershipProof {
	fn validator_count(&self) -> sp_session::ValidatorCount {
		self.validator_count
	}
}
