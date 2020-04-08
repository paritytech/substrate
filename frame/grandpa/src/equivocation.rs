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

use sp_std::prelude::*;

use codec::{self as codec, Decode, Encode};
use frame_system::offchain::SubmitSignedTransaction;
use sp_application_crypto::RuntimeAppPublic;
use sp_finality_grandpa::{EquivocationProof, RoundNumber, SetId};
use sp_runtime::{traits::IdentifyAccount, DispatchResult, Perbill};
use sp_staking::{
	offence::{Kind, Offence, OffenceError, ReportOffence},
	SessionIndex,
};

/// A trait with utility methods for handling equivocation reports in GRANDPA.
/// The key owner proof and offence types are generic, and the trait provides
/// methods to check an equivocation proof (i.e. the equivocation itself and the
/// key ownership proof), reporting an offence triggered by a valid equivocation
/// report, and also for creating and submitting equivocation report extrinsics
/// (useful only in offchain context).
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
		self.session()
	}
}

impl GetValidatorCount for sp_session::MembershipProof {
	fn validator_count(&self) -> sp_session::ValidatorCount {
		self.validator_count()
	}
}

/// Generic equivocation handler. This type implements `HandleEquivocation`
/// using existing subsystems that are part of frame (type bounds described
/// below) and will dispatch to them directly, it's only purpose is to wire all
/// subsystems together.
pub struct EquivocationHandler<I, S, R, K, O = GrandpaEquivocationOffence<I>> {
	_phantom: sp_std::marker::PhantomData<(I, S, O, R, K)>,
}

impl<I, S, R, K, O> Default for EquivocationHandler<I, S, R, K, O> {
	fn default() -> Self {
		Self {
			_phantom: Default::default(),
		}
	}
}

impl<T, S, R, K, O> HandleEquivocation<T>
	for EquivocationHandler<T::KeyOwnerIdentification, S, R, K, O>
where
	T: super::Trait,
	// A transaction submitter. Used for submitting equivocation reports.
	S: SubmitSignedTransaction<T, <T as super::Trait>::Call>,
	// The offence type that should be used when reporting.
	O: GrandpaOffence<T::KeyOwnerIdentification>,
	// A system for reporting offences after valid equivocation reports are
	// processed.
	R: ReportOffence<T::AccountId, T::KeyOwnerIdentification, O>,
	// Key type to use when signing equivocation report transactions, must be
	// convertible to and from an account id since that's what we need to use
	// to sign transactions.
	K: RuntimeAppPublic + IdentifyAccount<AccountId = T::AccountId>,
{
	type Offence = O;

	fn report_offence(reporters: Vec<T::AccountId>, offence: O) -> Result<(), OffenceError> {
		R::report_offence(reporters, offence)
	}

	fn submit_equivocation_report(
		equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResult {
		let call = super::Call::report_equivocation(equivocation_proof, key_owner_proof);

		let res = S::submit_signed_from(call, K::all().into_iter().map(|k| k.into_account()));

		if res.iter().any(|(_, r)| r.is_ok()) {
			Ok(())
		} else {
			Err("Error submitting equivocation report.".into())
		}
	}
}

/// A round number and set id which point on the time of an offence.
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Encode, Decode)]
pub struct GrandpaTimeSlot {
	// The order of these matters for `derive(Ord)`.
	pub set_id: SetId,
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
