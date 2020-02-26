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

use sp_std::{fmt::Debug, prelude::*};

use codec::{self as codec, Decode, Encode};
use frame_support::traits::KeyOwnerProofSystem;
use frame_system::offchain::SubmitSignedTransaction;
use sp_application_crypto::{key_types::GRANDPA, RuntimeAppPublic};
use sp_finality_grandpa::{EquivocationProof, RoundNumber, SetId};
use sp_runtime::{traits::IdentifyAccount, DispatchResult, KeyTypeId, PerThing, Perbill};
use sp_staking::{
	offence::{Kind, Offence, ReportOffence},
	SessionIndex,
};

pub trait HandleEquivocation<T: super::Trait> {
	type KeyOwnerProof: Clone + Debug + Decode + Encode + PartialEq;
	type KeyOwnerIdentification;
	type Offence: GrandpaOffence<Self::KeyOwnerIdentification>;

	fn check_proof(
		equivocation_proof: &EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: Self::KeyOwnerProof,
	) -> Option<(Self::KeyOwnerIdentification, SessionIndex, u32)>;

	fn report_offence(reporters: Vec<T::AccountId>, offence: Self::Offence);

	fn submit_equivocation_report(
		equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult;
}

impl<T: super::Trait> HandleEquivocation<T> for () {
	type KeyOwnerProof = ();
	type KeyOwnerIdentification = ();
	type Offence = GrandpaEquivocationOffence<Self::KeyOwnerIdentification>;

	fn check_proof(
		_equivocation_proof: &EquivocationProof<T::Hash, T::BlockNumber>,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> Option<(Self::KeyOwnerIdentification, SessionIndex, u32)> {
		None
	}

	fn report_offence(
		_reporters: Vec<T::AccountId>,
		_offence: GrandpaEquivocationOffence<Self::KeyOwnerIdentification>,
	) {
	}

	fn submit_equivocation_report(
		_equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		_key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		Ok(())
	}
}

pub struct EquivocationHandler<
	P,
	S,
	R,
	K,
	O = GrandpaEquivocationOffence<
		<P as KeyOwnerProofSystem<(KeyTypeId, Vec<u8>)>>::IdentificationTuple,
	>,
> {
	_phantom: sp_std::marker::PhantomData<(P, S, O, R, K)>,
}

impl<P, S, R, K, O> Default for EquivocationHandler<P, S, R, K, O> {
	fn default() -> Self {
		Self {
			_phantom: Default::default(),
		}
	}
}

impl<T, P, S, R, K, O> HandleEquivocation<T> for EquivocationHandler<P, S, R, K, O>
where
	T: super::Trait<HandleEquivocation = Self>,
	// A system for proving ownership of keys, i.e. that a given key was part
	// of a validator set, needed for validating equivocation reports. The
	// session index and validator count of the session are part of the proof
	// as extra data.
	P: KeyOwnerProofSystem<(KeyTypeId, Vec<u8>), ExtraData = (SessionIndex, u32)>,
	// A transaction submitter. Used for submitting equivocation reports.
	S: SubmitSignedTransaction<T, <T as super::Trait>::Call>,
	O: GrandpaOffence<P::IdentificationTuple>,
	R: ReportOffence<T::AccountId, P::IdentificationTuple, O>,
	// Key type to use when signing equivocation report transactions, must be
	// convertible to and from an account id since that's what we need to use
	// to sign transactions.
	K: RuntimeAppPublic + IdentifyAccount<AccountId = T::AccountId>,
{
	type KeyOwnerProof = P::Proof;
	type KeyOwnerIdentification = P::IdentificationTuple;
	type Offence = O;

	fn check_proof(
		equivocation_proof: &EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: Self::KeyOwnerProof,
	) -> Option<(Self::KeyOwnerIdentification, SessionIndex, u32)> {
		let (offender, (session_index, validator_set_count)) = P::check_proof(
			(GRANDPA, equivocation_proof.offender().encode()),
			key_owner_proof,
		)?;

		Some((offender, session_index, validator_set_count))
	}

	fn report_offence(reporters: Vec<T::AccountId>, offence: O) {
		R::report_offence(reporters, offence);
	}

	fn submit_equivocation_report(
		equivocation_proof: EquivocationProof<T::Hash, T::BlockNumber>,
		key_owner_proof: Self::KeyOwnerProof,
	) -> DispatchResult {
		let call =
			super::Call::report_equivocation(equivocation_proof.clone(), key_owner_proof.encode());

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

pub trait GrandpaOffence<FullIdentification>: Offence<FullIdentification> {
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
