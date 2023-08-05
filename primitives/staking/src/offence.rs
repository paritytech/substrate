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

//! Common traits and types that are useful for describing offences for usage in environments
//! that use staking.

use codec::{Decode, Encode};
use sp_core::Get;
use sp_runtime::{transaction_validity::TransactionValidityError, DispatchError, Perbill};
use sp_std::vec::Vec;

use crate::SessionIndex;

/// The kind of an offence, is a byte string representing some kind identifier
/// e.g. `b"im-online:offlin"`, `b"babe:equivocatio"`
pub type Kind = [u8; 16];

/// Number of times the offence of this authority was already reported in the past.
///
/// Note that we don't buffer offence reporting, so every time we see a new offence
/// of the same kind, we will report past authorities again.
/// This counter keeps track of how many times the authority was already reported in the past,
/// so that we can slash it accordingly.
pub type OffenceCount = u32;

/// In case of an offence, which conditions get an offending validator disabled.
#[derive(
	Clone,
	Copy,
	PartialEq,
	Eq,
	Hash,
	PartialOrd,
	Ord,
	Encode,
	Decode,
	sp_runtime::RuntimeDebug,
	scale_info::TypeInfo,
)]
pub enum DisableStrategy {
	/// Independently of slashing, this offence will not disable the offender.
	Never,
	/// Only disable the offender if it is also slashed.
	WhenSlashed,
	/// Independently of slashing, this offence will always disable the offender.
	Always,
}

/// A trait implemented by an offence report.
///
/// This trait assumes that the offence is legitimate and was validated already.
///
/// Examples of offences include: a BABE equivocation or a GRANDPA unjustified vote.
pub trait Offence<Offender> {
	/// Identifier which is unique for this kind of an offence.
	const ID: Kind;

	/// A type that represents a point in time on an abstract timescale.
	///
	/// See `Offence::time_slot` for details. The only requirement is that such timescale could be
	/// represented by a single `u128` value.
	type TimeSlot: Clone + codec::Codec + Ord;

	/// The list of all offenders involved in this incident.
	///
	/// The list has no duplicates, so it is rather a set.
	fn offenders(&self) -> Vec<Offender>;

	/// The session index that is used for querying the validator set for the `slash_fraction`
	/// function.
	///
	/// This is used for filtering historical sessions.
	fn session_index(&self) -> SessionIndex;

	/// Return a validator set count at the time when the offence took place.
	fn validator_set_count(&self) -> u32;

	/// A point in time when this offence happened.
	///
	/// This is used for looking up offences that happened at the "same time".
	///
	/// The timescale is abstract and doesn't have to be the same across different implementations
	/// of this trait. The value doesn't represent absolute timescale though since it is interpreted
	/// along with the `session_index`. Two offences are considered to happen at the same time iff
	/// both `session_index` and `time_slot` are equal.
	///
	/// As an example, for GRANDPA timescale could be a round number and for BABE it could be a slot
	/// number. Note that for GRANDPA the round number is reset each epoch.
	fn time_slot(&self) -> Self::TimeSlot;

	/// In which cases this offence needs to disable offenders until the next era starts.
	fn disable_strategy(&self) -> DisableStrategy {
		DisableStrategy::WhenSlashed
	}

	/// A slash fraction of the total exposure that should be slashed for this
	/// particular offence for the `offenders_count` that happened at a singular `TimeSlot`.
	///
	/// `offenders_count` - the count of unique offending authorities for this `TimeSlot`. It is >0.
	fn slash_fraction(&self, offenders_count: u32) -> Perbill;
}

/// Errors that may happen on offence reports.
#[derive(PartialEq, sp_runtime::RuntimeDebug)]
pub enum OffenceError {
	/// The report has already been sumbmitted.
	DuplicateReport,

	/// Other error has happened.
	Other(u8),
}

impl sp_runtime::traits::Printable for OffenceError {
	fn print(&self) {
		"OffenceError".print();
		match self {
			Self::DuplicateReport => "DuplicateReport".print(),
			Self::Other(e) => {
				"Other".print();
				e.print();
			},
		}
	}
}

/// A trait for decoupling offence reporters from the actual handling of offence reports.
pub trait ReportOffence<Reporter, Offender, O: Offence<Offender>> {
	/// Report an `offence` and reward given `reporters`.
	fn report_offence(reporters: Vec<Reporter>, offence: O) -> Result<(), OffenceError>;

	/// Returns true iff all of the given offenders have been previously reported
	/// at the given time slot. This function is useful to prevent the sending of
	/// duplicate offence reports.
	fn is_known_offence(offenders: &[Offender], time_slot: &O::TimeSlot) -> bool;
}

impl<Reporter, Offender, O: Offence<Offender>> ReportOffence<Reporter, Offender, O> for () {
	fn report_offence(_reporters: Vec<Reporter>, _offence: O) -> Result<(), OffenceError> {
		Ok(())
	}

	fn is_known_offence(_offenders: &[Offender], _time_slot: &O::TimeSlot) -> bool {
		true
	}
}

/// A trait to take action on an offence.
///
/// Used to decouple the module that handles offences and
/// the one that should punish for those offences.
pub trait OnOffenceHandler<Reporter, Offender, Res> {
	/// A handler for an offence of a particular kind.
	///
	/// Note that this contains a list of all previous offenders
	/// as well. The implementer should cater for a case, where
	/// the same authorities were reported for the same offence
	/// in the past (see `OffenceCount`).
	///
	/// The vector of `slash_fraction` contains `Perbill`s
	/// the authorities should be slashed and is computed
	/// according to the `OffenceCount` already. This is of the same length as `offenders.`
	/// Zero is a valid value for a fraction.
	///
	/// The `session` parameter is the session index of the offence.
	///
	/// The `disable_strategy` parameter decides if the offenders need to be disabled immediately.
	///
	/// The receiver might decide to not accept this offence. In this case, the call site is
	/// responsible for queuing the report and re-submitting again.
	fn on_offence(
		offenders: &[OffenceDetails<Reporter, Offender>],
		slash_fraction: &[Perbill],
		session: SessionIndex,
		disable_strategy: DisableStrategy,
	) -> Res;
}

impl<Reporter, Offender, Res: Default> OnOffenceHandler<Reporter, Offender, Res> for () {
	fn on_offence(
		_offenders: &[OffenceDetails<Reporter, Offender>],
		_slash_fraction: &[Perbill],
		_session: SessionIndex,
		_disable_strategy: DisableStrategy,
	) -> Res {
		Default::default()
	}
}

/// A details about an offending authority for a particular kind of offence.
#[derive(Clone, PartialEq, Eq, Encode, Decode, sp_runtime::RuntimeDebug, scale_info::TypeInfo)]
pub struct OffenceDetails<Reporter, Offender> {
	/// The offending authority id
	pub offender: Offender,
	/// A list of reporters of offences of this authority ID. Possibly empty where there are no
	/// particular reporters.
	pub reporters: Vec<Reporter>,
}

/// An abstract system to publish, check and process offence evidences.
///
/// Implementation details are left opaque and we don't assume any specific usage
/// scenario for this trait at this level. The main goal is to group together some
/// common actions required during a typical offence report flow.
///
/// Even though this trait doesn't assume too much, this is a general guideline
/// for a typical usage scenario:
///
/// 1. An offence is detected and an evidence is submitted on-chain via the
///    [`OffenceReportSystem::publish_evidence`] method. This will construct and submit an extrinsic
///    transaction containing the offence evidence.
///
/// 2. If the extrinsic is unsigned then the transaction receiver may want to perform some
///    preliminary checks before further processing. This is a good place to call the
///    [`OffenceReportSystem::check_evidence`] method.
///
/// 3. Finally the report extrinsic is executed on-chain. This is where the user calls the
///    [`OffenceReportSystem::process_evidence`] to consume the offence report and enact any
///    required action.
pub trait OffenceReportSystem<Reporter, Evidence> {
	/// Longevity, in blocks, for the evidence report validity.
	///
	/// For example, when using the staking pallet this should be set equal
	/// to the bonding duration in blocks, not eras.
	type Longevity: Get<u64>;

	/// Publish an offence evidence.
	///
	/// Common usage: submit the evidence on-chain via some kind of extrinsic.
	fn publish_evidence(evidence: Evidence) -> Result<(), ()>;

	/// Check an offence evidence.
	///
	/// Common usage: preliminary validity check before execution
	/// (e.g. for unsigned extrinsic quick checks).
	fn check_evidence(evidence: Evidence) -> Result<(), TransactionValidityError>;

	/// Process an offence evidence.
	///
	/// Common usage: enact some form of slashing directly or by forwarding
	/// the evidence to a lower level specialized subsystem (e.g. a handler
	/// implementing `ReportOffence` trait).
	fn process_evidence(reporter: Reporter, evidence: Evidence) -> Result<(), DispatchError>;
}

/// Dummy offence report system.
///
/// Doesn't do anything special and returns `Ok(())` for all the actions.
impl<Reporter, Evidence> OffenceReportSystem<Reporter, Evidence> for () {
	type Longevity = ();

	fn publish_evidence(_evidence: Evidence) -> Result<(), ()> {
		Ok(())
	}

	fn check_evidence(_evidence: Evidence) -> Result<(), TransactionValidityError> {
		Ok(())
	}

	fn process_evidence(_reporter: Reporter, _evidence: Evidence) -> Result<(), DispatchError> {
		Ok(())
	}
}
