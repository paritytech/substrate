// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Common traits and types that are useful for describing offences for usage in environments
//! that use staking.

use rstd::vec::Vec;

use codec::{Encode, Decode};
use crate::Perbill;

/// The kind of an offence, is a byte string representing some kind identifier
/// e.g. `b"im-online:offlin"`, `b"babe:equivocatio"`
// TODO [slashing]: Is there something better we can have here that is more natural but still
// flexible? as you see in examples, they get cut off with long names.
pub type Kind = [u8; 16];

/// Number of times the offence of this authority was already reported in the past.
///
/// Note we don't buffer offence reporting so everytime we see a new offence
/// of the same kind, we will report past authorities again.
/// This counter keeps track of how many times the authority was already reported in the past,
/// so that we can slash it accordingly.
pub type OffenceCount = u32;

/// A type that represents a point in time on an abstract timescale.
///
/// This type is not tied to a particular timescale and can be used for representing instants on
/// different timescales. Examples of such timescales would be the following: for GRANDPA is a round
/// ID, for BABE it's a slot number and for offline it's a session index. The only requirement is
/// that such timescale could be represented by a single `u128` value.
pub type TimeSlot = u128;

/// A trait implemented by an offence report.
///
/// This trait assumes that the offence is legitimate and was validated already.
///
/// Examples of offences include: a BABE equivocation or a GRANDPA unjustified vote.
pub trait Offence<Offender> {
	/// Identifier which is unique for this kind of an offence.
	const ID: Kind;

	/// The list of all offenders involved in this incident.
	///
	/// The list has no duplicates, so it is rather a set.
	fn offenders(&self) -> Vec<Offender>;

	/// The session index which is used for querying the validator set for the `slash_fraction`
	/// function.
	fn current_era_start_session_index(&self) -> u32; // TODO [slashing]: Should be a SessionIndex.

	/// Return a validators count at the time when the offence took place.
	fn validators_count(&self) -> u32;

	/// A point in time when this offence happened.
	///
	/// The timescale is abstract and it doesn't have to be the same across different
	/// implementations of this trait. For example, for GRANDPA it could represent a round number
	/// and for BABE it could be a slot number.
	fn time_slot(&self) -> TimeSlot;

	/// A slash fraction of the total exposure that should be slashed for this
	/// particular offence kind for the given parameters.
	///
	/// `offenders_count` - the count of unique offending authorities. It is >0.
	/// `validators_count` - the cardinality of the validator set at the time of offence.
	fn slash_fraction(
		offenders_count: u32,
		validators_count: u32,
	) -> Perbill;
}

/// A trait for decoupling offence reporters from the actual handling of offence reports.
pub trait ReportOffence<Reporter, Offender, O: Offence<Offender>> {
	/// Report an `offence` and reward the `reporter`.
	fn report_offence(reporter: Option<Reporter>, offence: O);
}

/// A trait to take action on an offence.
///
/// Used to decouple the module that handles offences and
/// the one that should punish for those offences.
pub trait OnOffenceHandler<Reporter, Offender> {
	/// A handler for offence of particular kind.
	///
	/// Note that this contains a list of all previous offenders
	/// as well. The implementer should cater for a case, where
	/// the same authorities were reported for the same offence
	/// in the past (see `OffenceCount`).
	///
	/// The vector of `slash_fraction` contains perbils
	/// the authorities should be slashed and is computed
	/// according to the `OffenceCount` already.
	fn on_offence(
		offenders: &[OffenceDetails<Reporter, Offender>],
		slash_fraction: &[Perbill],
	);
}

/// A details about an offending authority for a particular kind of offence.
#[derive(Clone, PartialEq, Eq, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct OffenceDetails<Reporter, Offender> {
	/// The offending authority id
	pub offender: Offender,
	/// A number of times the authority was already reported for this offence.
	///
	/// Since we punish all authorities for that made the same offence in the past as well
	/// we keep track the "age" of the report, so that the slashes can be lowered
	/// in case the authority was already slashed in the past.
	/// Note that we don't buffer slashes and instead use this approach.
	pub count: OffenceCount,
	/// A list of reporters of offences of this authority id.
	pub reporters: Vec<Reporter>,
}
