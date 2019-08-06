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

use crate::Perbill;

/// The kind of an offence, is a byte string representing some kind identifier
/// e.g. `b"im-online:off"`, `b"babe:equivocatio"`
// TODO [slashing]: Is there something better we can have here that is more natural but still
// flexible? as you see in examples, they get cut off with long names.
pub type Kind = [u8; 16];

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
	fn offenders(&self) -> rstd::vec::Vec<Offender>;

	/// The session index which is used for querying the validator set for the `slash_fraction`
	/// function.
	fn current_era_start_session_index(&self) -> u32; // TODO [slashing]: Should be a SessionIndex.

	/// A point in time when this offence happened.
	///
	/// The timescale is abstract and it doesn't have to be the same across different
	/// implementations of this trait. For example, for GRANDPA it could represent a round number
	/// and for BABE it could be a slot number.
	fn time_slot(&self) -> TimeSlot;

	/// A slash fraction of the total exposure that should be slashed for this
	/// particular offence kind for the given parameters.
	///
	/// `offenders` - the number of offences of this kind at the particular `time_slot`.
	/// `validators_count` - the cardinality of the validator set at the time of offence.
	fn slash_fraction(&self, offenders: u32, validators_count: u32) -> Perbill;
}

/// A trait for decoupling offence reporters from the actual handling of offence reports.
pub trait ReportOffence<Reporter, Offender, O: Offence<Offender>> {
	/// Report an `offence` from the given `reporters`.
	fn report_offence(reporters: &[Reporter], offence: &O);
}
