// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! # Offences Module
//!
//! Tracks reported offences

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use srml_support::{
	StorageDoubleMap, Parameter, decl_module, decl_storage,
	traits::{SlashingOffence, ReportOffence},
};
use parity_codec::{Decode, Encode};
use rstd::vec::Vec;
use sr_primitives::traits::{Member, TypedKey};

/// Offences trait
pub trait Trait: system::Trait {
	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + Default + TypedKey + Decode + Encode + AsRef<[u8]>;
}

// The kind of offence, is a binary representing some kind identifier
// e.g. `b"im-online:off"`, `b"babe:equivocatio"`
// TODO [slashing]: Is there something better we can have here that is more natural but still
// flexible? as you see in examples, they get cut off with long names.
type Kind = [u8; 16];
// The TimeSlot is the integer identifying for which timeslot this offence matters. For grandpa this
// is a Round ID, for babe it's a block number, for offline it's a SessionIndex.
type TimeSlot = u128;

decl_storage! {
	trait Store for Module<T: Trait> as Offences {
		/// Offence reports is a double_map of the kind, timeslot to a vec of authorities.
		/// It's important that we store all authorities reported for an offence for any kind and
		/// timeslot since the slashing will increase based on the length of this vec.
		OffenceReports get(offence_reports): double_map Kind, blake2_256(TimeSlot) => Vec<T::AuthorityId>;
	}
}

decl_module! {
	/// Offences module, currently just responsible for taking offence reports.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait, O: SlashingOffence<T::AuthorityId>> ReportOffence<T::AuthorityId, T::AuthorityId, O>
	for Module<T>
{
	// Implementation of report_offence, where it checks if an offence is already reported for an
	// authority and otherwise stores that report.
	fn report_offence(_reporters: &[T::AuthorityId], offence: &O) {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();

		<OffenceReports<T>>::mutate(&O::ID, &time_slot, |offending_authorities| {
			for offender in offenders {
				if !offending_authorities.contains(&offender) {
					offending_authorities.push(offender);
				}
			}
		});
	}
}
