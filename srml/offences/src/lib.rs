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

//! # Offences Module
//!
//! Tracks reported offences

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use rstd::vec::Vec;
use session::{SessionIndex, historical::{self, IdentificationTuple}};
use support::{
	StorageDoubleMap, decl_module, decl_storage,
};
use sr_primitives::{
	Perbill,
	offence::{Offence, ReportOffence, TimeSlot, Kind, OnOffenceHandler, OffenceDetails},
};

/// Offences trait
pub trait Trait: system::Trait + historical::Trait {
	/// A handler called for every offence report.
	type OnOffenceHandler: OnOffenceHandler<Self::AccountId, IdentificationTuple<Self>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Offences {
		/// A mapping between unique `TimeSlots` within a particular session and the offence `Kind` into
		/// a vector of offending authorities.
		///
		/// It's important that we store all authorities reported for an offence for any kind and
		/// timeslot since the slashing will increase based on the length of this vec.
		OffenceReports get(offence_reports):
			double_map Kind, blake2_256((SessionIndex, TimeSlot))
			=> Vec<OffenceDetails<T::AccountId, IdentificationTuple<T>>>;
	}
}

decl_module! {
	/// Offences module, currently just responsible for taking offence reports.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait, O: Offence<IdentificationTuple<T>>> ReportOffence<T::AccountId, IdentificationTuple<T>, O>
	for Module<T> where
	IdentificationTuple<T>: Clone,
{
	fn report_offence(reporter: Option<T::AccountId>, offence: O) {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();
		let session = offence.current_era_start_session_index();
		let validators_count = offence.validators_count();

		// Check if an offence is already reported for the offender authorities
		// and otherwise stores that report.
		let mut changed = false;
		let all_offenders = <OffenceReports<T>>
			::mutate(&O::ID, &(session, time_slot), |offending_authorities| {
				for offender in offenders {
					// TODO [slashing] This prevents slashing for multiple reports of the same kind at the same slot,
					// note however that we might do that in the future if the reports are not exactly the same (dups).
					// De-duplication of reports is tricky though, we need a canonical form of the report
					// (for instance babe equivocation can have headers swapped).
					if !offending_authorities.iter().any(|details| details.offender == offender) {
						changed = true;
						offending_authorities.push(OffenceDetails {
							offender,
							count: 0,
							reporters: reporter.clone().into_iter().collect(),
						});
					}
				}

				if changed {
					for details in offending_authorities.iter_mut() {
						details.count += 1;
					}
				}

				offending_authorities.clone()
			});

		if !changed {
			// The report contained only duplicates, so there is no need to slash again.
			return
		}

		let offenders_count = all_offenders.len() as u32;
		let expected_fraction = O::slash_fraction(offenders_count, validators_count);
		let slash_perbil = all_offenders
			.iter()
			.map(|details| {
				if details.count > 1 {
					let previous_fraction = O::slash_fraction(
						offenders_count.saturating_sub(details.count - 1),
						validators_count,
					);
					let perbil = expected_fraction
						.into_parts()
						.saturating_sub(previous_fraction.into_parts());
					Perbill::from_parts(perbil)
				} else {
					expected_fraction.clone()
				}
			})
			.collect::<Vec<_>>();

		T::OnOffenceHandler::on_offence(
			&all_offenders,
			&slash_perbil
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_trigger_on_offence_handler() {
		// TODO [slashing] implement me
		assert_eq!(true, false);
	}
}

