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

mod mock;
mod tests;

use rstd::vec::Vec;
use support::{
	StorageDoubleMap, decl_module, decl_event, decl_storage, Parameter,
};
use sr_primitives::Perbill;
use sr_staking_primitives::{
	SessionIndex,
	offence::{Offence, ReportOffence, TimeSlot, Kind, OnOffenceHandler, OffenceDetails},
};

/// Offences trait
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;
	/// Full identification of the validator.
	type IdentificationTuple: Parameter;
	/// A handler called for every offence report.
	type OnOffenceHandler: OnOffenceHandler<Self::AccountId, Self::IdentificationTuple>;
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
			=> Vec<OffenceDetails<T::AccountId, T::IdentificationTuple>>;
	}
}

decl_event!(
	pub enum Event {
		/// There is an offence reported of the given `kind` happened at the `session_index` and
		/// (kind-specific) time slot. This event is not deposited for duplicate slashes.
		Offence(Kind, SessionIndex, TimeSlot),
	}
);

decl_module! {
	/// Offences module, currently just responsible for taking offence reports.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;
	}
}

impl<T: Trait, O: Offence<T::IdentificationTuple>> ReportOffence<T::AccountId, T::IdentificationTuple, O>
	for Module<T> where
	T::IdentificationTuple: Clone,
{
	fn report_offence(reporter: Option<T::AccountId>, offence: O) {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();
		let session = offence.session_index();
		let validator_set_count = offence.validator_set_count();

		// Check if an offence is already reported for the offender authorities
		// and otherwise stores that report.
		let mut changed = false;
		let all_offenders = {
			// We have to return the modified list of offending authorities. If we were to use
			// `mutate` we would have to clone the whole list in order to return it.
			let mut offending_authorities = <OffenceReports<T>>::get(&O::ID, &(session, time_slot));

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
				// Increase the count in each offence report. For just added offences the count is
				// going to be increased from 0 to 1.
				for details in offending_authorities.iter_mut() {
					details.count += 1;
				}

				// We pushed new items in the offending_authorities, so update it.
				<OffenceReports<T>>::insert(&O::ID, &(session, time_slot), &offending_authorities);
			}

			offending_authorities
		};

		if !changed {
			// The report contained only duplicates, so there is no need to slash again.
			return
		}

		// The report is not a duplicate. Deposit an event.
		Self::deposit_event(Event::Offence(O::ID, session, time_slot));

		let offenders_count = all_offenders.len() as u32;
		let expected_fraction = O::slash_fraction(offenders_count, validator_set_count);
		let slash_perbil = all_offenders
			.iter()
			.map(|details| {
				if details.count > 1 {
					let previous_fraction = O::slash_fraction(
						offenders_count.saturating_sub(details.count - 1),
						validator_set_count,
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
