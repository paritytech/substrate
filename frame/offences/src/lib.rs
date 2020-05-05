// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use sp_std::vec::Vec;
use frame_support::{
	decl_module, decl_event, decl_storage, Parameter, debug,
	weights::Weight,
};
use sp_runtime::{traits::Hash, Perbill};
use sp_staking::{
	SessionIndex,
	offence::{Offence, ReportOffence, Kind, OnOffenceHandler, OffenceDetails, OffenceError},
};
use codec::{Encode, Decode};
use frame_system as system;

/// A binary blob which represents a SCALE codec-encoded `O::TimeSlot`.
type OpaqueTimeSlot = Vec<u8>;

/// A type alias for a report identifier.
type ReportIdOf<T> = <T as frame_system::Trait>::Hash;

/// Type of data stored as a deferred offence
pub type DeferredOffenceOf<T> = (
	Vec<OffenceDetails<<T as frame_system::Trait>::AccountId, <T as Trait>::IdentificationTuple>>,
	Vec<Perbill>,
	SessionIndex,
);

/// Offences trait
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as frame_system::Trait>::Event>;
	/// Full identification of the validator.
	type IdentificationTuple: Parameter + Ord;
	/// A handler called for every offence report.
	type OnOffenceHandler: OnOffenceHandler<Self::AccountId, Self::IdentificationTuple>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Offences {
		/// The primary structure that holds all offence records keyed by report identifiers.
		Reports get(fn reports):
			map hasher(twox_64_concat) ReportIdOf<T>
			=> Option<OffenceDetails<T::AccountId, T::IdentificationTuple>>;

		/// Deferred reports that have been rejected by the offence handler and need to be submitted
		/// at a later time.
		DeferredOffences get(fn deferred_offences): Vec<DeferredOffenceOf<T>>;

		/// A vector of reports of the same kind that happened at the same time slot.
		ConcurrentReportsIndex:
			double_map hasher(twox_64_concat) Kind, hasher(twox_64_concat) OpaqueTimeSlot
			=> Vec<ReportIdOf<T>>;

		/// Enumerates all reports of a kind along with the time they happened.
		///
		/// All reports are sorted by the time of offence.
		///
		/// Note that the actual type of this mapping is `Vec<u8>`, this is because values of
		/// different types are not supported at the moment so we are doing the manual serialization.
		ReportsByKindIndex: map hasher(twox_64_concat) Kind => Vec<u8>; // (O::TimeSlot, ReportIdOf<T>)
	}
}

decl_event!(
	pub enum Event {
		/// There is an offence reported of the given `kind` happened at the `session_index` and
		/// (kind-specific) time slot. This event is not deposited for duplicate slashes. last
		/// element indicates of the offence was applied (true) or queued (false).
		Offence(Kind, OpaqueTimeSlot, bool),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		fn on_initialize(now: T::BlockNumber) -> Weight {
			// only decode storage if we can actually submit anything again.
			if T::OnOffenceHandler::can_report() {
				<DeferredOffences<T>>::mutate(|deferred| {
					// keep those that fail to be reported again. An error log is emitted here; this
					// should not happen if staking's `can_report` is implemented properly.
					deferred.retain(|(o, p, s)| {
						T::OnOffenceHandler::on_offence(&o, &p, *s).map_err(|_| {
							debug::native::error!(
								target: "pallet-offences",
								"re-submitting a deferred slash returned Err at {}. This should not happen with pallet-staking",
								now,
							);
						}).is_err()
					})
				})
			}

			0
		}
	}
}

impl<T: Trait, O: Offence<T::IdentificationTuple>>
	ReportOffence<T::AccountId, T::IdentificationTuple, O> for Module<T>
where
	T::IdentificationTuple: Clone,
{
	fn report_offence(reporters: Vec<T::AccountId>, offence: O) -> Result<(), OffenceError> {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();
		let validator_set_count = offence.validator_set_count();

		// Go through all offenders in the offence report and find all offenders that was spotted
		// in unique reports.
		let TriageOutcome { concurrent_offenders } = match Self::triage_offence_report::<O>(
			reporters,
			&time_slot,
			offenders,
		) {
			Some(triage) => triage,
			// The report contained only duplicates, so there is no need to slash again.
			None => return Err(OffenceError::DuplicateReport),
		};

		let offenders_count = concurrent_offenders.len() as u32;

		// The amount new offenders are slashed
		let new_fraction = O::slash_fraction(offenders_count, validator_set_count);

		let slash_perbill: Vec<_> = (0..concurrent_offenders.len())
			.map(|_| new_fraction.clone()).collect();

		let applied = Self::report_or_store_offence(
			&concurrent_offenders,
			&slash_perbill,
			offence.session_index(),
		);

		// Deposit the event.
		Self::deposit_event(Event::Offence(O::ID, time_slot.encode(), applied));

		Ok(())
	}
}

impl<T: Trait> Module<T> {
	/// Tries (without checking) to report an offence. Stores them in [`DeferredOffences`] in case
	/// it fails. Returns false in case it has to store the offence.
	fn report_or_store_offence(
		concurrent_offenders: &[OffenceDetails<T::AccountId, T::IdentificationTuple>],
		slash_perbill: &[Perbill],
		session_index: SessionIndex,
	) -> bool {
		match T::OnOffenceHandler::on_offence(
			&concurrent_offenders,
			&slash_perbill,
			session_index,
		) {
			Ok(_) => true,
			Err(_) => {
				<DeferredOffences<T>>::mutate(|d|
					d.push((concurrent_offenders.to_vec(), slash_perbill.to_vec(), session_index))
				);
				false
			}
		}
	}

	/// Compute the ID for the given report properties.
	///
	/// The report id depends on the offence kind, time slot and the id of offender.
	fn report_id<O: Offence<T::IdentificationTuple>>(
		time_slot: &O::TimeSlot,
		offender: &T::IdentificationTuple,
	) -> ReportIdOf<T> {
		(O::ID, time_slot.encode(), offender).using_encoded(T::Hashing::hash)
	}

	/// Triages the offence report and returns the set of offenders that was involved in unique
	/// reports along with the list of the concurrent offences.
	fn triage_offence_report<O: Offence<T::IdentificationTuple>>(
		reporters: Vec<T::AccountId>,
		time_slot: &O::TimeSlot,
		offenders: Vec<T::IdentificationTuple>,
	) -> Option<TriageOutcome<T>> {
		let mut storage = ReportIndexStorage::<T, O>::load(time_slot);

		let mut any_new = false;
		for offender in offenders {
			let report_id = Self::report_id::<O>(time_slot, &offender);

			if !<Reports<T>>::contains_key(&report_id) {
				any_new = true;
				<Reports<T>>::insert(
					&report_id,
					OffenceDetails {
						offender,
						reporters: reporters.clone(),
					},
				);

				storage.insert(time_slot, report_id);
			}
		}

		if any_new {
			// Load report details for the all reports happened at the same time.
			let concurrent_offenders = storage.concurrent_reports
				.iter()
				.filter_map(|report_id| <Reports<T>>::get(report_id))
				.collect::<Vec<_>>();

			storage.save();

			Some(TriageOutcome {
				concurrent_offenders,
			})
		} else {
			None
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	pub fn set_deferred_offences(offences: Vec<DeferredOffenceOf<T>>) {
		<DeferredOffences<T>>::put(offences);
	}
}

struct TriageOutcome<T: Trait> {
	/// Other reports for the same report kinds.
	concurrent_offenders: Vec<OffenceDetails<T::AccountId, T::IdentificationTuple>>,
}

/// An auxiliary struct for working with storage of indexes localized for a specific offence
/// kind (specified by the `O` type parameter).
///
/// This struct is responsible for aggregating storage writes and the underlying storage should not
/// accessed directly meanwhile.
#[must_use = "The changes are not saved without called `save`"]
struct ReportIndexStorage<T: Trait, O: Offence<T::IdentificationTuple>> {
	opaque_time_slot: OpaqueTimeSlot,
	concurrent_reports: Vec<ReportIdOf<T>>,
	same_kind_reports: Vec<(O::TimeSlot, ReportIdOf<T>)>,
}

impl<T: Trait, O: Offence<T::IdentificationTuple>> ReportIndexStorage<T, O> {
	/// Preload indexes from the storage for the specific `time_slot` and the kind of the offence.
	fn load(time_slot: &O::TimeSlot) -> Self {
		let opaque_time_slot = time_slot.encode();

		let same_kind_reports = <ReportsByKindIndex>::get(&O::ID);
		let same_kind_reports =
			Vec::<(O::TimeSlot, ReportIdOf<T>)>::decode(&mut &same_kind_reports[..])
				.unwrap_or_default();

		let concurrent_reports = <ConcurrentReportsIndex<T>>::get(&O::ID, &opaque_time_slot);

		Self {
			opaque_time_slot,
			concurrent_reports,
			same_kind_reports,
		}
	}

	/// Insert a new report to the index.
	fn insert(&mut self, time_slot: &O::TimeSlot, report_id: ReportIdOf<T>) {
		// Insert the report id into the list while maintaining the ordering by the time
		// slot.
		let pos = match self
			.same_kind_reports
			.binary_search_by_key(&time_slot, |&(ref when, _)| when)
		{
			Ok(pos) => pos,
			Err(pos) => pos,
		};
		self.same_kind_reports
			.insert(pos, (time_slot.clone(), report_id));

		// Update the list of concurrent reports.
		self.concurrent_reports.push(report_id);
	}

	/// Dump the indexes to the storage.
	fn save(self) {
		<ReportsByKindIndex>::insert(&O::ID, self.same_kind_reports.encode());
		<ConcurrentReportsIndex<T>>::insert(
			&O::ID,
			&self.opaque_time_slot,
			&self.concurrent_reports,
		);
	}
}
