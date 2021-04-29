// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Offences Module
//!
//! Tracks reported offences

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod mock;
mod tests;
mod migration;

use sp_std::vec::Vec;
use frame_support::{
	decl_module, decl_event, decl_storage, Parameter, weights::Weight,
};
use sp_runtime::{traits::Hash, Perbill};
use sp_staking::{
	SessionIndex,
	offence::{Offence, ReportOffence, Kind, OnOffenceHandler, OffenceDetails, OffenceError},
};
use codec::{Encode, Decode};

/// A binary blob which represents a SCALE codec-encoded `O::TimeSlot`.
type OpaqueTimeSlot = Vec<u8>;

/// A type alias for a report identifier.
type ReportIdOf<T> = <T as frame_system::Config>::Hash;

pub trait WeightInfo {
	fn report_offence_im_online(r: u32, o: u32, n: u32, ) -> Weight;
	fn report_offence_grandpa(r: u32, n: u32, ) -> Weight;
	fn report_offence_babe(r: u32, n: u32, ) -> Weight;
	fn on_initialize(d: u32, ) -> Weight;
}

impl WeightInfo for () {
	fn report_offence_im_online(_r: u32, _o: u32, _n: u32, ) -> Weight { 1_000_000_000 }
	fn report_offence_grandpa(_r: u32, _n: u32, ) -> Weight { 1_000_000_000 }
	fn report_offence_babe(_r: u32, _n: u32, ) -> Weight { 1_000_000_000 }
	fn on_initialize(_d: u32, ) -> Weight { 1_000_000_000 }
}

/// Offences trait
pub trait Config: frame_system::Config {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as frame_system::Config>::Event>;
	/// Full identification of the validator.
	type IdentificationTuple: Parameter + Ord;
	/// A handler called for every offence report.
	type OnOffenceHandler: OnOffenceHandler<Self::AccountId, Self::IdentificationTuple, Weight>;
}

decl_storage! {
	trait Store for Module<T: Config> as Offences {
		/// The primary structure that holds all offence records keyed by report identifiers.
		Reports get(fn reports):
			map hasher(twox_64_concat) ReportIdOf<T>
			=> Option<OffenceDetails<T::AccountId, T::IdentificationTuple>>;

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
		/// (kind-specific) time slot. This event is not deposited for duplicate slashes.
		/// \[kind, timeslot\].
		Offence(Kind, OpaqueTimeSlot),
	}
);

decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		fn on_runtime_upgrade() -> Weight {
			migration::remove_deferred_storage::<T>()
		}
	}
}

impl<T: Config, O: Offence<T::IdentificationTuple>>
	ReportOffence<T::AccountId, T::IdentificationTuple, O> for Module<T>
where
	T::IdentificationTuple: Clone,
{
	fn report_offence(reporters: Vec<T::AccountId>, offence: O) -> Result<(), OffenceError> {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();
		let validator_set_count = offence.validator_set_count();

		// Go through all offenders in the offence report and find all offenders that were spotted
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

		T::OnOffenceHandler::on_offence(
			&concurrent_offenders,
			&slash_perbill,
			offence.session_index(),
		);

		// Deposit the event.
		Self::deposit_event(Event::Offence(O::ID, time_slot.encode()));

		Ok(())
	}

	fn is_known_offence(offenders: &[T::IdentificationTuple], time_slot: &O::TimeSlot) -> bool {
		let any_unknown = offenders.iter().any(|offender| {
			let report_id = Self::report_id::<O>(time_slot, offender);
			!<Reports<T>>::contains_key(&report_id)
		});

		!any_unknown
	}
}

impl<T: Config> Module<T> {
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
}

struct TriageOutcome<T: Config> {
	/// Other reports for the same report kinds.
	concurrent_offenders: Vec<OffenceDetails<T::AccountId, T::IdentificationTuple>>,
}

/// An auxiliary struct for working with storage of indexes localized for a specific offence
/// kind (specified by the `O` type parameter).
///
/// This struct is responsible for aggregating storage writes and the underlying storage should not
/// accessed directly meanwhile.
#[must_use = "The changes are not saved without called `save`"]
struct ReportIndexStorage<T: Config, O: Offence<T::IdentificationTuple>> {
	opaque_time_slot: OpaqueTimeSlot,
	concurrent_reports: Vec<ReportIdOf<T>>,
	same_kind_reports: Vec<(O::TimeSlot, ReportIdOf<T>)>,
}

impl<T: Config, O: Offence<T::IdentificationTuple>> ReportIndexStorage<T, O> {
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
