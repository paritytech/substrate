// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! # Offences Pallet
//!
//! Tracks reported offences

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

//TODO pub mod migration;
mod mock;
mod tests;

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{weights::Weight, BoundedVec};
use sp_runtime::traits::Hash;
use sp_staking::offence::{
	Kind, MaxOffenders, MaxReporters, Offence, OffenceDetails, OffenceError, OnOffenceHandler,
	ReportOffence,
};
use sp_std::prelude::*;

pub use pallet::*;

/// A binary blob which represents a SCALE codec-encoded `O::TimeSlot`.
///
/// Needs to be bounded since it is included in events.
type OpaqueTimeSlotOf<T> = BoundedVec<u8, <T as Config>::MaxOpaqueTimeSlotLen>;

/// A type alias for a report identifier.
type ReportIdOf<T> = <T as frame_system::Config>::Hash;

type SameKindReportsOf<T, TimeSlot> =
	BoundedVec<(TimeSlot, ReportIdOf<T>), <T as Config>::MaxSameKindReportsPerKind>;

type ConcurrentReportsOf<T> =
	BoundedVec<ReportIdOf<T>, <T as Config>::MaxConcurrentReportsPerKindAndTime>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	/// The pallet's config trait.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// Full identification of the validator.
		type IdentificationTuple: Parameter + MaxEncodedLen;
		/// A handler called for every offence report.
		type OnOffenceHandler: OnOffenceHandler<Self::AccountId, Self::IdentificationTuple, Weight>;

		/// The maximum number of reporters per offence.
		#[pallet::constant]
		type MaxReportersPerOffence: Get<u32>;

		/// Maximum number of different kinds and different time slots reports that can be tracked.
		///
		/// Can be trivially set to `MaxReports`.
		#[pallet::constant]
		type MaxConcurrentReports: Get<Option<u32>>;

		/// Maximum number of reports of the same kind that happened at a specific time slot.
		#[pallet::constant]
		type MaxConcurrentReportsPerKindAndTime: Get<u32>;

		/// The maximum number of reports for the same kind.
		#[pallet::constant]
		type MaxSameKindReports: Get<Option<u32>>;

		/// The maximum number of reports for the same kind.
		#[pallet::constant]
		type MaxSameKindReportsPerKind: Get<u32>;

		/// Maximum encoded length of same-kind reports `SameKindReportsOf<T>`.
		///
		/// This depends on [`pallet_staking::Config::MaxNominations`].
		#[pallet::constant]
		type MaxSameKindReportsEncodedLen: Get<u32>;

		/// The maximum encoded length of an offence `TimeSlot`.
		#[pallet::constant]
		type MaxOpaqueTimeSlotLen: Get<u32>;
	}

	/// The primary structure that holds all offence records keyed by report identifiers.
	#[pallet::storage]
	#[pallet::getter(fn reports)]
	pub type Reports<T: Config> = StorageMap<
		_,
		Twox64Concat,
		ReportIdOf<T>,
		OffenceDetails<T::AccountId, T::IdentificationTuple>,
	>;

	/// A vector of reports of the same kind that happened at the same time slot.
	#[pallet::storage]
	pub type ConcurrentReportsIndex<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		Kind,
		Twox64Concat,
		OpaqueTimeSlotOf<T>,
		ConcurrentReportsOf<T>,
		ValueQuery,
	>;

	/// Enumerates all reports of a kind along with the time they happened.
	///
	/// All reports are sorted by the time of offence.
	///
	/// Note that the actual type of this mapping is `Vec<u8>`, this is because values of
	/// different types are not supported at the moment so we are doing the manual serialization.
	#[pallet::storage]
	pub type ReportsByKindIndex<T: Config> = StorageMap<
		_,
		Twox64Concat,
		Kind,
		BoundedVec<u8, T::MaxSameKindReportsEncodedLen>, // (O::TimeSlot, ReportIdOf<T>)
		ValueQuery,
	>;

	/// Events type.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// There is an offence reported of the given `kind` happened at the `session_index` and
		/// (kind-specific) time slot. This event is not deposited for duplicate slashes.
		/// \[kind, timeslot\].
		Offence { kind: Kind, timeslot: OpaqueTimeSlotOf<T> },
	}

	#[pallet::error]
	#[derive(PartialEq, Eq)]
	pub enum Error<T> {
		TooManyConcurrentReports,
		TooManySameKindReports,

		/// The length of an encoded time slot is too long.
		TimeSlotEncodingTooLong,
		/// The length of the encoded same kind reports is too long.
		SameKindReportsEncodingTooLong,
	}
}

impl<T: Config, O: Offence<T::IdentificationTuple>>
	ReportOffence<T::AccountId, T::IdentificationTuple, O> for Pallet<T>
where
	T::IdentificationTuple: Clone,
{
	fn report_offence(
		reporters: BoundedVec<T::AccountId, MaxReporters>,
		offence: O,
	) -> Result<(), OffenceError> {
		let offenders = offence.offenders();
		let time_slot = offence.time_slot();
		let validator_set_count = offence.validator_set_count();

		// Go through all offenders in the offence report and find all offenders that were spotted
		// in unique reports.
		let TriageOutcome { concurrent_offenders } =
			match Self::triage_offence_report::<O>(reporters, &time_slot, offenders)? {
				Some(triage) => triage,
				// The report contained only duplicates, so there is no need to slash again.
				None => return Err(OffenceError::DuplicateReport),
			};

		let offenders_count = concurrent_offenders.len() as u32;

		// The amount new offenders are slashed
		let new_fraction = O::slash_fraction(offenders_count, validator_set_count);

		let slash_perbill: Vec<_> = (0..concurrent_offenders.len()).map(|_| new_fraction).collect();
		let slash_perbill: BoundedVec<_, _> = slash_perbill.try_into().expect("todo");

		T::OnOffenceHandler::on_offence(
			&concurrent_offenders,
			&slash_perbill,
			offence.session_index(),
			offence.disable_strategy(),
		);

		// Deposit the event.
		Self::deposit_event(Event::Offence {
			kind: O::ID,
			timeslot: time_slot
				.encode()
				.try_into()
				.map_err(|_| Error::<T>::TimeSlotEncodingTooLong)?,
		});

		Ok(())
	}

	fn is_known_offence(
		offenders: &BoundedVec<T::IdentificationTuple, MaxOffenders>,
		time_slot: &O::TimeSlot,
	) -> bool {
		let any_unknown = offenders.iter().any(|offender| {
			let report_id = Self::report_id::<O>(time_slot, offender);
			!<Reports<T>>::contains_key(&report_id)
		});

		!any_unknown
	}
}

impl<T: Config> From<Error<T>> for OffenceError {
	fn from(err: Error<T>) -> OffenceError {
		let index = match err {
			Error::TooManyConcurrentReports => 0,
			Error::TooManySameKindReports => 1,
			Error::TimeSlotEncodingTooLong => 2,
			Error::SameKindReportsEncodingTooLong => 3,
			// This case is unreachable but don't panic, just in case.
			Error::__Ignore(_, _) => 255,
		};
		OffenceError::Other(index)
	}
}

impl<T: Config> Pallet<T> {
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
		reporters: BoundedVec<T::AccountId, MaxReporters>,
		time_slot: &O::TimeSlot,
		offenders: BoundedVec<T::IdentificationTuple, MaxOffenders>,
	) -> Result<Option<TriageOutcome<T>>, Error<T>> {
		let mut storage = ReportIndexStorage::<T, O>::load(time_slot)?;

		let mut any_new = false;
		for offender in offenders {
			let report_id = Self::report_id::<O>(time_slot, &offender);

			if !<Reports<T>>::contains_key(&report_id) {
				any_new = true;
				<Reports<T>>::insert(
					&report_id,
					OffenceDetails { offender, reporters: reporters.clone() },
				);

				storage.insert(time_slot, report_id)?;
			}
		}

		if any_new {
			// Load report details for the all reports happened at the same time.
			let concurrent_offenders = storage
				.concurrent_reports
				.iter()
				.filter_map(<Reports<T>>::get)
				.collect::<Vec<_>>()
				.try_into()
				.expect("todo");

			storage.save()?;

			Ok(Some(TriageOutcome { concurrent_offenders }))
		} else {
			Ok(None)
		}
	}
}

struct TriageOutcome<T: Config> {
	/// Other reports for the same report kinds.
	concurrent_offenders:
		BoundedVec<OffenceDetails<T::AccountId, T::IdentificationTuple>, MaxOffenders>,
}

/// An auxiliary struct for working with storage of indexes localized for a specific offence
/// kind (specified by the `O` type parameter).
///
/// This struct is responsible for aggregating storage writes and the underlying storage should not
/// accessed directly meanwhile.
///
/// The vectors are bounded for easier loading/saving into storage.
#[must_use = "The changes are not saved without called `save`"]
struct ReportIndexStorage<T: Config, O: Offence<T::IdentificationTuple>> {
	opaque_time_slot: OpaqueTimeSlotOf<T>,
	concurrent_reports: ConcurrentReportsOf<T>,
	same_kind_reports: SameKindReportsOf<T, O::TimeSlot>,
}

impl<T: Config, O: Offence<T::IdentificationTuple>> ReportIndexStorage<T, O> {
	/// Preload indexes from the storage for the specific `time_slot` and the kind of the offence.
	fn load(time_slot: &O::TimeSlot) -> Result<Self, Error<T>> {
		let opaque_time_slot: OpaqueTimeSlotOf<T> =
			time_slot.encode().try_into().map_err(|_| Error::<T>::TimeSlotEncodingTooLong)?;

		let same_kind_reports = ReportsByKindIndex::<T>::get(&O::ID);
		let same_kind_reports =
			SameKindReportsOf::<T, O::TimeSlot>::decode(&mut &same_kind_reports[..])
				.unwrap_or_default();

		let concurrent_reports = <ConcurrentReportsIndex<T>>::get(&O::ID, &opaque_time_slot);

		Ok(Self { opaque_time_slot, concurrent_reports, same_kind_reports })
	}

	/// Insert a new report to the index.
	fn insert(
		&mut self,
		time_slot: &O::TimeSlot,
		report_id: ReportIdOf<T>,
	) -> Result<(), Error<T>> {
		// Insert the report id into the list while maintaining the ordering by the time
		// slot.
		let pos = self.same_kind_reports.partition_point(|&(ref when, _)| when <= time_slot);
		self.same_kind_reports
			.try_insert(pos, (time_slot.clone(), report_id))
			.map_err(|_| crate::Error::<T>::TooManySameKindReports)?;

		// Update the list of concurrent reports.
		self.concurrent_reports
			.try_push(report_id)
			.map_err(|_| crate::Error::<T>::TooManyConcurrentReports)
	}

	/// Dump the indexes to the storage.
	fn save(self) -> Result<(), Error<T>> {
		let encoded: BoundedVec<u8, _> = self
			.same_kind_reports
			.encode()
			.try_into()
			.map_err(|_| crate::Error::<T>::SameKindReportsEncodingTooLong)?;
		ReportsByKindIndex::<T>::insert(&O::ID, encoded);
		<ConcurrentReportsIndex<T>>::insert(
			&O::ID,
			&self.opaque_time_slot,
			&self.concurrent_reports,
		);
		Ok(())
	}
}
