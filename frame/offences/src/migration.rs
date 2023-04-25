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

use super::{Config, Kind, OffenceDetails, Pallet, Perbill, SessionIndex, LOG_TARGET};
use frame_support::{
	dispatch::GetStorageVersion,
	pallet_prelude::ValueQuery,
	storage_alias,
	traits::{Get, OnRuntimeUpgrade},
	weights::Weight,
	Twox64Concat,
};
use sp_staking::offence::{DisableStrategy, OnOffenceHandler};
use sp_std::vec::Vec;

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

mod v0 {
	use super::*;

	#[storage_alias]
	pub type ReportsByKindIndex<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		Kind,
		Vec<u8>, // (O::TimeSlot, ReportIdOf<T>)
		ValueQuery,
	>;
}

pub mod v1 {
	use frame_support::traits::StorageVersion;

	use super::*;

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();
			ensure!(onchain < 1, "pallet_offences::MigrateToV1 migration can be deleted");

			log::info!(
				target: LOG_TARGET,
				"Number of reports to refund and delete: {}",
				v0::ReportsByKindIndex::<T>::iter_keys().count()
			);

			Ok(Vec::new())
		}

		fn on_runtime_upgrade() -> Weight {
			let onchain = Pallet::<T>::on_chain_storage_version();

			if onchain > 0 {
				log::info!(target: LOG_TARGET, "pallet_offences::MigrateToV1 should be removed");
				return T::DbWeight::get().reads(1)
			}

			let keys_removed = v0::ReportsByKindIndex::<T>::clear(u32::MAX, None).unique as u64;
			let weight = T::DbWeight::get().reads_writes(keys_removed, keys_removed);

			StorageVersion::new(1).put::<Pallet<T>>();

			weight
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();
			ensure!(onchain == 1, "pallet_offences::MigrateToV1 needs to be run");
			ensure!(
				v0::ReportsByKindIndex::<T>::iter_keys().count() == 0,
				"there are some dangling reports that need to be destroyed and refunded"
			);
			Ok(())
		}
	}
}

/// Type of data stored as a deferred offence
type DeferredOffenceOf<T> = (
	Vec<OffenceDetails<<T as frame_system::Config>::AccountId, <T as Config>::IdentificationTuple>>,
	Vec<Perbill>,
	SessionIndex,
);

// Deferred reports that have been rejected by the offence handler and need to be submitted
// at a later time.
#[storage_alias]
type DeferredOffences<T: Config> =
	StorageValue<crate::Pallet<T>, Vec<DeferredOffenceOf<T>>, ValueQuery>;

pub fn remove_deferred_storage<T: Config>() -> Weight {
	let mut weight = T::DbWeight::get().reads_writes(1, 1);
	let deferred = <DeferredOffences<T>>::take();
	log::info!(target: LOG_TARGET, "have {} deferred offences, applying.", deferred.len());
	for (offences, perbill, session) in deferred.iter() {
		let consumed = T::OnOffenceHandler::on_offence(
			offences,
			perbill,
			*session,
			DisableStrategy::WhenSlashed,
		);
		weight = weight.saturating_add(consumed);
	}

	weight
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::mock::{new_test_ext, with_on_offence_fractions, Runtime as T, KIND};
	use codec::Encode;
	use sp_runtime::Perbill;
	use sp_staking::offence::OffenceDetails;

	#[test]
	fn migration_to_v1_works() {
		let mut ext = new_test_ext();

		ext.execute_with(|| {
			<v0::ReportsByKindIndex<T>>::insert(KIND, 2u32.encode());
			assert!(<v0::ReportsByKindIndex<T>>::iter_values().count() > 0);
		});

		ext.commit_all().unwrap();

		ext.execute_with(|| {
			assert_eq!(
				v1::MigrateToV1::<T>::on_runtime_upgrade(),
				<T as frame_system::Config>::DbWeight::get().reads_writes(1, 1),
			);

			assert!(<v0::ReportsByKindIndex<T>>::iter_values().count() == 0);
		})
	}

	#[test]
	fn should_resubmit_deferred_offences() {
		new_test_ext().execute_with(|| {
			// given
			assert_eq!(<DeferredOffences<T>>::get().len(), 0);
			with_on_offence_fractions(|f| {
				assert_eq!(f.clone(), vec![]);
			});

			let offence_details = OffenceDetails::<
				<T as frame_system::Config>::AccountId,
				<T as Config>::IdentificationTuple,
			> {
				offender: 5,
				reporters: vec![],
			};

			// push deferred offence
			<DeferredOffences<T>>::append((
				vec![offence_details],
				vec![Perbill::from_percent(5 + 1 * 100 / 5)],
				1,
			));

			// when
			assert_eq!(
				remove_deferred_storage::<T>(),
				<T as frame_system::Config>::DbWeight::get().reads_writes(1, 1),
			);

			// then
			assert!(!<DeferredOffences<T>>::exists());
			with_on_offence_fractions(|f| {
				assert_eq!(f.clone(), vec![Perbill::from_percent(5 + 1 * 100 / 5)]);
			});
		})
	}
}
