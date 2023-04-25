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

use crate::{Pallet, Config, LOG_TARGET};
use frame_support::{
    traits::{Get, OnRuntimeUpgrade},
    dispatch::GetStorageVersion,
    storage::storage_prefix,
    weights::Weight,
};
use sp_io::{storage::clear_prefix, KillStorageResult};

pub struct MigrateToV2<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> OnRuntimeUpgrade for MigrateToV2<T> {
    #[cfg(feature = "try-runtime")]
    fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
        let onchain = Pallet::<T>::on_chain_storage_version();
        ensure!(onchain < 2, "pallet_session::MigrateToV2 migration can be deleted");
        Ok(Vec::new())
    }

    fn on_runtime_upgrade() -> Weight {
        let current = Pallet::<T>::current_storage_version();
        let onchain = Pallet::<T>::on_chain_storage_version();

        if onchain > 1 {
            log::info!(target: LOG_TARGET, "pallet_session::MigrateToV2 should be removed");
            return T::DbWeight::get().reads(1)
        }

        let prefix = storage_prefix(b"Session", b"StoredRange");
        let keys_removed_stored_range = match clear_prefix(&prefix, None) {
			KillStorageResult::AllRemoved(value) => value,
			KillStorageResult::SomeRemaining(value) => {
				log::error!(
					"`clear_prefix` failed to remove all keys. THIS SHOULD NEVER HAPPEN! 🚨",
				);
				value
			},
		} as u64;

        let prefix = storage_prefix(b"Session", b"HistoricalSessions");
        let keys_removed_historical_sessions = match clear_prefix(&prefix, None) {
			KillStorageResult::AllRemoved(value) => value,
			KillStorageResult::SomeRemaining(value) => {
				log::error!(
					"`clear_prefix` failed to remove all keys. THIS SHOULD NEVER HAPPEN! 🚨",
				);
				value
			},
		} as u64;

        let keys_removed = keys_removed_stored_range + keys_removed_historical_sessions;
		log::info!("Removed {} keys 🧹", keys_removed);

        current.put::<Pallet<T>>();

        T::DbWeight::get().reads_writes(keys_removed, keys_removed)
    }

    #[cfg(feature = "try-runtime")]
    fn post_upgrade(_state: Vec<u8>) -> Result<(), &'static str> {
        let onchain = Pallet::<T>::on_chain_storage_version();
        ensure!(onchain == 2, "pallet_session::MigrateToV2 needs to be run");
        Ok(())
    }
}

#[cfg(test)]
mod test {
	use super::*;
    use crate::mock::{new_test_ext, Test as T};
    use frame_support::{weights::RuntimeDbWeight, Twox64Concat};

    #[test]
	fn migration_to_v1_works() {
        #[frame_support::storage_alias]
        type HistoricalSessions = StorageMap<Session, Twox64Concat, u64, u64>;

        #[frame_support::storage_alias]
        type StoredRange = StorageValue<Session, u64>;

		let mut ext = new_test_ext();

		ext.execute_with(|| {
			HistoricalSessions::insert(1, 10);
            StoredRange::set(Some(5));

			assert!(HistoricalSessions::iter_keys().collect::<Vec<_>>().len() > 0);
            assert_eq!(StoredRange::get(), Some(5));
		});

		ext.commit_all().unwrap();

		ext.execute_with(|| {
            let weight: RuntimeDbWeight = <T as frame_system::Config>::DbWeight::get();

			assert_eq!(
				MigrateToV2::<T>::on_runtime_upgrade(),
				weight.reads_writes(2, 2),
			);

			assert!(HistoricalSessions::iter_keys().collect::<Vec<_>>().len() == 0);
            assert_eq!(StoredRange::get(), None);
		})
	}
}