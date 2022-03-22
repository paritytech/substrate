// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::*;
use enumflags2::BitFlags;
use frame_support::pallet_prelude::*;
use sp_runtime::traits::{CheckedAdd, One};

impl<T: Config> Pallet<T> {
	pub fn do_create_collection(
		caller: T::AccountId,
		config: UserFeatures,
	) -> DispatchResult {
		let id = CountForCollections::<T>::get();

		ensure!(!CollectionConfigs::<T>::contains_key(id), Error::<T>::CollectionIdTaken);

		let default_system_config = T::DefaultSystemConfig::get();
		let collection_config = CollectionConfig {
			system_features: default_system_config,
			user_features: config,
		};
		CollectionConfigs::<T>::insert(id, collection_config);

		let collection = Collection { id, owner: caller.clone(), deposit: None };
		ensure!(!Collections::<T>::contains_key(id), Error::<T>::CollectionIdTaken);

		Collections::<T>::insert(id, collection);

		// emit events
		Self::deposit_event(Event::<T>::CollectionCreated { id });

		if config == UserFeatures::IsLocked {
			Self::deposit_event(Event::<T>::CollectionLocked { id });
		}

		// update the next id value
		let next_id = id.checked_add(&One::one()).ok_or(Error::<T>::Overflow)?;
		CountForCollections::<T>::put(next_id);

		Ok(())
	}

	pub fn do_lock_collection(
		id: T::CollectionId,
		caller: T::AccountId,
		config: CollectionConfig,
	) -> DispatchResult {
		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let mut user_features: BitFlags<UserFeatures> = config.user_features.into();

		if user_features.contains(UserFeatures::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into());
		}

		// update the flag
		user_features.insert(UserFeatures::IsLocked);

		Self::deposit_event(Event::<T>::CollectionLocked { id });

		Ok(())
	}

	pub fn do_destroy_collection(
		id: T::CollectionId,
		caller: T::AccountId,
		config: CollectionConfig,
	) -> DispatchResult {
		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let user_features: BitFlags<UserFeatures> = config.user_features.into();

		if user_features.contains(UserFeatures::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into());
		}

		// destroy the collection
		CollectionConfigs::<T>::remove(&id);
		Collections::<T>::remove(&id);
		CollectionMetadataOf::<T>::remove(&id);

		Self::deposit_event(Event::<T>::CollectionDestroyed { id });

		Ok(())
	}
}
