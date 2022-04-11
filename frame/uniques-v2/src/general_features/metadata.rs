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
use sp_runtime::traits::Saturating;

impl<T: Config> Pallet<T> {
	pub fn do_set_collection_metadata(
		id: T::CollectionId,
		config: CollectionConfig,
		sender: T::AccountId,
		data: MetadataOf<T>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();

		if user_features.contains(UserFeatures::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into());
		}

		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == sender, Error::<T>::NotAuthorized);

		CollectionMetadataOf::<T>::try_mutate_exists(id, |metadata| {
			*metadata = Some(CollectionMetadata { data: data.clone() });
			Self::deposit_event(Event::<T>::CollectionMetadataSet { id, data });
			Ok(())
		})
	}

	pub fn do_set_item_metadata(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		caller: T::AccountId,
		data: MetadataOf<T>,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&collection_id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		ItemMetadataOf::<T>::try_mutate_exists(collection_id, item_id, |metadata| {
			if metadata.is_none() {
				collection.item_metadatas.saturating_inc();
			}

			*metadata = Some(ItemMetadata { data: data.clone() });

			Collections::<T>::insert(&collection_id, &collection);

			Self::deposit_event(Event::<T>::ItemMetadataSet { collection_id, item_id, data });
			Ok(())
		})
	}
}
