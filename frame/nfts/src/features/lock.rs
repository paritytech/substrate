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
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_lock_collection(
		origin: T::AccountId,
		collection: T::CollectionId,
		lock_config: CollectionConfig,
	) -> DispatchResult {
		let details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(origin == details.freezer, Error::<T, I>::NoPermission);

		CollectionConfigOf::<T, I>::try_mutate(collection, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
			let mut settings = config.values();
			let lock_settings = lock_config.values();

			if lock_settings.contains(CollectionSetting::NonTransferableItems) {
				settings.insert(CollectionSetting::NonTransferableItems);
			}
			if lock_settings.contains(CollectionSetting::LockedMetadata) {
				settings.insert(CollectionSetting::LockedMetadata);
			}
			if lock_settings.contains(CollectionSetting::LockedAttributes) {
				settings.insert(CollectionSetting::LockedAttributes);
			}

			config.0 = settings;

			Self::deposit_event(Event::<T, I>::CollectionLocked { collection });
			Ok(())
		})
	}

	pub fn do_lock_item(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
		lock_metadata: bool,
		lock_attributes: bool,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		if let Some(check_owner) = &maybe_check_owner {
			ensure!(check_owner == &collection_details.owner, Error::<T, I>::NoPermission);
		}

		ItemConfigOf::<T, I>::try_mutate(collection, item, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::UnknownItem)?;
			let mut settings = config.values();

			if lock_metadata {
				settings.insert(ItemSetting::LockedMetadata);
			}
			if lock_attributes {
				settings.insert(ItemSetting::LockedAttributes);
			}

			config.0 = settings;

			Self::deposit_event(Event::<T, I>::ItemLocked {
				collection,
				item,
				lock_metadata,
				lock_attributes,
			});
			Ok(())
		})
	}
}
