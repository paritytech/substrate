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

	pub fn do_freeze_item(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(collection_details.freezer == origin, Error::<T, I>::NoPermission);

		let mut settings = Self::get_item_settings(&collection, &item)?;
		if !settings.contains(ItemSetting::NonTransferable) {
			settings.insert(ItemSetting::NonTransferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, ItemConfig(settings));

		Self::deposit_event(Event::<T, I>::Frozen { collection, item });
		Ok(())
	}

	pub fn do_thaw_item(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(collection_details.freezer == origin, Error::<T, I>::NoPermission);

		let mut settings = Self::get_item_settings(&collection, &item)?;
		if settings.contains(ItemSetting::NonTransferable) {
			settings.remove(ItemSetting::NonTransferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, ItemConfig(settings));

		Self::deposit_event(Event::<T, I>::Thawed { collection, item });
		Ok(())
	}

	// helpers
	pub fn get_collection_settings(
		collection_id: &T::CollectionId,
	) -> Result<CollectionSettings, DispatchError> {
		let config = CollectionConfigOf::<T, I>::get(&collection_id)
			.ok_or(Error::<T, I>::UnknownCollection)?;
		Ok(config.values())
	}

	pub fn get_item_settings(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
	) -> Result<ItemSettings, DispatchError> {
		let config = ItemConfigOf::<T, I>::get(&collection_id, &item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		Ok(config.values())
	}

	pub fn is_collection_setting_disabled(
		collection_id: &T::CollectionId,
		setting: CollectionSetting,
	) -> Result<(bool, CollectionSettings), DispatchError> {
		let settings = Self::get_collection_settings(&collection_id)?;
		Ok((!settings.contains(setting), settings))
	}

	pub fn is_item_setting_disabled(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
		setting: ItemSetting,
	) -> Result<(bool, ItemSettings), DispatchError> {
		let settings = Self::get_item_settings(&collection_id, &item_id)?;
		Ok((!settings.contains(setting), settings))
	}

	pub fn is_feature_flag_set(feature: SystemFeature) -> bool {
		let features = T::FeatureFlags::get();
		return features.0.contains(feature)
	}
}
