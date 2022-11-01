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
	pub(crate) fn do_lock_collection(
		origin: T::AccountId,
		collection: T::CollectionId,
		lock_settings: CollectionSettings,
	) -> DispatchResult {
		ensure!(
			Self::has_role(&collection, &origin, CollectionRole::Freezer),
			Error::<T, I>::NoPermission
		);
		ensure!(
			!lock_settings.is_disabled(CollectionSetting::DepositRequired),
			Error::<T, I>::WrongSetting
		);
		CollectionConfigOf::<T, I>::try_mutate(collection, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::NoConfig)?;

			for setting in lock_settings.get_disabled() {
				config.disable_setting(setting);
			}

			Self::deposit_event(Event::<T, I>::CollectionLocked { collection });
			Ok(())
		})
	}

	pub(crate) fn do_lock_item_transfer(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		ensure!(
			Self::has_role(&collection, &origin, CollectionRole::Freezer),
			Error::<T, I>::NoPermission
		);

		let mut config = Self::get_item_config(&collection, &item)?;
		if !config.has_disabled_setting(ItemSetting::Transferable) {
			config.disable_setting(ItemSetting::Transferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, config);

		Self::deposit_event(Event::<T, I>::ItemTransferLocked { collection, item });
		Ok(())
	}

	pub(crate) fn do_unlock_item_transfer(
		origin: T::AccountId,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		ensure!(
			Self::has_role(&collection, &origin, CollectionRole::Freezer),
			Error::<T, I>::NoPermission
		);

		let mut config = Self::get_item_config(&collection, &item)?;
		if config.has_disabled_setting(ItemSetting::Transferable) {
			config.enable_setting(ItemSetting::Transferable);
		}
		ItemConfigOf::<T, I>::insert(&collection, &item, config);

		Self::deposit_event(Event::<T, I>::ItemTransferUnlocked { collection, item });
		Ok(())
	}

	pub(crate) fn do_lock_item_properties(
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

			if lock_metadata {
				config.disable_setting(ItemSetting::UnlockedMetadata);
			}
			if lock_attributes {
				config.disable_setting(ItemSetting::UnlockedAttributes);
			}

			Self::deposit_event(Event::<T, I>::ItemPropertiesLocked {
				collection,
				item,
				lock_metadata,
				lock_attributes,
			});
			Ok(())
		})
	}
}
