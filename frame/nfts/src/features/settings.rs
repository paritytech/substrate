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

//! This module provides helper methods to configure collection settings for the NFTs pallet.

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Forcefully change the configuration of a collection.
	///
	/// - `collection`: The ID of the collection for which to update the configuration.
	/// - `config`: The new collection configuration to set.
	///
	/// This function allows for changing the configuration of a collection without any checks.
	/// It updates the collection configuration and emits a `CollectionConfigChanged` event.
	pub(crate) fn do_force_collection_config(
		collection: T::CollectionId,
		config: CollectionConfigFor<T, I>,
	) -> DispatchResult {
		ensure!(Collection::<T, I>::contains_key(&collection), Error::<T, I>::UnknownCollection);
		CollectionConfigOf::<T, I>::insert(&collection, config);
		Self::deposit_event(Event::CollectionConfigChanged { collection });
		Ok(())
	}

	/// Set the maximum supply for a collection.
	///
	/// - `maybe_check_owner`: An optional account ID used to check permissions.
	/// - `collection`: The ID of the collection for which to set the maximum supply.
	/// - `max_supply`: The new maximum supply to set for the collection.
	///
	/// This function checks if the setting `UnlockedMaxSupply` is enabled in the collection
	/// configuration. If it is not enabled, it returns an `Error::MaxSupplyLocked`. If
	/// `maybe_check_owner` is `Some(owner)`, it checks if the caller of the function is the
	/// owner of the collection. If the caller is not the owner and the `maybe_check_owner`
	/// parameter is provided, it returns an `Error::NoPermission`.
	///
	/// It also checks if the new maximum supply is greater than the current number of items in
	/// the collection, and if not, it returns an `Error::MaxSupplyTooSmall`. If all checks pass,
	/// it updates the collection configuration with the new maximum supply and emits a
	/// `CollectionMaxSupplySet` event.
	pub(crate) fn do_set_collection_max_supply(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		max_supply: u32,
	) -> DispatchResult {
		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			collection_config.is_setting_enabled(CollectionSetting::UnlockedMaxSupply),
			Error::<T, I>::MaxSupplyLocked
		);

		let details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		if let Some(check_owner) = &maybe_check_owner {
			ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
		}

		ensure!(details.items <= max_supply, Error::<T, I>::MaxSupplyTooSmall);

		CollectionConfigOf::<T, I>::try_mutate(collection, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::NoConfig)?;
			config.max_supply = Some(max_supply);
			Self::deposit_event(Event::CollectionMaxSupplySet { collection, max_supply });
			Ok(())
		})
	}

	/// Update the mint settings for a collection.
	///
	/// - `maybe_check_origin`: An optional account ID used to check issuer permissions.
	/// - `collection`: The ID of the collection for which to update the mint settings.
	/// - `mint_settings`: The new mint settings to set for the collection.
	///
	/// This function updates the mint settings for a collection. If `maybe_check_origin` is
	/// `Some(origin)`, it checks if the caller of the function has the `CollectionRole::Issuer`
	/// for the given collection. If the caller doesn't have the required permission and
	/// `maybe_check_origin` is provided, it returns an `Error::NoPermission`. If all checks
	/// pass, it updates the collection configuration with the new mint settings and emits a
	/// `CollectionMintSettingsUpdated` event.
	pub(crate) fn do_update_mint_settings(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		mint_settings: MintSettings<
			BalanceOf<T, I>,
			frame_system::pallet_prelude::BlockNumberFor<T>,
			T::CollectionId,
		>,
	) -> DispatchResult {
		if let Some(check_origin) = &maybe_check_origin {
			ensure!(
				Self::has_role(&collection, &check_origin, CollectionRole::Issuer),
				Error::<T, I>::NoPermission
			);
		}

		CollectionConfigOf::<T, I>::try_mutate(collection, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::NoConfig)?;
			config.mint_settings = mint_settings;
			Self::deposit_event(Event::CollectionMintSettingsUpdated { collection });
			Ok(())
		})
	}

	/// Get the configuration for a specific collection.
	///
	/// - `collection_id`: The ID of the collection for which to retrieve the configuration.
	///
	/// This function attempts to fetch the configuration (`CollectionConfigFor`) associated
	/// with the given `collection_id`. If the configuration exists, it returns `Ok(config)`,
	/// otherwise, it returns a `DispatchError` with `Error::NoConfig`.
	pub(crate) fn get_collection_config(
		collection_id: &T::CollectionId,
	) -> Result<CollectionConfigFor<T, I>, DispatchError> {
		let config =
			CollectionConfigOf::<T, I>::get(&collection_id).ok_or(Error::<T, I>::NoConfig)?;
		Ok(config)
	}

	/// Get the configuration for a specific item within a collection.
	///
	/// - `collection_id`: The ID of the collection to which the item belongs.
	/// - `item_id`: The ID of the item for which to retrieve the configuration.
	///
	/// This function attempts to fetch the configuration (`ItemConfig`) associated with the given
	/// `collection_id` and `item_id`. If the configuration exists, it returns `Ok(config)`,
	/// otherwise, it returns a `DispatchError` with `Error::UnknownItem`.
	pub(crate) fn get_item_config(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
	) -> Result<ItemConfig, DispatchError> {
		let config = ItemConfigOf::<T, I>::get(&collection_id, &item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		Ok(config)
	}

	/// Get the default item settings for a specific collection.
	///
	/// - `collection_id`: The ID of the collection for which to retrieve the default item settings.
	///
	/// This function fetches the `default_item_settings` from the collection configuration
	/// associated with the given `collection_id`. If the collection configuration exists, it
	/// returns `Ok(default_item_settings)`, otherwise, it returns a `DispatchError` with
	/// `Error::NoConfig`.
	pub(crate) fn get_default_item_settings(
		collection_id: &T::CollectionId,
	) -> Result<ItemSettings, DispatchError> {
		let collection_config = Self::get_collection_config(collection_id)?;
		Ok(collection_config.mint_settings.default_item_settings)
	}

	/// Check if a specified pallet feature is enabled.
	///
	/// - `feature`: The feature to check.
	///
	/// This function checks if the given `feature` is enabled in the runtime using the
	/// pallet's `T::Features::get()` function. It returns `true` if the feature is enabled,
	/// otherwise it returns `false`.
	pub(crate) fn is_pallet_feature_enabled(feature: PalletFeature) -> bool {
		let features = T::Features::get();
		return features.is_enabled(feature)
	}
}
