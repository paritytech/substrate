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
	pub(crate) fn do_force_collection_status(
		collection: T::CollectionId,
		new_owner: T::AccountId,
		issuer: T::AccountId,
		admin: T::AccountId,
		freezer: T::AccountId,
		config: CollectionConfigFor<T, I>,
	) -> DispatchResult {
		Collection::<T, I>::try_mutate(collection, |maybe_collection| {
			let mut collection_info =
				maybe_collection.take().ok_or(Error::<T, I>::UnknownCollection)?;
			let old_owner = collection_info.owner;
			collection_info.owner = new_owner.clone();
			*maybe_collection = Some(collection_info);
			CollectionAccount::<T, I>::remove(&old_owner, &collection);
			CollectionAccount::<T, I>::insert(&new_owner, &collection, ());
			CollectionConfigOf::<T, I>::insert(&collection, config);

			// delete previous values
			Self::clear_roles(&collection)?;

			let account_to_role = Self::group_roles_by_account(vec![
				(issuer, CollectionRole::Issuer),
				(admin, CollectionRole::Admin),
				(freezer, CollectionRole::Freezer),
			]);
			for (account, roles) in account_to_role {
				CollectionRoleOf::<T, I>::insert(&collection, &account, roles);
			}

			Self::deposit_event(Event::CollectionStatusChanged { collection });
			Ok(())
		})
	}

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

	pub(crate) fn do_update_mint_settings(
		maybe_check_owner: Option<T::AccountId>,
		collection: T::CollectionId,
		mint_settings: MintSettings<
			BalanceOf<T, I>,
			<T as SystemConfig>::BlockNumber,
			T::CollectionId,
		>,
	) -> DispatchResult {
		let details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		if let Some(check_owner) = &maybe_check_owner {
			ensure!(check_owner == &details.owner, Error::<T, I>::NoPermission);
		}

		CollectionConfigOf::<T, I>::try_mutate(collection, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T, I>::NoConfig)?;
			config.mint_settings = mint_settings;
			Self::deposit_event(Event::CollectionMintSettingsUpdated { collection });
			Ok(())
		})
	}

	pub(crate) fn get_collection_config(
		collection_id: &T::CollectionId,
	) -> Result<CollectionConfigFor<T, I>, DispatchError> {
		let config =
			CollectionConfigOf::<T, I>::get(&collection_id).ok_or(Error::<T, I>::NoConfig)?;
		Ok(config)
	}

	pub(crate) fn get_item_config(
		collection_id: &T::CollectionId,
		item_id: &T::ItemId,
	) -> Result<ItemConfig, DispatchError> {
		let config = ItemConfigOf::<T, I>::get(&collection_id, &item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		Ok(config)
	}

	pub(crate) fn is_pallet_feature_enabled(feature: PalletFeature) -> bool {
		let features = T::Features::get();
		return features.is_enabled(feature)
	}
}
