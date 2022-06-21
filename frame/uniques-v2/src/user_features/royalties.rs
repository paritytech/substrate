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
use frame_support::{
	pallet_prelude::*,
	traits::{Currency, ExistenceRequirement::KeepAlive},
};
use sp_runtime::{traits::CheckedAdd, DispatchError, Perbill};

impl<T: Config> Pallet<T> {
	pub fn do_change_creator_royalties(
		caller: T::AccountId,
		id: T::CollectionId,
		royalties: Perbill,
	) -> DispatchResult {
		Collections::<T>::try_mutate(id, |maybe_collection| {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(collection.creator == caller, Error::<T>::NotAuthorized);

			// royalties can only be decreased
			ensure!(
				royalties < collection.creator_royalties,
				Error::<T>::RoyaltiesBiggerToPreviousValue
			);

			collection.creator_royalties = royalties;

			// update collection's config
			let mut config =
				CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			let mut system_features = config.system_features.get();

			if !royalties.is_zero() && !system_features.contains(SystemFeature::CreatorRoyalties) {
				system_features.insert(SystemFeature::CreatorRoyalties);
			} else if royalties.is_zero() {
				system_features.remove(SystemFeature::CreatorRoyalties);
			}
			config.system_features = SystemFeatures::new(system_features);

			CollectionConfigs::<T>::insert(id, config);

			Self::deposit_event(Event::CreatorRoyaltiesChanged {
				id,
				royalties,
				creator: collection.creator.clone(),
			});

			Ok(())
		})
	}

	pub fn do_change_owner_royalties(
		caller: T::AccountId,
		id: T::CollectionId,
		config: CollectionConfig,
		royalties: Perbill,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		let is_locked = user_features.contains(UserFeature::IsLocked);

		Collections::<T>::try_mutate(id, |maybe_collection| {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

			let total = royalties.checked_add(&collection.creator_royalties);
			ensure!(
				total.map_or(false, |v| v < Perbill::one()),
				Error::<T>::TotalRoyaltiesExceedHundredPercent
			);

			// if collection is locked then royalties can only be decreased
			ensure!(
				!is_locked || royalties < collection.owner_royalties,
				Error::<T>::RoyaltiesBiggerToPreviousValue
			);

			collection.owner_royalties = royalties;

			// update collection's config
			let mut config =
				CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			let mut system_features = config.system_features.get();

			if !royalties.is_zero() && !system_features.contains(SystemFeature::OwnerRoyalties) {
				system_features.insert(SystemFeature::OwnerRoyalties);
			} else if royalties.is_zero() {
				system_features.remove(SystemFeature::OwnerRoyalties);
			}
			config.system_features = SystemFeatures::new(system_features);

			CollectionConfigs::<T>::insert(id, config);

			Self::deposit_event(Event::OwnerRoyaltiesChanged {
				id,
				royalties,
				owner: collection.owner.clone(),
			});

			Ok(())
		})
	}

	pub fn process_royalties(
		amount: BalanceOf<T>,
		source: &T::AccountId,
		collection: &Collection<T::CollectionId, T::AccountId, BalanceOf<T>>,
		item_id: T::ItemId,
	) -> Result<BalanceOf<T>, DispatchError> {
		let mut amount_left = amount.clone();

		if !collection.creator_royalties.is_zero() {
			let transfer_amount = collection.creator_royalties * amount;

			T::Currency::transfer(&source, &collection.creator, transfer_amount, KeepAlive)?;

			amount_left -= transfer_amount;

			Self::deposit_event(Event::CreatorRoyaltiesPaid {
				collection_id: collection.id,
				item_id,
				amount: transfer_amount,
				payer: source.clone(),
				receiver: collection.creator.clone(),
			});
		}

		if !collection.owner_royalties.is_zero() {
			let transfer_amount = collection.owner_royalties * amount;

			T::Currency::transfer(&source, &collection.owner, transfer_amount, KeepAlive)?;

			amount_left -= transfer_amount;

			Self::deposit_event(Event::OwnerRoyaltiesPaid {
				collection_id: collection.id,
				item_id,
				amount: transfer_amount,
				payer: source.clone(),
				receiver: collection.owner.clone(),
			});
		}

		Ok(amount_left)
	}

	// helpers
	pub fn has_royalties(config: &CollectionConfig) -> bool {
		let system_features: BitFlags<SystemFeature> = config.system_features.get();

		return system_features.contains(SystemFeature::CreatorRoyalties) ||
			system_features.contains(SystemFeature::OwnerRoyalties)
	}
}
