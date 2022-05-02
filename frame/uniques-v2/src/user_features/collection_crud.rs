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
use sp_runtime::{
	traits::{CheckedAdd, One},
	Perbill,
};

impl<T: Config> Pallet<T> {
	pub fn do_create_collection(
		creator: T::AccountId,
		owner: T::AccountId,
		user_config: UserFeatures,
		max_supply: Option<u32>,
		max_items_per_account: Option<u32>,
		creator_royalties: Perbill,
		owner_royalties: Perbill,
	) -> DispatchResult {
		let id = CollectionNextId::<T>::get();

		ensure!(!CollectionConfigs::<T>::contains_key(id), Error::<T>::CollectionIdTaken);

		let mut system_features = (T::DefaultSystemConfig::get()).get();

		if !creator_royalties.is_zero() {
			system_features.insert(SystemFeature::CreatorRoyalties);
		}
		if !owner_royalties.is_zero() {
			system_features.insert(SystemFeature::OwnerRoyalties);
		}

		let collection_config = CollectionConfig {
			system_features: SystemFeatures::new(system_features),
			user_features: user_config,
		};
		CollectionConfigs::<T>::insert(id, collection_config);

		let collection = Collection {
			id,
			creator: creator.clone(),
			owner: owner.clone(),
			deposit: None,
			attributes: 0,
			items: 0,
			item_metadatas: 0,
			max_supply,
			max_items_per_account,
			creator_royalties,
			owner_royalties,
		};
		ensure!(!Collections::<T>::contains_key(id), Error::<T>::CollectionIdTaken);

		Collections::<T>::insert(id, collection);
		CollectionOwner::<T>::insert(&owner, &id, ());
		CollectionCreator::<T>::insert(&creator, &id, ());

		// emit events

		let user_features: BitFlags<UserFeature> = collection_config.user_features.get();
		if user_features.contains(UserFeature::IsLocked) {
			Self::deposit_event(Event::<T>::CollectionLocked { id });
		}

		Self::deposit_event(Event::<T>::CollectionCreated { id, max_supply, creator, owner });

		// update the next id value
		let next_id = id.checked_add(&One::one()).ok_or(Error::<T>::Overflow)?;
		CollectionNextId::<T>::put(next_id);

		// TODO: maybe we should return the id here?
		Ok(())
	}

	pub fn do_update_max_supply(
		id: T::CollectionId,
		caller: T::AccountId,
		config: CollectionConfig,
		max_supply: Option<u32>,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let user_features: BitFlags<UserFeature> = config.user_features.get();

		if user_features.contains(UserFeature::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into())
		}

		collection.max_supply = max_supply;
		Collections::<T>::insert(&id, collection);

		Self::deposit_event(Event::<T>::CollectionMaxSupplyChanged { id, max_supply });

		Ok(())
	}

	pub fn do_update_max_items_per_account(
		id: T::CollectionId,
		caller: T::AccountId,
		config: CollectionConfig,
		max_items_per_account: Option<u32>,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let user_features: BitFlags<UserFeature> = config.user_features.get();

		if user_features.contains(UserFeature::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into())
		}

		collection.max_items_per_account = max_items_per_account;
		Collections::<T>::insert(&id, collection);

		Self::deposit_event(Event::<T>::CollectionMaxItemsPerAccountChanged {
			id,
			max_items_per_account,
		});

		Ok(())
	}

	pub fn do_change_collection_config(
		id: T::CollectionId,
		caller: T::AccountId,
		current_config: CollectionConfig,
		new_config: UserFeatures,
	) -> DispatchResult {
		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let user_features: BitFlags<UserFeature> = current_config.user_features.get();

		if user_features.contains(UserFeature::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into())
		}

		CollectionConfigs::<T>::try_mutate(id, |maybe_config| {
			let config = maybe_config.as_mut().ok_or(Error::<T>::CollectionNotFound)?;

			config.user_features = new_config;

			Self::deposit_event(Event::<T>::CollectionConfigChanged { id });

			Ok(())
		})
	}

	pub fn do_destroy_collection(
		id: T::CollectionId,
		caller: T::AccountId,
		config: CollectionConfig,
		witness: DestroyWitness,
	) -> DispatchResult {
		let collection = Collections::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);
		ensure!(collection.attributes == witness.attributes, Error::<T>::BadWitness);
		ensure!(collection.items == witness.items, Error::<T>::BadWitness);
		ensure!(collection.item_metadatas == witness.item_metadatas, Error::<T>::BadWitness);

		let user_features: BitFlags<UserFeature> = config.user_features.get();

		if user_features.contains(UserFeature::IsLocked) {
			return Err(Error::<T>::CollectionIsLocked.into())
		}

		// destroy the collection
		CollectionConfigs::<T>::remove(&id);
		Collections::<T>::remove(&id);
		CollectionMetadataOf::<T>::remove(&id);
		CollectionOwner::<T>::remove(&collection.owner, &id);
		CollectionCreator::<T>::remove(&collection.creator, &id);
		Attributes::<T>::remove_prefix((&id,), None);

		for (item_id, details) in Items::<T>::drain_prefix(&id) {
			AccountItems::<T>::remove((&details.owner, &id, &item_id));
			CountForAccountItems::<T>::remove(&details.owner, &id);
		}

		ItemMetadataOf::<T>::remove_prefix(&id, None);

		Self::deposit_event(Event::<T>::CollectionDestroyed { id });

		Ok(())
	}
}
