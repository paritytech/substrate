// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Implementations for `nonfungibles` traits.

use super::*;
use frame_support::{
	traits::{tokens::nonfungibles_v2::*, Get},
	BoundedSlice,
};
use sp_runtime::{DispatchError, DispatchResult};
use sp_std::prelude::*;

impl<T: Config<I>, I: 'static> Inspect<<T as SystemConfig>::AccountId> for Pallet<T, I> {
	type ItemId = T::ItemId;
	type CollectionId = T::CollectionId;

	fn owner(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
	) -> Option<<T as SystemConfig>::AccountId> {
		Item::<T, I>::get(collection, item).map(|a| a.owner)
	}

	fn collection_owner(collection: &Self::CollectionId) -> Option<<T as SystemConfig>::AccountId> {
		Collection::<T, I>::get(collection).map(|a| a.owner)
	}

	/// Returns the attribute value of `item` of `collection` corresponding to `key`.
	///
	/// When `key` is empty, we return the item metadata value.
	///
	/// By default this is `None`; no attributes are defined.
	fn attribute(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &[u8],
	) -> Option<Vec<u8>> {
		if key.is_empty() {
			// We make the empty key map to the item metadata value.
			ItemMetadataOf::<T, I>::get(collection, item).map(|m| m.data.into())
		} else {
			let key = BoundedSlice::<_, _>::try_from(key).ok()?;
			Attribute::<T, I>::get((collection, Some(item), key)).map(|a| a.0.into())
		}
	}

	/// Returns the attribute value of `item` of `collection` corresponding to `key`.
	///
	/// When `key` is empty, we return the item metadata value.
	///
	/// By default this is `None`; no attributes are defined.
	fn collection_attribute(collection: &Self::CollectionId, key: &[u8]) -> Option<Vec<u8>> {
		if key.is_empty() {
			// We make the empty key map to the item metadata value.
			CollectionMetadataOf::<T, I>::get(collection).map(|m| m.data.into())
		} else {
			let key = BoundedSlice::<_, _>::try_from(key).ok()?;
			Attribute::<T, I>::get((collection, Option::<T::ItemId>::None, key)).map(|a| a.0.into())
		}
	}

	/// Returns `true` if the `item` of `collection` may be transferred.
	///
	/// Default implementation is that all items are transferable.
	fn can_transfer(collection: &Self::CollectionId, item: &Self::ItemId) -> bool {
		match (
			CollectionConfigOf::<T, I>::get(collection),
			ItemConfigOf::<T, I>::get(collection, item),
		) {
			(Some(cc), Some(ic))
				if cc.is_setting_enabled(CollectionSetting::TransferableItems) &&
					ic.is_setting_enabled(ItemSetting::Transferable) =>
				true,
			_ => false,
		}
	}
}

impl<T: Config<I>, I: 'static> Create<<T as SystemConfig>::AccountId, CollectionSettings>
	for Pallet<T, I>
{
	/// Create a `collection` of nonfungible items to be owned by `who` and managed by `admin`.
	fn create_collection(
		collection: &Self::CollectionId,
		who: &T::AccountId,
		admin: &T::AccountId,
		disabled_settings: &CollectionSettings,
	) -> DispatchResult {
		let mut disabled_settings = *disabled_settings;
		// DepositRequired can be disabled by calling the force_create() only
		if disabled_settings.contains(CollectionSetting::DepositRequired) {
			disabled_settings.remove(CollectionSetting::DepositRequired);
		}
		Self::do_create_collection(
			*collection,
			who.clone(),
			admin.clone(),
			CollectionConfig::disable_settings(disabled_settings),
			T::CollectionDeposit::get(),
			Event::Created { collection: *collection, creator: who.clone(), owner: admin.clone() },
		)
	}
}

impl<T: Config<I>, I: 'static> Destroy<<T as SystemConfig>::AccountId> for Pallet<T, I> {
	type DestroyWitness = DestroyWitness;

	fn get_destroy_witness(collection: &Self::CollectionId) -> Option<DestroyWitness> {
		Collection::<T, I>::get(collection).map(|a| a.destroy_witness())
	}

	fn destroy(
		collection: Self::CollectionId,
		witness: Self::DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<Self::DestroyWitness, DispatchError> {
		Self::do_destroy_collection(collection, witness, maybe_check_owner)
	}
}

impl<T: Config<I>, I: 'static> Mutate<<T as SystemConfig>::AccountId, ItemSettings>
	for Pallet<T, I>
{
	fn mint_into(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		who: &T::AccountId,
		settings: &ItemSettings,
	) -> DispatchResult {
		Self::do_mint(*collection, *item, who.clone(), ItemConfig(*settings), |_| Ok(()))
	}

	fn burn(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		maybe_check_owner: Option<&T::AccountId>,
	) -> DispatchResult {
		Self::do_burn(*collection, *item, |_, d| {
			if let Some(check_owner) = maybe_check_owner {
				if &d.owner != check_owner {
					return Err(Error::<T, I>::NoPermission.into())
				}
			}
			Ok(())
		})
	}
}

impl<T: Config<I>, I: 'static> Transfer<T::AccountId> for Pallet<T, I> {
	fn transfer(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		destination: &T::AccountId,
	) -> DispatchResult {
		Self::do_transfer(*collection, *item, destination.clone(), |_, _| Ok(()))
	}
}

impl<T: Config<I>, I: 'static> InspectEnumerable<T::AccountId> for Pallet<T, I> {
	/// Returns an iterator of the collections in existence.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn collections() -> Box<dyn Iterator<Item = Self::CollectionId>> {
		Box::new(CollectionMetadataOf::<T, I>::iter_keys())
	}

	/// Returns an iterator of the items of a `collection` in existence.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn items(collection: &Self::CollectionId) -> Box<dyn Iterator<Item = Self::ItemId>> {
		Box::new(ItemMetadataOf::<T, I>::iter_key_prefix(collection))
	}

	/// Returns an iterator of the items of all collections owned by `who`.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn owned(who: &T::AccountId) -> Box<dyn Iterator<Item = (Self::CollectionId, Self::ItemId)>> {
		Box::new(Account::<T, I>::iter_key_prefix((who,)))
	}

	/// Returns an iterator of the items of `collection` owned by `who`.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn owned_in_collection(
		collection: &Self::CollectionId,
		who: &T::AccountId,
	) -> Box<dyn Iterator<Item = Self::ItemId>> {
		Box::new(Account::<T, I>::iter_key_prefix((who, collection)))
	}
}
