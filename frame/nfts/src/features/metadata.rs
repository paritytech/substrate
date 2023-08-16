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

//! This module contains helper methods to configure the metadata of collections and items.

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Sets the metadata for a specific item within a collection.
	///
	/// - `maybe_check_origin`: An optional account ID that is allowed to set the metadata. If
	///   `None`, it's considered the root account.
	/// - `collection`: The ID of the collection to which the item belongs.
	/// - `item`: The ID of the item to set the metadata for.
	/// - `data`: The metadata to set for the item.
	/// - `maybe_depositor`: An optional account ID that will provide the deposit for the metadata.
	///   If `None`, the collection's owner provides the deposit.
	///
	/// Emits `ItemMetadataSet` event upon successful setting of the metadata.
	/// Returns `Ok(())` on success, or one of the following dispatch errors:
	/// - `UnknownCollection`: The specified collection does not exist.
	/// - `UnknownItem`: The specified item does not exist within the collection.
	/// - `LockedItemMetadata`: The metadata for the item is locked and cannot be modified.
	/// - `NoPermission`: The caller does not have the required permission to set the metadata.
	/// - `DepositExceeded`: The deposit amount exceeds the maximum allowed value.
	pub(crate) fn do_set_item_metadata(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
		data: BoundedVec<u8, T::StringLimit>,
		maybe_depositor: Option<T::AccountId>,
	) -> DispatchResult {
		if let Some(check_origin) = &maybe_check_origin {
			ensure!(
				Self::has_role(&collection, &check_origin, CollectionRole::Admin),
				Error::<T, I>::NoPermission
			);
		}

		let is_root = maybe_check_origin.is_none();
		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		let item_config = Self::get_item_config(&collection, &item)?;
		ensure!(
			is_root || item_config.is_setting_enabled(ItemSetting::UnlockedMetadata),
			Error::<T, I>::LockedItemMetadata
		);

		let collection_config = Self::get_collection_config(&collection)?;

		ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
			if metadata.is_none() {
				collection_details.item_metadatas.saturating_inc();
			}

			let old_deposit = metadata
				.take()
				.map_or(ItemMetadataDeposit { account: None, amount: Zero::zero() }, |m| m.deposit);

			let mut deposit = Zero::zero();
			if collection_config.is_setting_enabled(CollectionSetting::DepositRequired) && !is_root
			{
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}

			let depositor = maybe_depositor.clone().unwrap_or(collection_details.owner.clone());
			let old_depositor = old_deposit.account.unwrap_or(collection_details.owner.clone());

			if depositor != old_depositor {
				T::Currency::unreserve(&old_depositor, old_deposit.amount);
				T::Currency::reserve(&depositor, deposit)?;
			} else if deposit > old_deposit.amount {
				T::Currency::reserve(&depositor, deposit - old_deposit.amount)?;
			} else if deposit < old_deposit.amount {
				T::Currency::unreserve(&depositor, old_deposit.amount - deposit);
			}

			if maybe_depositor.is_none() {
				collection_details.owner_deposit.saturating_accrue(deposit);
				collection_details.owner_deposit.saturating_reduce(old_deposit.amount);
			}

			*metadata = Some(ItemMetadata {
				deposit: ItemMetadataDeposit { account: maybe_depositor, amount: deposit },
				data: data.clone(),
			});

			Collection::<T, I>::insert(&collection, &collection_details);
			Self::deposit_event(Event::ItemMetadataSet { collection, item, data });
			Ok(())
		})
	}

	/// Clears the metadata for a specific item within a collection.
	///
	/// - `maybe_check_origin`: An optional account ID that is allowed to clear the metadata. If
	///   `None`, it's considered the root account.
	/// - `collection`: The ID of the collection to which the item belongs.
	/// - `item`: The ID of the item for which to clear the metadata.
	///
	/// Emits `ItemMetadataCleared` event upon successful clearing of the metadata.
	/// Returns `Ok(())` on success, or one of the following dispatch errors:
	/// - `UnknownCollection`: The specified collection does not exist.
	/// - `MetadataNotFound`: The metadata for the specified item was not found.
	/// - `LockedItemMetadata`: The metadata for the item is locked and cannot be modified.
	/// - `NoPermission`: The caller does not have the required permission to clear the metadata.
	pub(crate) fn do_clear_item_metadata(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		if let Some(check_origin) = &maybe_check_origin {
			ensure!(
				Self::has_role(&collection, &check_origin, CollectionRole::Admin),
				Error::<T, I>::NoPermission
			);
		}

		let is_root = maybe_check_origin.is_none();
		let metadata = ItemMetadataOf::<T, I>::take(collection, item)
			.ok_or(Error::<T, I>::MetadataNotFound)?;
		let mut collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		let depositor_account =
			metadata.deposit.account.unwrap_or(collection_details.owner.clone());

		// NOTE: if the item was previously burned, the ItemConfigOf record might not exist
		let is_locked = Self::get_item_config(&collection, &item)
			.map_or(false, |c| c.has_disabled_setting(ItemSetting::UnlockedMetadata));

		ensure!(is_root || !is_locked, Error::<T, I>::LockedItemMetadata);

		collection_details.item_metadatas.saturating_dec();
		T::Currency::unreserve(&depositor_account, metadata.deposit.amount);

		if depositor_account == collection_details.owner {
			collection_details.owner_deposit.saturating_reduce(metadata.deposit.amount);
		}

		Collection::<T, I>::insert(&collection, &collection_details);
		Self::deposit_event(Event::ItemMetadataCleared { collection, item });

		Ok(())
	}

	/// Sets the metadata for a specific collection.
	///
	/// - `maybe_check_origin`: An optional account ID that is allowed to set the collection
	///   metadata. If `None`, it's considered the root account.
	/// - `collection`: The ID of the collection for which to set the metadata.
	/// - `data`: The metadata to set for the collection.
	///
	/// Emits `CollectionMetadataSet` event upon successful setting of the metadata.
	/// Returns `Ok(())` on success, or one of the following dispatch errors:
	/// - `UnknownCollection`: The specified collection does not exist.
	/// - `LockedCollectionMetadata`: The metadata for the collection is locked and cannot be
	///   modified.
	/// - `NoPermission`: The caller does not have the required permission to set the metadata.
	pub(crate) fn do_set_collection_metadata(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		data: BoundedVec<u8, T::StringLimit>,
	) -> DispatchResult {
		if let Some(check_origin) = &maybe_check_origin {
			ensure!(
				Self::has_role(&collection, &check_origin, CollectionRole::Admin),
				Error::<T, I>::NoPermission
			);
		}

		let is_root = maybe_check_origin.is_none();
		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			is_root || collection_config.is_setting_enabled(CollectionSetting::UnlockedMetadata),
			Error::<T, I>::LockedCollectionMetadata
		);

		let mut details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			details.owner_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if !is_root && collection_config.is_setting_enabled(CollectionSetting::DepositRequired)
			{
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}
			if deposit > old_deposit {
				T::Currency::reserve(&details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&details.owner, old_deposit - deposit);
			}
			details.owner_deposit.saturating_accrue(deposit);

			Collection::<T, I>::insert(&collection, details);

			*metadata = Some(CollectionMetadata { deposit, data: data.clone() });

			Self::deposit_event(Event::CollectionMetadataSet { collection, data });
			Ok(())
		})
	}

	/// Clears the metadata for a specific collection.
	///
	/// - `maybe_check_origin`: An optional account ID that is allowed to clear the collection
	///   metadata. If `None`, it's considered the root account.
	/// - `collection`: The ID of the collection for which to clear the metadata.
	///
	/// Emits `CollectionMetadataCleared` event upon successful clearing of the metadata.
	/// Returns `Ok(())` on success, or one of the following dispatch errors:
	/// - `UnknownCollection`: The specified collection does not exist.
	/// - `MetadataNotFound`: The metadata for the collection was not found.
	/// - `LockedCollectionMetadata`: The metadata for the collection is locked and cannot be
	///   modified.
	/// - `NoPermission`: The caller does not have the required permission to clear the metadata.
	pub(crate) fn do_clear_collection_metadata(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
	) -> DispatchResult {
		if let Some(check_origin) = &maybe_check_origin {
			ensure!(
				Self::has_role(&collection, &check_origin, CollectionRole::Admin),
				Error::<T, I>::NoPermission
			);
		}

		let details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		let collection_config = Self::get_collection_config(&collection)?;

		ensure!(
			maybe_check_origin.is_none() ||
				collection_config.is_setting_enabled(CollectionSetting::UnlockedMetadata),
			Error::<T, I>::LockedCollectionMetadata
		);

		CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
			let deposit = metadata.take().ok_or(Error::<T, I>::UnknownCollection)?.deposit;
			T::Currency::unreserve(&details.owner, deposit);
			Self::deposit_event(Event::CollectionMetadataCleared { collection });
			Ok(())
		})
	}

	/// A helper method to construct metadata.
	///
	/// # Errors
	///
	/// This function returns an [`IncorrectMetadata`](crate::Error::IncorrectMetadata) dispatch
	/// error if the provided metadata is too long.
	pub fn construct_metadata(
		metadata: Vec<u8>,
	) -> Result<BoundedVec<u8, T::StringLimit>, DispatchError> {
		Ok(BoundedVec::try_from(metadata).map_err(|_| Error::<T, I>::IncorrectMetadata)?)
	}
}
