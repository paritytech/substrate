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

//! Implementations for `nonfungibles` traits.

use super::*;
use frame_support::{
	ensure,
	storage::KeyPrefixIterator,
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
			let namespace = AttributeNamespace::CollectionOwner;
			let key = BoundedSlice::<_, _>::try_from(key).ok()?;
			Attribute::<T, I>::get((collection, Some(item), namespace, key)).map(|a| a.0.into())
		}
	}

	/// Returns the custom attribute value of `item` of `collection` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn custom_attribute(
		account: &T::AccountId,
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &[u8],
	) -> Option<Vec<u8>> {
		let namespace = Account::<T, I>::get((account, collection, item))
			.map(|_| AttributeNamespace::ItemOwner)
			.unwrap_or_else(|| AttributeNamespace::Account(account.clone()));

		let key = BoundedSlice::<_, _>::try_from(key).ok()?;
		Attribute::<T, I>::get((collection, Some(item), namespace, key)).map(|a| a.0.into())
	}

	/// Returns the system attribute value of `item` of `collection` corresponding to `key`.
	///
	/// By default this is `None`; no attributes are defined.
	fn system_attribute(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &[u8],
	) -> Option<Vec<u8>> {
		let namespace = AttributeNamespace::Pallet;
		let key = BoundedSlice::<_, _>::try_from(key).ok()?;
		Attribute::<T, I>::get((collection, Some(item), namespace, key)).map(|a| a.0.into())
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
			Attribute::<T, I>::get((
				collection,
				Option::<T::ItemId>::None,
				AttributeNamespace::CollectionOwner,
				key,
			))
			.map(|a| a.0.into())
		}
	}

	/// Returns `true` if the `item` of `collection` may be transferred.
	///
	/// Default implementation is that all items are transferable.
	fn can_transfer(collection: &Self::CollectionId, item: &Self::ItemId) -> bool {
		use PalletAttributes::TransferDisabled;
		match Self::has_system_attribute(&collection, &item, TransferDisabled) {
			Ok(transfer_disabled) if transfer_disabled => return false,
			_ => (),
		}
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

impl<T: Config<I>, I: 'static> Create<<T as SystemConfig>::AccountId, CollectionConfigFor<T, I>>
	for Pallet<T, I>
{
	/// Create a `collection` of nonfungible items to be owned by `who` and managed by `admin`.
	fn create_collection(
		who: &T::AccountId,
		admin: &T::AccountId,
		config: &CollectionConfigFor<T, I>,
	) -> Result<T::CollectionId, DispatchError> {
		// DepositRequired can be disabled by calling the force_create() only
		ensure!(
			!config.has_disabled_setting(CollectionSetting::DepositRequired),
			Error::<T, I>::WrongSetting
		);

		let collection =
			NextCollectionId::<T, I>::get().unwrap_or(T::CollectionId::initial_value());

		Self::do_create_collection(
			collection,
			who.clone(),
			admin.clone(),
			*config,
			T::CollectionDeposit::get(),
			Event::Created { collection, creator: who.clone(), owner: admin.clone() },
		)?;
		Ok(collection)
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

impl<T: Config<I>, I: 'static> Mutate<<T as SystemConfig>::AccountId, ItemConfig> for Pallet<T, I> {
	fn mint_into(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		who: &T::AccountId,
		item_config: &ItemConfig,
		deposit_collection_owner: bool,
	) -> DispatchResult {
		Self::do_mint(
			*collection,
			*item,
			match deposit_collection_owner {
				true => None,
				false => Some(who.clone()),
			},
			who.clone(),
			*item_config,
			|_, _| Ok(()),
		)
	}

	fn burn(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		maybe_check_owner: Option<&T::AccountId>,
	) -> DispatchResult {
		Self::do_burn(*collection, *item, |d| {
			if let Some(check_owner) = maybe_check_owner {
				if &d.owner != check_owner {
					return Err(Error::<T, I>::NoPermission.into())
				}
			}
			Ok(())
		})
	}

	fn set_attribute(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &[u8],
		value: &[u8],
	) -> DispatchResult {
		Self::do_force_set_attribute(
			None,
			*collection,
			Some(*item),
			AttributeNamespace::Pallet,
			Self::construct_attribute_key(key.to_vec())?,
			Self::construct_attribute_value(value.to_vec())?,
		)
	}

	fn set_typed_attribute<K: Encode, V: Encode>(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| {
			value.using_encoded(|v| {
				<Self as Mutate<T::AccountId, ItemConfig>>::set_attribute(collection, item, k, v)
			})
		})
	}

	fn set_collection_attribute(
		collection: &Self::CollectionId,
		key: &[u8],
		value: &[u8],
	) -> DispatchResult {
		Self::do_force_set_attribute(
			None,
			*collection,
			None,
			AttributeNamespace::Pallet,
			Self::construct_attribute_key(key.to_vec())?,
			Self::construct_attribute_value(value.to_vec())?,
		)
	}

	fn set_typed_collection_attribute<K: Encode, V: Encode>(
		collection: &Self::CollectionId,
		key: &K,
		value: &V,
	) -> DispatchResult {
		key.using_encoded(|k| {
			value.using_encoded(|v| {
				<Self as Mutate<T::AccountId, ItemConfig>>::set_collection_attribute(
					collection, k, v,
				)
			})
		})
	}

	fn clear_attribute(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &[u8],
	) -> DispatchResult {
		Self::do_clear_attribute(
			None,
			*collection,
			Some(*item),
			AttributeNamespace::Pallet,
			Self::construct_attribute_key(key.to_vec())?,
		)
	}

	fn clear_typed_attribute<K: Encode>(
		collection: &Self::CollectionId,
		item: &Self::ItemId,
		key: &K,
	) -> DispatchResult {
		key.using_encoded(|k| {
			<Self as Mutate<T::AccountId, ItemConfig>>::clear_attribute(collection, item, k)
		})
	}

	fn clear_collection_attribute(collection: &Self::CollectionId, key: &[u8]) -> DispatchResult {
		Self::do_clear_attribute(
			None,
			*collection,
			None,
			AttributeNamespace::Pallet,
			Self::construct_attribute_key(key.to_vec())?,
		)
	}

	fn clear_typed_collection_attribute<K: Encode>(
		collection: &Self::CollectionId,
		key: &K,
	) -> DispatchResult {
		key.using_encoded(|k| {
			<Self as Mutate<T::AccountId, ItemConfig>>::clear_collection_attribute(collection, k)
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

	fn disable_transfer(collection: &Self::CollectionId, item: &Self::ItemId) -> DispatchResult {
		<Self as Mutate<T::AccountId, ItemConfig>>::set_attribute(
			collection,
			item,
			&PalletAttributes::<Self::CollectionId>::TransferDisabled.encode(),
			&[],
		)
	}

	fn enable_transfer(collection: &Self::CollectionId, item: &Self::ItemId) -> DispatchResult {
		<Self as Mutate<T::AccountId, ItemConfig>>::clear_attribute(
			collection,
			item,
			&PalletAttributes::<Self::CollectionId>::TransferDisabled.encode(),
		)
	}
}

impl<T: Config<I>, I: 'static> InspectEnumerable<T::AccountId> for Pallet<T, I> {
	type CollectionsIterator = KeyPrefixIterator<<T as Config<I>>::CollectionId>;
	type ItemsIterator = KeyPrefixIterator<<T as Config<I>>::ItemId>;
	type OwnedIterator =
		KeyPrefixIterator<(<T as Config<I>>::CollectionId, <T as Config<I>>::ItemId)>;
	type OwnedInCollectionIterator = KeyPrefixIterator<<T as Config<I>>::ItemId>;

	/// Returns an iterator of the collections in existence.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn collections() -> Self::CollectionsIterator {
		Collection::<T, I>::iter_keys()
	}

	/// Returns an iterator of the items of a `collection` in existence.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn items(collection: &Self::CollectionId) -> Self::ItemsIterator {
		Item::<T, I>::iter_key_prefix(collection)
	}

	/// Returns an iterator of the items of all collections owned by `who`.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn owned(who: &T::AccountId) -> Self::OwnedIterator {
		Account::<T, I>::iter_key_prefix((who,))
	}

	/// Returns an iterator of the items of `collection` owned by `who`.
	///
	/// NOTE: iterating this list invokes a storage read per item.
	fn owned_in_collection(
		collection: &Self::CollectionId,
		who: &T::AccountId,
	) -> Self::OwnedInCollectionIterator {
		Account::<T, I>::iter_key_prefix((who, collection))
	}
}
