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

//! Various pieces of common functionality.

use super::*;
use frame_support::{
	ensure,
	traits::{ExistenceRequirement, Get},
};
use sp_runtime::{DispatchError, DispatchResult};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_transfer(
		collection: T::CollectionId,
		item: T::ItemId,
		dest: T::AccountId,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&mut ItemDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::ItemLocked);

		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
			Error::<T, I>::ItemsNotTransferable
		);

		let item_config = Self::get_item_config(&collection, &item)?;
		ensure!(
			item_config.is_setting_enabled(ItemSetting::Transferable),
			Error::<T, I>::ItemLocked
		);

		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &item));
		Account::<T, I>::insert((&dest, &collection, &item), ());
		let origin = details.owner;
		details.owner = dest;

		// The approved accounts have to be reset to None, because otherwise pre-approve attack
		// would be possible, where the owner can approve his second account before making the
		// transaction and then claiming the item back.
		details.approvals.clear();

		Item::<T, I>::insert(&collection, &item, &details);
		ItemPriceOf::<T, I>::remove(&collection, &item);
		PendingSwapOf::<T, I>::remove(&collection, &item);

		Self::deposit_event(Event::Transferred {
			collection,
			item,
			from: origin,
			to: details.owner,
		});
		Ok(())
	}

	pub fn do_create_collection(
		collection: T::CollectionId,
		owner: T::AccountId,
		admin: T::AccountId,
		config: CollectionConfig,
		deposit: DepositBalanceOf<T, I>,
		event: Event<T, I>,
	) -> DispatchResult {
		ensure!(!Collection::<T, I>::contains_key(collection), Error::<T, I>::CollectionIdInUse);

		T::Currency::reserve(&owner, deposit)?;

		Collection::<T, I>::insert(
			collection,
			CollectionDetails {
				owner: owner.clone(),
				issuer: admin.clone(),
				admin: admin.clone(),
				freezer: admin,
				total_deposit: deposit,
				items: 0,
				item_metadatas: 0,
				attributes: 0,
			},
		);

		let next_id = collection.increment();

		CollectionConfigOf::<T, I>::insert(&collection, config);
		CollectionAccount::<T, I>::insert(&owner, &collection, ());
		NextCollectionId::<T, I>::set(Some(next_id));

		Self::deposit_event(Event::NextCollectionIdIncremented { next_id });
		Self::deposit_event(event);
		Ok(())
	}

	pub fn do_destroy_collection(
		collection: T::CollectionId,
		witness: DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<DestroyWitness, DispatchError> {
		Collection::<T, I>::try_mutate_exists(collection, |maybe_details| {
			let collection_details =
				maybe_details.take().ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = maybe_check_owner {
				ensure!(collection_details.owner == check_owner, Error::<T, I>::NoPermission);
			}
			ensure!(collection_details.items == witness.items, Error::<T, I>::BadWitness);
			ensure!(
				collection_details.item_metadatas == witness.item_metadatas,
				Error::<T, I>::BadWitness
			);
			ensure!(collection_details.attributes == witness.attributes, Error::<T, I>::BadWitness);

			for (item, details) in Item::<T, I>::drain_prefix(&collection) {
				Account::<T, I>::remove((&details.owner, &collection, &item));
			}
			#[allow(deprecated)]
			ItemMetadataOf::<T, I>::remove_prefix(&collection, None);
			#[allow(deprecated)]
			ItemPriceOf::<T, I>::remove_prefix(&collection, None);
			#[allow(deprecated)]
			PendingSwapOf::<T, I>::remove_prefix(&collection, None);
			CollectionMetadataOf::<T, I>::remove(&collection);
			#[allow(deprecated)]
			Attribute::<T, I>::remove_prefix((&collection,), None);
			CollectionAccount::<T, I>::remove(&collection_details.owner, &collection);
			T::Currency::unreserve(&collection_details.owner, collection_details.total_deposit);
			CollectionMaxSupply::<T, I>::remove(&collection);
			CollectionConfigOf::<T, I>::remove(&collection);
			#[allow(deprecated)]
			ItemConfigOf::<T, I>::remove_prefix(&collection, None);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				items: collection_details.items,
				item_metadatas: collection_details.item_metadatas,
				attributes: collection_details.attributes,
			})
		})
	}

	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		owner: T::AccountId,
		config: ItemConfig,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!Item::<T, I>::contains_key(collection, item), Error::<T, I>::AlreadyExists);

		Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> DispatchResult {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;

				with_details(collection_details)?;

				if let Ok(max_supply) = CollectionMaxSupply::<T, I>::try_get(&collection) {
					ensure!(collection_details.items < max_supply, Error::<T, I>::MaxSupplyReached);
				}

				let items =
					collection_details.items.checked_add(1).ok_or(ArithmeticError::Overflow)?;
				collection_details.items = items;

				let collection_config = Self::get_collection_config(&collection)?;
				let deposit = match collection_config
					.is_setting_enabled(CollectionSetting::DepositRequired)
				{
					true => T::ItemDeposit::get(),
					false => Zero::zero(),
				};
				T::Currency::reserve(&collection_details.owner, deposit)?;
				collection_details.total_deposit += deposit;

				let owner = owner.clone();
				Account::<T, I>::insert((&owner, &collection, &item), ());

				if let Ok(existing_config) = ItemConfigOf::<T, I>::try_get(&collection, &item) {
					ensure!(existing_config == config, Error::<T, I>::InconsistentItemConfig);
				} else {
					ItemConfigOf::<T, I>::insert(&collection, &item, config);
				}

				let details =
					ItemDetails { owner, approvals: ApprovalsOf::<T, I>::default(), deposit };
				Item::<T, I>::insert(&collection, &item, details);
				Ok(())
			},
		)?;

		Self::deposit_event(Event::Issued { collection, item, owner });
		Ok(())
	}

	pub fn do_burn(
		collection: T::CollectionId,
		item: T::ItemId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>, &ItemDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		let owner = Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> Result<T::AccountId, DispatchError> {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				let details = Item::<T, I>::get(&collection, &item)
					.ok_or(Error::<T, I>::UnknownCollection)?;
				with_details(collection_details, &details)?;

				// Return the deposit.
				T::Currency::unreserve(&collection_details.owner, details.deposit);
				collection_details.total_deposit.saturating_reduce(details.deposit);
				collection_details.items.saturating_dec();
				Ok(details.owner)
			},
		)?;

		Item::<T, I>::remove(&collection, &item);
		Account::<T, I>::remove((&owner, &collection, &item));
		ItemPriceOf::<T, I>::remove(&collection, &item);
		PendingSwapOf::<T, I>::remove(&collection, &item);

		// NOTE: if item's settings are not empty (e.g. item's metadata is locked)
		// then we keep the record and don't remove it
		let config = Self::get_item_config(&collection, &item)?;
		if !config.has_disabled_settings() {
			ItemConfigOf::<T, I>::remove(&collection, &item);
		}

		Self::deposit_event(Event::Burned { collection, item, owner });
		Ok(())
	}

	pub fn do_set_price(
		collection: T::CollectionId,
		item: T::ItemId,
		sender: T::AccountId,
		price: Option<ItemPrice<T, I>>,
		whitelisted_buyer: Option<T::AccountId>,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Trading),
			Error::<T, I>::MethodDisabled
		);

		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(details.owner == sender, Error::<T, I>::NoPermission);

		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
			Error::<T, I>::ItemsNotTransferable
		);

		let item_config = Self::get_item_config(&collection, &item)?;
		ensure!(
			item_config.is_setting_enabled(ItemSetting::Transferable),
			Error::<T, I>::ItemLocked
		);

		if let Some(ref price) = price {
			ItemPriceOf::<T, I>::insert(&collection, &item, (price, whitelisted_buyer.clone()));
			Self::deposit_event(Event::ItemPriceSet {
				collection,
				item,
				price: *price,
				whitelisted_buyer,
			});
		} else {
			ItemPriceOf::<T, I>::remove(&collection, &item);
			Self::deposit_event(Event::ItemPriceRemoved { collection, item });
		}

		Ok(())
	}

	pub fn do_buy_item(
		collection: T::CollectionId,
		item: T::ItemId,
		buyer: T::AccountId,
		bid_price: ItemPrice<T, I>,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Trading),
			Error::<T, I>::MethodDisabled
		);

		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(details.owner != buyer, Error::<T, I>::NoPermission);

		let price_info =
			ItemPriceOf::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::NotForSale)?;

		ensure!(bid_price >= price_info.0, Error::<T, I>::BidTooLow);

		if let Some(only_buyer) = price_info.1 {
			ensure!(only_buyer == buyer, Error::<T, I>::NoPermission);
		}

		T::Currency::transfer(
			&buyer,
			&details.owner,
			price_info.0,
			ExistenceRequirement::KeepAlive,
		)?;

		let old_owner = details.owner.clone();

		Self::do_transfer(collection, item, buyer.clone(), |_, _| Ok(()))?;

		Self::deposit_event(Event::ItemBought {
			collection,
			item,
			price: price_info.0,
			seller: old_owner,
			buyer,
		});

		Ok(())
	}

	#[cfg(any(test, feature = "runtime-benchmarks"))]
	pub fn set_next_id(id: T::CollectionId) {
		NextCollectionId::<T, I>::set(Some(id));
	}

	#[cfg(test)]
	pub fn get_next_id() -> T::CollectionId {
		NextCollectionId::<T, I>::get().unwrap_or(T::CollectionId::initial_value())
	}
}
