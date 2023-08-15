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

//! Various pieces of common functionality.

use super::*;
use frame_support::{
	ensure,
	traits::{ExistenceRequirement, Get},
};
use sp_runtime::{DispatchError, DispatchResult};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Perform a transfer of an item from one account to another within a collection.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - The collection or item does not exist
	///   ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The collection is frozen, and no transfers are allowed ([`Frozen`](crate::Error::Frozen)).
	/// - The item is locked, and transfers are not permitted ([`Locked`](crate::Error::Locked)).
	/// - The `with_details` closure returns an error.
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
		ensure!(!collection_details.is_frozen, Error::<T, I>::Frozen);
		ensure!(!T::Locker::is_locked(collection.clone(), item), Error::<T, I>::Locked);

		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &item));
		Account::<T, I>::insert((&dest, &collection, &item), ());
		let origin = details.owner;
		details.owner = dest;

		// The approved account has to be reset to `None`, because otherwise pre-approve attack
		// would be possible, where the owner can approve their second account before making the
		// transaction and then claiming the item back.
		details.approved = None;

		Item::<T, I>::insert(&collection, &item, &details);
		ItemPriceOf::<T, I>::remove(&collection, &item);

		Self::deposit_event(Event::Transferred {
			collection,
			item,
			from: origin,
			to: details.owner,
		});
		Ok(())
	}

	/// Create a new collection with the provided details.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - If the collection ID is already in use ([`InUse`](crate::Error::InUse)).
	/// - If reserving the deposit fails (e.g., insufficient funds).
	pub fn do_create_collection(
		collection: T::CollectionId,
		owner: T::AccountId,
		admin: T::AccountId,
		deposit: DepositBalanceOf<T, I>,
		free_holding: bool,
		event: Event<T, I>,
	) -> DispatchResult {
		ensure!(!Collection::<T, I>::contains_key(collection.clone()), Error::<T, I>::InUse);

		T::Currency::reserve(&owner, deposit)?;

		Collection::<T, I>::insert(
			collection.clone(),
			CollectionDetails {
				owner: owner.clone(),
				issuer: admin.clone(),
				admin: admin.clone(),
				freezer: admin,
				total_deposit: deposit,
				free_holding,
				items: 0,
				item_metadatas: 0,
				attributes: 0,
				is_frozen: false,
			},
		);

		CollectionAccount::<T, I>::insert(&owner, &collection, ());
		Self::deposit_event(event);
		Ok(())
	}

	/// Destroy a collection along with its associated items and metadata.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - The collection does not exist ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The provided witness does not match the actual counts
	///   ([`BadWitness`](crate::Error::BadWitness)).
	/// - The caller is not the owner of the collection
	///   ([`NoPermission`](crate::Error::NoPermission)).
	pub fn do_destroy_collection(
		collection: T::CollectionId,
		witness: DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<DestroyWitness, DispatchError> {
		Collection::<T, I>::try_mutate_exists(collection.clone(), |maybe_details| {
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
			CollectionMetadataOf::<T, I>::remove(&collection);
			#[allow(deprecated)]
			Attribute::<T, I>::remove_prefix((&collection,), None);
			CollectionAccount::<T, I>::remove(&collection_details.owner, &collection);
			T::Currency::unreserve(&collection_details.owner, collection_details.total_deposit);
			CollectionMaxSupply::<T, I>::remove(&collection);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				items: collection_details.items,
				item_metadatas: collection_details.item_metadatas,
				attributes: collection_details.attributes,
			})
		})
	}

	/// Mint (create) a new item within a collection and assign ownership to an account.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - The item already exists in the collection
	///   ([`AlreadyExists`](crate::Error::AlreadyExists)).
	/// - The collection does not exist ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The provided closure `with_details` returns an error.
	/// - The collection has reached its maximum supply
	///   ([`MaxSupplyReached`](crate::Error::MaxSupplyReached)).
	/// - An arithmetic overflow occurs when incrementing the number of items in the collection.
	/// - The currency reserve operation for the item deposit fails for any reason.
	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		owner: T::AccountId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(
			!Item::<T, I>::contains_key(collection.clone(), item),
			Error::<T, I>::AlreadyExists
		);

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

				let deposit = match collection_details.free_holding {
					true => Zero::zero(),
					false => T::ItemDeposit::get(),
				};
				T::Currency::reserve(&collection_details.owner, deposit)?;
				collection_details.total_deposit += deposit;

				let owner = owner.clone();
				Account::<T, I>::insert((&owner, &collection, &item), ());
				let details = ItemDetails { owner, approved: None, is_frozen: false, deposit };
				Item::<T, I>::insert(&collection, &item, details);
				Ok(())
			},
		)?;

		Self::deposit_event(Event::Issued { collection, item, owner });
		Ok(())
	}

	/// Burn (destroy) an item from a collection.
	///
	/// # Errors
	/// This function returns a `Dispatch` error in the following cases:
	/// - The item is locked and burns are not permitted ([`Locked`](crate::Error::Locked)).
	/// - The collection or item does not exist
	///   ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The `with_details` closure returns an error.
	pub fn do_burn(
		collection: T::CollectionId,
		item: T::ItemId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>, &ItemDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!T::Locker::is_locked(collection.clone(), item), Error::<T, I>::Locked);
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

		Self::deposit_event(Event::Burned { collection, item, owner });
		Ok(())
	}

	/// Set or remove the price for an item in a collection.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - The item or collection does not exist ([`UnknownItem`](crate::Error::UnknownItem) or
	///   [`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The sender is not the owner of the item ([`NoPermission`](crate::Error::NoPermission)).
	pub fn do_set_price(
		collection: T::CollectionId,
		item: T::ItemId,
		sender: T::AccountId,
		price: Option<ItemPrice<T, I>>,
		whitelisted_buyer: Option<T::AccountId>,
	) -> DispatchResult {
		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(details.owner == sender, Error::<T, I>::NoPermission);

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

	/// Buy an item from a collection.
	///
	/// # Errors
	/// This function returns a dispatch error in the following cases:
	/// - The item or collection does not exist ([`UnknownItem`](crate::Error::UnknownItem) or
	///   [`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - The buyer is the current owner of the item ([`NoPermission`](crate::Error::NoPermission)).
	/// - The item is not for sale ([`NotForSale`](crate::Error::NotForSale)).
	/// - The bid price is lower than the item's sale price
	///   ([`BidTooLow`](crate::Error::BidTooLow)).
	/// - The item is set to be sold only to a specific buyer, and the provided buyer is not the
	///   whitelisted buyer ([`NoPermission`](crate::Error::NoPermission)).
	/// - The currency transfer between the buyer and the owner fails for any reason.
	pub fn do_buy_item(
		collection: T::CollectionId,
		item: T::ItemId,
		buyer: T::AccountId,
		bid_price: ItemPrice<T, I>,
	) -> DispatchResult {
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

		Self::do_transfer(collection.clone(), item, buyer.clone(), |_, _| Ok(()))?;

		Self::deposit_event(Event::ItemBought {
			collection,
			item,
			price: price_info.0,
			seller: old_owner,
			buyer,
		});

		Ok(())
	}
}
