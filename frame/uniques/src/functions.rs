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
	BoundedVec
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
		ensure!(!collection_details.is_frozen, Error::<T, I>::Frozen);
		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::Locked);

		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &item));
		Account::<T, I>::insert((&dest, &collection, &item), ());
		let origin = details.owner;
		details.owner = dest;
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

	pub fn do_create_collection(
		collection: T::CollectionId,
		owner: T::AccountId,
		admin: T::AccountId,
		deposit: DepositBalanceOf<T, I>,
		free_holding: bool,
		event: Event<T, I>,
	) -> DispatchResult {
		ensure!(!Collection::<T, I>::contains_key(collection), Error::<T, I>::InUse);

		T::Currency::reserve(&owner, deposit)?;

		Collection::<T, I>::insert(
			collection,
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

	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		owner: T::AccountId,
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
		let details = Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(details.owner == sender, Error::<T, I>::NoPermission);

		if let Some(ref price) = price {
			ItemPriceOf::<T, I>::insert(
				&collection,
				&item,
				(price.clone(), whitelisted_buyer.clone()),
			);
			Self::deposit_event(Event::ItemPriceSet {
				collection,
				item,
				price: price.clone(),
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

	pub fn do_set_item_metadata(
		collection: T::CollectionId,
		item: T::ItemId,
		data: BoundedVec<u8, T::StringLimit>,
		is_frozen: bool,
		maybe_check_owner: Option<T::AccountId>,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&Option<ItemMetadata<DepositBalanceOf<T, I>, T::StringLimit>>,
		) -> DispatchResult,
	) -> DispatchResult {
		ItemMetadataOf::<T, I>::try_mutate_exists(collection, item, |metadata| {
			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

			with_details(&collection_details, metadata)?;

			if metadata.is_none() {
				collection_details.item_metadatas.saturating_inc();
			}

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			collection_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if !collection_details.free_holding && maybe_check_owner.is_some() {
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}
			if deposit > old_deposit {
				T::Currency::reserve(&collection_details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&collection_details.owner, old_deposit - deposit);
			}
			collection_details.total_deposit.saturating_accrue(deposit);

			*metadata = Some(ItemMetadata { deposit, data: data.clone(), is_frozen });

			Collection::<T, I>::insert(&collection, &collection_details);
			Self::deposit_event(Event::MetadataSet { collection, item, data, is_frozen });
			Ok(())
		})
	}

	pub fn do_set_collection_metadata(
		collection: T::CollectionId,
		data: BoundedVec<u8, T::StringLimit>,
		is_frozen: bool,
		maybe_check_owner: Option<T::AccountId>,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&Option<CollectionMetadata<DepositBalanceOf<T, I>, T::StringLimit>>,
		) -> DispatchResult,
	) -> DispatchResult {
		CollectionMetadataOf::<T, I>::try_mutate_exists(collection, |metadata| {
			let mut collection_details =
				Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

			with_details(&collection_details, metadata)?;

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			collection_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if maybe_check_owner.is_some() && !collection_details.free_holding {
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}
			if deposit > old_deposit {
				T::Currency::reserve(&collection_details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&collection_details.owner, old_deposit - deposit);
			}
			collection_details.total_deposit.saturating_accrue(deposit);

			*metadata = Some(CollectionMetadata { deposit, data: data.clone(), is_frozen });

			Collection::<T, I>::insert(&collection, collection_details);
			Self::deposit_event(Event::CollectionMetadataSet { collection, data, is_frozen });
			Ok(())
		})
	}

	pub fn do_set_attribute(
		collection: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		key: BoundedVec<u8, T::KeyLimit>,
		value: BoundedVec<u8, T::ValueLimit>,
	) -> DispatchResult {
		// If collection exists, update collection metadata and set/update attribute
		Collection::<T, I>::mutate_exists(collection, |opt_collection_details| {
			match opt_collection_details {
				Some(collection_details) => {
					let attribute = Attribute::<T, I>::get((collection, maybe_item, &key));
					// If the collection does not have an attribute for the given key, increase the
					// counter of the number of attributes
					if attribute.is_none() {
						collection_details.attributes.saturating_inc();
					}

					let deposit = Attribute::<T, I>::get((collection, maybe_item, &key))
						.map_or(Zero::zero(), |m| m.1);
					//Set attribute value
					Attribute::<T, I>::insert((&collection, maybe_item, &key), (&value, deposit));
					Ok(())
				},
				None => Err(Error::<T, I>::UnknownCollection),
			}
		})?;
		Ok(())
	}
}
