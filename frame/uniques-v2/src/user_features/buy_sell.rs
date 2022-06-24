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
use sp_runtime::traits::Saturating;

impl<T: Config> Pallet<T> {
	pub fn do_set_price(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		caller: T::AccountId,
		price: Option<BalanceOf<T>>,
		buyer: Option<T::AccountId>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			// Set the price
			item.price = price.clone();
			item.buyer = buyer.clone();

			Self::deposit_event(Event::ItemPriceSet { collection_id, item_id, price, buyer });

			Ok(())
		})
	}

	pub fn do_buy_item(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		buyer: T::AccountId,
		bid_price: BalanceOf<T>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemNotForSale
		);

		let item = Items::<T>::get(collection_id, item_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(item.owner != buyer, Error::<T>::NotAuthorized);

		let item_price = item.price.ok_or(Error::<T>::ItemNotForSale)?;
		ensure!(bid_price >= item_price, Error::<T>::BidTooLow);

		if let Some(only_buyer) = item.buyer {
			ensure!(only_buyer == buyer, Error::<T>::ItemNotForSale);
		}

		T::Currency::transfer(&buyer, &item.owner, item_price.clone(), KeepAlive)?;

		let old_owner = item.owner.clone();

		Self::do_transfer_item(collection_id, item_id, config, item.owner.clone(), buyer.clone())?;

		Self::deposit_event(Event::ItemBought {
			collection_id,
			item_id,
			price: item_price,
			seller: old_owner,
			buyer,
		});

		Ok(())
	}

	pub fn do_set_seller(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		caller: T::AccountId,
		seller: Option<T::AccountId>,
		price: Option<BalanceOf<T>>,
		seller_tips: Option<BalanceOf<T>>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			if let Some(ref current_seller) = item.seller {
				Sellers::<T>::remove((&current_seller, &collection_id, &item_id));
			}

			item.seller = None;

			if let Some(ref seller) = seller {
				if let Some(price) = price {
					item.seller = Some(seller.clone());

					Sellers::<T>::insert(
						(seller, &collection_id, &item_id),
						ItemSellData { seller_price: price, seller_tips },
					);
				}
			}

			Self::deposit_event(Event::ItemSellerSet {
				collection_id,
				item_id,
				seller,
				price,
				seller_tips,
			});

			Ok(())
		})
	}

	pub fn do_buy_from_seller(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		buyer: T::AccountId,
		seller: T::AccountId,
		amount: BalanceOf<T>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		let item = Items::<T>::get(collection_id, item_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(item.owner != buyer, Error::<T>::NotAuthorized);

		let seller_account = item.seller.ok_or(Error::<T>::ItemNotForSale)?;
		ensure!(seller_account == seller, Error::<T>::WrongSeller);

		let ItemSellData { seller_price, seller_tips } =
			Sellers::<T>::get((seller_account, collection_id, item_id))
				.ok_or(Error::<T>::SellDataNotFound)?;

		let total = seller_price.saturating_add(seller_tips.unwrap_or(Default::default()));
		ensure!(amount >= total, Error::<T>::AmountTooLow);

		if let Some(seller_tips) = seller_tips {
			T::Currency::transfer(&buyer, &seller, seller_tips, KeepAlive)?;
		}

		T::Currency::transfer(&buyer, &item.owner, seller_price.clone(), KeepAlive)?;

		Self::do_transfer_item(collection_id, item_id, config, item.owner.clone(), buyer.clone())?;

		Self::deposit_event(Event::ItemSold {
			collection_id,
			item_id,
			buyer,
			seller,
			price: seller_price,
			seller_tips,
		});

		Ok(())
	}

	// user 1 signed an offer to buy user's 2 item
	// user 2 executes that offer
	pub fn do_accept_buy_offer(
		caller: T::AccountId,           // user 2
		collection_id: T::CollectionId, // user's 2 item
		item_id: T::ItemId,             // user's 2 item
		config: CollectionConfig,
		buyer: T::AccountId, // user 1
		receiver: T::AccountId,
		item_owner: T::AccountId, // user 2
		bid_price: BalanceOf<T>,
		deadline: Option<T::BlockNumber>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemNotForSale
		);

		let item = Items::<T>::get(collection_id, item_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(item.owner == item_owner && caller == item.owner, Error::<T>::NotAuthorized);

		if let Some(deadline) = deadline {
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::AuthorizationExpired);
		}

		T::Currency::transfer(&buyer, &item.owner, bid_price.clone(), KeepAlive)?;

		let old_owner = item.owner.clone();

		Self::do_transfer_item(
			collection_id,
			item_id,
			config,
			item.owner.clone(),
			receiver.clone(),
		)?;

		Self::deposit_event(Event::BuyOfferAccepted {
			collection_id,
			item_id,
			price: bid_price,
			seller: old_owner,
			buyer,
			receiver,
			deadline,
		});

		Ok(())
	}

	// user 1 signed an offer to swap his item to user's 2 item by paying some price
	// `collection_from_id/`item_from_id` would refer to user 1
	// user 2 executes that offer
	// user 2 will pay the `price` (if specified), send his `to_item` and get the `from_item`
	pub fn do_swap_items(
		caller: T::AccountId,                // user 2
		collection_from_id: T::CollectionId, // user's 1 item
		item_from_id: T::ItemId,             // user's 1 item
		collection_to_id: T::CollectionId,   // user's 2 item
		item_to_id: T::ItemId,               // user's 2 item
		config_from: CollectionConfig,
		config_to: CollectionConfig,
		signer_account: T::AccountId, // user 1
		item_from_receiver: T::AccountId,
		item_to_owner: T::AccountId, // user 2
		price: Option<BalanceOf<T>>,
		deadline: Option<T::BlockNumber>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config_from.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemNotForSale
		);
		let user_features: BitFlags<UserFeature> = config_to.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemNotForSale
		);

		let from_item =
			Items::<T>::get(collection_from_id, item_from_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(signer_account == from_item.owner, Error::<T>::NotAuthorized);

		let to_item =
			Items::<T>::get(collection_to_id, item_to_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(
			to_item.owner == item_to_owner && caller == to_item.owner,
			Error::<T>::NotAuthorized
		);

		if let Some(deadline) = deadline {
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T>::AuthorizationExpired);
		}

		if let Some(price) = price {
			T::Currency::transfer(&caller, &from_item.owner, price, KeepAlive)?;
		}

		Self::do_transfer_item(
			collection_to_id,
			item_to_id,
			config_to,
			to_item.owner.clone(),
			signer_account.clone(),
		)?;

		Self::do_transfer_item(
			collection_from_id,
			item_from_id,
			config_from,
			signer_account.clone(),
			item_from_receiver.clone(),
		)?;

		Self::deposit_event(Event::ItemsSwapExecuted {
			collection_from_id,
			collection_to_id,
			item_from_id,
			item_to_id,
			executed_by: caller,
			new_item_from_owner: item_from_receiver,
			new_item_to_owner: signer_account,
			price,
			deadline,
		});

		Ok(())
	}
}
