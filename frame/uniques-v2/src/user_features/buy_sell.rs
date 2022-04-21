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
use frame_support::{pallet_prelude::*, traits::Currency};

impl<T: Config> Pallet<T> {
	pub fn do_set_price(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		caller: T::AccountId,
		price: Option<BalanceOf<T>>,
		buyer: Option<T::AccountId>,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();
		ensure!(
			!user_features.contains(UserFeatures::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			// Set the price
			item.price = price;
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
		let user_features: BitFlags<UserFeatures> = config.user_features.into();
		ensure!(
			!user_features.contains(UserFeatures::NonTransferableItems),
			Error::<T>::ItemNotForSale
		);

		let item = Items::<T>::get(collection_id, item_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(item.owner != buyer, Error::<T>::NotAuthorized);

		if let Some(price) = item.price {
			ensure!(bid_price >= price, Error::<T>::ItemUnderpriced);
		} else {
			return Err(Error::<T>::ItemNotForSale.into())
		}

		if let Some(only_buyer) = item.buyer {
			ensure!(only_buyer == buyer, Error::<T>::ItemNotForSale);
		}

		T::Currency::transfer(
			&buyer,
			&item.owner,
			bid_price,
			frame_support::traits::ExistenceRequirement::KeepAlive,
		)?;

		let old_owner = item.owner.clone();

		Self::do_transfer_item(collection_id, item_id, config, item.owner.clone(), buyer.clone())?;

		// reset the price & the buyer
		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;

			item.price = None;
			item.buyer = None;

			Self::deposit_event(Event::ItemBought {
				collection_id,
				item_id,
				price: bid_price,
				seller: old_owner,
				buyer,
			});

			Ok(())
		})
	}

	pub fn do_accept_buy_offer(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		buyer: T::AccountId,
		receiver: T::AccountId,
		item_owner: T::AccountId,
		bid_price: BalanceOf<T>,
		deadline: Option<T::BlockNumber>,
	) -> DispatchResult {
		// dbg!(&buyer);
		dbg!(&receiver);
		/*
		 * Validate:
		 * 1
		 * 2
		 * 3
		 * 4
		 */
		Ok(())
	}
}
