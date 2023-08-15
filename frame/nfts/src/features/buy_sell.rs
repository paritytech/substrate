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

//! This module contains helper functions to perform the buy and sell functionalities of the NFTs
//! pallet.
//! The bitflag [`PalletFeature::Trading`] needs to be set in the [`Config::Features`] for NFTs
//! to have the functionality defined in this module.

use crate::*;
use frame_support::{
	pallet_prelude::*,
	traits::{Currency, ExistenceRequirement, ExistenceRequirement::KeepAlive},
};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Pays the specified tips to the corresponding receivers.
	///
	/// This function is used to pay tips from the `sender` account to multiple receivers. The tips
	/// are specified as a `BoundedVec` of `ItemTipOf` with a maximum length of `T::MaxTips`. For
	/// each tip, the function transfers the `amount` to the `receiver` account. The sender is
	/// responsible for ensuring the validity of the provided tips.
	///
	/// - `sender`: The account that pays the tips.
	/// - `tips`: A `BoundedVec` containing the tips to be paid, where each tip contains the
	///   `collection`, `item`, `receiver`, and `amount`.
	pub(crate) fn do_pay_tips(
		sender: T::AccountId,
		tips: BoundedVec<ItemTipOf<T, I>, T::MaxTips>,
	) -> DispatchResult {
		for tip in tips {
			let ItemTip { collection, item, receiver, amount } = tip;
			T::Currency::transfer(&sender, &receiver, amount, KeepAlive)?;
			Self::deposit_event(Event::TipSent {
				collection,
				item,
				sender: sender.clone(),
				receiver,
				amount,
			});
		}
		Ok(())
	}

	/// Sets the price and whitelists a buyer for an item in the specified collection.
	///
	/// This function is used to set the price and whitelist a buyer for an item in the
	/// specified `collection`. The `sender` account must be the owner of the item. The item's price
	/// and the whitelisted buyer can be set to allow trading the item. If `price` is `None`, the
	/// item will be marked as not for sale.
	///
	/// - `collection`: The identifier of the collection containing the item.
	/// - `item`: The identifier of the item for which the price and whitelist information will be
	///   set.
	/// - `sender`: The account that sets the price and whitelist information for the item.
	/// - `price`: The optional price for the item.
	/// - `whitelisted_buyer`: The optional account that is whitelisted to buy the item at the set
	///   price.
	pub(crate) fn do_set_price(
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
			Error::<T, I>::ItemsNonTransferable
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

	/// Buys the specified item from the collection.
	///
	/// This function is used to buy an item from the specified `collection`. The `buyer` account
	/// will attempt to buy the item with the provided `bid_price`. The item's current owner will
	/// receive the bid price if it is equal to or higher than the item's set price. If
	/// `whitelisted_buyer` is specified in the item's price information, only that account is
	/// allowed to buy the item. If the item is not for sale, or the bid price is too low, the
	/// function will return an error.
	///
	/// - `collection`: The identifier of the collection containing the item to be bought.
	/// - `item`: The identifier of the item to be bought.
	/// - `buyer`: The account that attempts to buy the item.
	/// - `bid_price`: The bid price offered by the buyer for the item.
	pub(crate) fn do_buy_item(
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
}
