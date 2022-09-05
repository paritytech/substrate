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
use frame_support::{
	pallet_prelude::*,
	traits::{Currency, ExistenceRequirement::KeepAlive},
};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_pay_tips(sender: T::AccountId, tips: Vec<ItemTip<T, I>>) -> DispatchResult {
		for tip in tips {
			T::Currency::transfer(&sender, &tip.2, tip.3, KeepAlive)?;
			Self::deposit_event(Event::TipSent {
				collection: tip.0,
				item: tip.1,
				sender: sender.clone(),
				receiver: tip.2,
				amount: tip.3,
			});
		}
		Ok(())
	}

	pub fn do_set_seller(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		sender: T::AccountId,
		seller: T::AccountId,
		price: ItemPrice<T, I>,
		tips: SellerTipsOf<T, I>,
	) -> DispatchResult {
		Item::<T, I>::try_mutate(&collection_id, &item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T, I>::UnknownItem)?;
			ensure!(item.owner == sender, Error::<T, I>::NoPermission);

			item.seller = Some(seller.clone());

			Seller::<T, I>::insert(
				(&seller, &collection_id, &item_id),
				ItemSellData { price, tips: tips.clone() },
			);

			Self::deposit_event(Event::SellerSet {
				collection: collection_id,
				item: item_id,
				seller,
				price,
				tips,
			});

			Ok(())
		})
	}

	pub fn do_remove_seller(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		sender: T::AccountId,
		seller: T::AccountId,
	) -> DispatchResult {
		Item::<T, I>::try_mutate(&collection_id, &item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T, I>::UnknownItem)?;
			ensure!(item.owner == sender, Error::<T, I>::NoPermission);

			let mut is_correct_seller = false;
			if let Some(ref item_seller) = item.seller {
				is_correct_seller = *item_seller == seller;
			}
			ensure!(is_correct_seller, Error::<T, I>::WrongSeller);

			Seller::<T, I>::remove((&seller, &collection_id, &item_id));
			item.seller = None;

			Self::deposit_event(Event::SellerRemoved {
				collection: collection_id,
				item: item_id,
				seller,
			});

			Ok(())
		})
	}

	pub fn do_buy_from_seller(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		buyer: T::AccountId,
		w_seller: T::AccountId,
		w_price: ItemPrice<T, I>,
		w_tips: SellerTipsOf<T, I>,
	) -> DispatchResult {
		let item = Item::<T, I>::get(collection_id, item_id).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(item.owner != buyer, Error::<T, I>::NoPermission);

		let seller = item.seller.ok_or(Error::<T, I>::NotForSale)?;
		ensure!(seller == w_seller, Error::<T, I>::WrongSeller);

		let ItemSellData { price, tips } = Seller::<T, I>::get((seller, collection_id, item_id))
			.ok_or(Error::<T, I>::NotForSale)?;

		ensure!(w_price == price, Error::<T, I>::WrongPrice);
		ensure!(w_tips == tips, Error::<T, I>::WrongTips);

		T::Currency::transfer(&buyer, &item.owner, price.clone(), KeepAlive)?;
		Self::do_pay_tips(buyer.clone(), tips.into())?;

		let old_owner = item.owner.clone();
		Self::do_transfer(collection_id, item_id, buyer.clone(), |_, _| Ok(()))?;

		Self::deposit_event(Event::ItemBought {
			collection: collection_id,
			item: item_id,
			price,
			seller: old_owner,
			buyer,
		});

		Ok(())
	}
}
