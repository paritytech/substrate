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
use frame_support::pallet_prelude::*;

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
		ensure!(!user_features.contains(UserFeatures::NonTransferableItems), Error::<T>::ItemsNotTransferable);

		let mut item = Items::<T>::get(&collection_id, &item_id).ok_or(Error::<T>::ItemNotFound)?;
		ensure!(item.owner == caller, Error::<T>::NotAuthorized);

		// Set the price
		item.price = price;
		item.buyer = buyer.clone();

		Self::deposit_event(Event::ItemPriceSet { collection_id, item_id, price, buyer });

		Ok(())
	}
}
