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
use frame_support::pallet_prelude::*;
use sp_runtime::ArithmeticError;

impl<T: Config> Pallet<T> {
	pub fn do_mint_item(
		caller: T::AccountId,
		owner: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
	) -> DispatchResult {
		ensure!(!Items::<T>::contains_key(collection_id, item_id), Error::<T>::ItemIdTaken);

		Collections::<T>::try_mutate(&collection_id, |maybe_collection| -> DispatchResult {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

			if let Some(max_supply) = collection.max_supply {
				ensure!(collection.items < max_supply, Error::<T>::AllItemsMinted);
			}

			let item = Item {
				id: item_id,
				owner: owner.clone(),
				deposit: None,
				price: None,
				buyer: None,
				approvals: Default::default(),
				seller: None,
			};

			let items = collection.items.checked_add(1).ok_or(ArithmeticError::Overflow)?;
			collection.items = items;

			Items::<T>::insert(collection_id, item_id, item);
			AccountItems::<T>::insert((&owner, &collection_id, &item_id), ());

			Self::deposit_event(Event::<T>::ItemCreated { collection_id, item_id });

			Ok(())
		})
	}

	pub fn do_burn_item(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
	) -> DispatchResult {
		ensure!(Items::<T>::contains_key(collection_id, item_id), Error::<T>::ItemNotFound);

		Collections::<T>::try_mutate(&collection_id, |maybe_collection| -> DispatchResult {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			let item = Items::<T>::get(collection_id, item_id).ok_or(Error::<T>::ItemNotFound)?;

			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			let items = collection.items.checked_sub(1).ok_or(ArithmeticError::Overflow)?;
			collection.items = items;

			if let Some(seller) = item.seller {
				Sellers::<T>::remove((&seller, &collection_id, &item_id));
			}

			Items::<T>::remove(&collection_id, &item_id);
			ItemMetadataOf::<T>::remove(&collection_id, &item_id);
			AccountItems::<T>::remove((&caller, &collection_id, &item_id));

			// TODO: shall we remove attributes as well?

			Self::deposit_event(Event::<T>::ItemBurned { collection_id, item_id });

			Ok(())
		})
	}
}
