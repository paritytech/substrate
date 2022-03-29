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
use sp_runtime::{ArithmeticError};

impl<T: Config> Pallet<T> {
	pub fn do_mint_item(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&collection_id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);
		ensure!(!Items::<T>::contains_key(collection_id, item_id), Error::<T>::ItemIdTaken);

		if collection.max_supply.is_some() {
			ensure!(collection.items < collection.max_supply.unwrap(), Error::<T>::ItemIdNotWithinMaxSupply);
		}

		let item = Item {
			id: item_id,
			owner: caller.clone(),
			deposit: None,
		};

		let instances =
			collection.items.checked_add(1).ok_or(ArithmeticError::Overflow)?;
		collection.items = instances;

		Items::<T>::insert(collection_id, item_id, item);

		Self::deposit_event(Event::<T>::ItemCreated { collection_id, item_id });

		Ok(())
	}
}
