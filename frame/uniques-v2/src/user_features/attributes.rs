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
use sp_runtime::traits::Saturating;

impl<T: Config> Pallet<T> {
	pub fn do_set_attributes(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		key: AttributeKeyOf<T>,
		value: AttributeValueOf<T>,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&collection_id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		let attribute = Attributes::<T>::get((collection_id, maybe_item, &key));
		if attribute.is_none() {
			collection.attributes.saturating_inc();
		}

		Attributes::<T>::insert((&collection_id, maybe_item, &key), &value);
		Collections::<T>::insert(collection_id, &collection);
		Self::deposit_event(Event::AttributeSet { id: collection_id, maybe_item, key, value });
		Ok(())
	}

	pub fn do_clear_attribute(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		maybe_item: Option<T::ItemId>,
		key: AttributeKeyOf<T>,
	) -> DispatchResult {
		let mut collection = Collections::<T>::get(&collection_id).ok_or(Error::<T>::CollectionNotFound)?;
		ensure!(collection.owner == caller, Error::<T>::NotAuthorized);

		if let Some(_) = Attributes::<T>::take((collection_id, maybe_item, &key)) {
			collection.attributes.saturating_dec();
			Collections::<T>::insert(collection_id, &collection);
			Self::deposit_event(Event::AttributeCleared { id: collection_id, maybe_item, key });
		}

		Ok(())
	}
}
