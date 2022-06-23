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
	pub fn do_transfer_item(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		sender: T::AccountId,
		receiver: T::AccountId,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;

			// approvals
			if item.owner != sender {
				if let Some(deadline) = item.approvals.get(&sender) {
					if let Some(deadline) = deadline {
						let now = frame_system::Pallet::<T>::block_number();
						ensure!(deadline >= &now, Error::<T>::AuthorizationExpired);
					}
				} else {
					return Err(Error::<T>::NotAuthorized.into())
				}
			}

			if item.owner == receiver {
				return Ok(())
			}

			AccountItems::<T>::remove((&item.owner, &collection_id, &item_id));
			AccountItems::<T>::insert((&receiver, &collection_id, &item_id), ());

			item.owner = receiver.clone();
			item.approvals = Default::default();
			item.price = None;
			item.buyer = None;

			if let Some(ref seller) = item.seller.clone() {
				item.seller = None;
				Sellers::<T>::remove((seller, &collection_id, &item_id));
			}

			Self::deposit_event(Event::ItemTransferred {
				collection_id,
				item_id,
				sender,
				receiver,
			});

			Ok(())
		})
	}

	pub fn do_transfer_collection_ownership(
		id: T::CollectionId,
		caller: T::AccountId,
		new_owner: T::AccountId,
	) -> DispatchResult {
		Collections::<T>::try_mutate(id, |maybe_collection| {
			let collection = maybe_collection.as_mut().ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(&caller == &collection.owner, Error::<T>::NotAuthorized);

			if collection.owner == new_owner {
				return Ok(())
			}

			CollectionOwner::<T>::remove(&collection.owner, &id);
			CollectionOwner::<T>::insert(&new_owner, &id, ());
			collection.owner = new_owner.clone();

			Self::deposit_event(Event::CollectionOwnerChanged { id, old_owner: caller, new_owner });
			Ok(())
		})
	}
}
