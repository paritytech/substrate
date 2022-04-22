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
use sp_runtime::ArithmeticError;

impl<T: Config> Pallet<T> {
	pub fn do_transfer_item(
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		config: CollectionConfig,
		sender: T::AccountId,
		receiver: T::AccountId,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeatures> = config.user_features.into();
		ensure!(
			!user_features.contains(UserFeatures::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;

			let collection =
				Collections::<T>::get(collection_id).ok_or(Error::<T>::CollectionNotFound)?;

			// approvals
			if item.owner != sender {
				if let Some((_, deadline)) = item.approvals.get_key_value(&sender) {
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

			if user_features.contains(UserFeatures::Royalty) {
				// take a part of the transfer amount
			}

			// max items per user
			let mut maybe_receiver_items_amount =
				CountForAccountItems::<T>::get(&receiver, &collection_id);
			let receiver_items_amount = maybe_receiver_items_amount.get_or_insert(0);

			let sender_items_amount = CountForAccountItems::<T>::get(&item.owner, &collection_id)
				.ok_or(Error::<T>::ItemNotFound)?;

			if collection.max_items_per_account.is_some() {
				ensure!(
					receiver_items_amount < &mut collection.max_items_per_account.unwrap(),
					Error::<T>::CollectionItemsPerAccountLimitReached
				);
			}

			// all checks passed

			AccountItems::<T>::remove((&item.owner, &collection_id, &item_id));
			AccountItems::<T>::insert((&receiver, &collection_id, &item_id), ());

			let new_sender_items_amount =
				sender_items_amount.checked_sub(1).ok_or(ArithmeticError::Overflow)?;
			let new_receiver_items_amount =
				receiver_items_amount.checked_add(1).ok_or(ArithmeticError::Overflow)?;
			CountForAccountItems::<T>::insert(&item.owner, &collection_id, new_sender_items_amount);
			CountForAccountItems::<T>::insert(&receiver, &collection_id, new_receiver_items_amount);

			item.owner = receiver.clone();
			item.approvals = Default::default();

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
