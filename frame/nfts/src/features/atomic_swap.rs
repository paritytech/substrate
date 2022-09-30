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
	pub fn do_create_swap(
		caller: T::AccountId,
		offered_collection_id: T::CollectionId,
		offered_item_id: T::ItemId,
		desired_collection_id: T::CollectionId,
		maybe_desired_item_id: Option<T::ItemId>,
		maybe_price: Option<ItemPrice<T, I>>,
		maybe_price_direction: Option<PriceDirection>,
		maybe_duration: Option<<T as SystemConfig>::BlockNumber>,
	) -> DispatchResult {
		let item = Item::<T, I>::get(&offered_collection_id, &offered_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(item.owner == caller, Error::<T, I>::NoPermission);

		match maybe_desired_item_id {
			Some(desired_item_id) => {
				if !(Item::<T, I>::contains_key(&desired_collection_id, &desired_item_id)) {
					return Err(Error::<T, I>::UnknownItem.into())
				}
			},
			None =>
				if !(Collection::<T, I>::contains_key(&desired_collection_id)) {
					return Err(Error::<T, I>::UnknownCollection.into())
				},
		};

		if maybe_price.is_some() && maybe_price_direction.is_none() {
			return Err(Error::<T, I>::PriceDirectionNotSet.into())
		}
		if maybe_price.is_none() && maybe_price_direction.is_some() {
			return Err(Error::<T, I>::PriceDirectionCannotBeSet.into())
		}

		let now = frame_system::Pallet::<T>::block_number();
		let maybe_deadline = maybe_duration.map(|d| d.saturating_add(now));

		PendingSwapOf::<T, I>::insert(
			&offered_collection_id,
			&offered_item_id,
			PendingSwap {
				desired_collection: desired_collection_id,
				desired_item: maybe_desired_item_id,
				price: maybe_price,
				price_direction: maybe_price_direction.clone(),
				deadline: maybe_deadline,
			},
		);

		Self::deposit_event(Event::SwapCreated {
			offered_collection: offered_collection_id,
			offered_item: offered_item_id,
			desired_collection: desired_collection_id,
			desired_item: maybe_desired_item_id,
			price: maybe_price,
			price_direction: maybe_price_direction,
			deadline: maybe_deadline,
		});

		Ok(())
	}

	pub fn do_cancel_swap(
		caller: T::AccountId,
		offered_collection_id: T::CollectionId,
		offered_item_id: T::ItemId,
	) -> DispatchResult {
		let swap = PendingSwapOf::<T, I>::get(&offered_collection_id, &offered_item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		let is_past_deadline = if let Some(deadline) = swap.deadline {
			let now = frame_system::Pallet::<T>::block_number();
			now > deadline
		} else {
			false
		};

		if !is_past_deadline {
			let item = Item::<T, I>::get(&offered_collection_id, &offered_item_id)
				.ok_or(Error::<T, I>::UnknownItem)?;
			ensure!(item.owner == caller, Error::<T, I>::NoPermission);
		}

		PendingSwapOf::<T, I>::remove(&offered_collection_id, &offered_item_id);

		Self::deposit_event(Event::SwapCancelled {
			offered_collection: offered_collection_id,
			offered_item: offered_item_id,
			desired_collection: swap.desired_collection,
			desired_item: swap.desired_item,
			price: swap.price,
			price_direction: swap.price_direction,
			deadline: swap.deadline,
		});

		Ok(())
	}

	pub fn do_claim_swap(
		caller: T::AccountId,
		send_collection_id: T::CollectionId,
		send_item_id: T::ItemId,
		receive_collection_id: T::CollectionId,
		receive_item_id: T::ItemId,
		maybe_price: Option<ItemPrice<T, I>>,
		maybe_price_direction: Option<PriceDirection>,
	) -> DispatchResult {
		let send_item = Item::<T, I>::get(&send_collection_id, &send_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let receive_item = Item::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let swap = PendingSwapOf::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		ensure!(send_item.owner == caller, Error::<T, I>::NoPermission);
		ensure!(
			swap.desired_collection == send_collection_id &&
				swap.price == maybe_price &&
				swap.price_direction == maybe_price_direction,
			Error::<T, I>::UnknownSwap
		);

		if let Some(desired_item) = swap.desired_item {
			ensure!(desired_item == send_item_id, Error::<T, I>::UnknownSwap);
		}

		if let Some(deadline) = swap.deadline {
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now <= deadline, Error::<T, I>::DeadlineExpired);
		}

		if let Some(amount) = swap.price {
			match swap.price_direction {
				Some(PriceDirection::Send) =>
					T::Currency::transfer(&receive_item.owner, &send_item.owner, amount, KeepAlive)?,
				Some(PriceDirection::Receive) =>
					T::Currency::transfer(&send_item.owner, &receive_item.owner, amount, KeepAlive)?,
				_ => {},
			};
		}

		// This also removes the swap.
		Self::do_transfer(send_collection_id, send_item_id, receive_item.owner.clone(), |_, _| {
			Ok(())
		})?;
		Self::do_transfer(
			receive_collection_id,
			receive_item_id,
			send_item.owner.clone(),
			|_, _| Ok(()),
		)?;

		Self::deposit_event(Event::SwapClaimed {
			sent_collection: send_collection_id,
			sent_item: send_item_id,
			sent_item_owner: send_item.owner,
			received_collection: receive_collection_id,
			received_item: receive_item_id,
			received_item_owner: receive_item.owner,
			price: swap.price,
			price_direction: swap.price_direction,
			deadline: swap.deadline,
		});

		Ok(())
	}
}
