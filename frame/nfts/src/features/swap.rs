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
		sender: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		desired_collection_id: T::CollectionId,
		desired_item_id: T::ItemId,
		maybe_price: Option<ItemPrice<T, I>>,
		maybe_duration: Option<<T as SystemConfig>::BlockNumber>,
	) -> DispatchResult {
		let item = Item::<T, I>::get(&collection_id, &item_id).ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(item.owner == sender, Error::<T, I>::NoPermission);

		Item::<T, I>::get(&desired_collection_id, &desired_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;

		let now = frame_system::Pallet::<T>::block_number();
		let deadline = maybe_duration.map(|d| d.saturating_add(now));

		PendingSwapOf::<T, I>::insert(
			&collection_id,
			&item_id,
			PendingSwap {
				desired_collection: desired_collection_id,
				desired_item: desired_item_id,
				price: maybe_price,
				deadline,
			},
		);

		Self::deposit_event(Event::SwapCreated {
			collection: collection_id,
			item: item_id,
			desired_collection: desired_collection_id,
			desired_item: desired_item_id,
			price: maybe_price,
			deadline,
		});

		Ok(())
	}

	pub fn do_cancel_swap(
		sender: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
	) -> DispatchResult {
		let item = Item::<T, I>::get(&collection_id, &item_id).ok_or(Error::<T, I>::UnknownItem)?;
		let swap = PendingSwapOf::<T, I>::get(&collection_id, &item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		let is_past_deadline = if let Some(deadline) = swap.deadline {
			let now = frame_system::Pallet::<T>::block_number();
			now > deadline
		} else {
			false
		};

		if !is_past_deadline {
			ensure!(item.owner == sender, Error::<T, I>::NoPermission);
		}

		PendingSwapOf::<T, I>::remove(&collection_id, &item_id);

		Self::deposit_event(Event::SwapCancelled {
			collection: collection_id,
			item: item_id,
			desired_collection: swap.desired_collection,
			desired_item: swap.desired_item,
			price: swap.price,
			deadline: swap.deadline,
		});

		Ok(())
	}

	pub fn do_claim_swap(
		sender: T::AccountId,
		send_collection_id: T::CollectionId,
		send_item_id: T::ItemId,
		receive_collection_id: T::CollectionId,
		receive_item_id: T::ItemId,
		maybe_receive_amount: Option<ItemPrice<T, I>>,
	) -> DispatchResult {
		let send_item = Item::<T, I>::get(&send_collection_id, &send_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let receive_item = Item::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let swap = PendingSwapOf::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		ensure!(send_item.owner == sender, Error::<T, I>::NoPermission);
		ensure!(swap.desired_collection == send_collection_id, Error::<T, I>::UnknownSwap);
		ensure!(swap.desired_item == send_item_id, Error::<T, I>::UnknownSwap);
		ensure!(swap.price == maybe_receive_amount, Error::<T, I>::UnknownSwap);

		if let Some(deadline) = swap.deadline {
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(deadline >= now, Error::<T, I>::DeadlineExpired);
		}

		if let Some(amount) = swap.price {
			T::Currency::transfer(&receive_item.owner, &send_item.owner, amount, KeepAlive)?;
		}

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
			send_collection: send_collection_id,
			send_item: send_item_id,
			send_item_owner: send_item.owner,
			receive_collection: receive_collection_id,
			receive_item: receive_item_id,
			receive_item_owner: receive_item.owner,
			price: swap.price,
			deadline: swap.deadline,
		});

		Ok(())
	}
}
