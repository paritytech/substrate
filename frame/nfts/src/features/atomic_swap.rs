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

use crate::*;
use frame_support::{
	pallet_prelude::*,
	traits::{Currency, ExistenceRequirement::KeepAlive},
};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn do_create_swap(
		caller: T::AccountId,
		offered_collection_id: T::CollectionId,
		offered_item_id: T::ItemId,
		desired_collection_id: T::CollectionId,
		maybe_desired_item_id: Option<T::ItemId>,
		maybe_price: Option<PriceWithDirection<ItemPrice<T, I>>>,
		duration: frame_system::pallet_prelude::BlockNumberFor<T>,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Swaps),
			Error::<T, I>::MethodDisabled
		);
		ensure!(duration <= T::MaxDeadlineDuration::get(), Error::<T, I>::WrongDuration);

		let item = Item::<T, I>::get(&offered_collection_id, &offered_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		ensure!(item.owner == caller, Error::<T, I>::NoPermission);

		match maybe_desired_item_id {
			Some(desired_item_id) => ensure!(
				Item::<T, I>::contains_key(&desired_collection_id, &desired_item_id),
				Error::<T, I>::UnknownItem
			),
			None => ensure!(
				Collection::<T, I>::contains_key(&desired_collection_id),
				Error::<T, I>::UnknownCollection
			),
		};

		let now = frame_system::Pallet::<T>::block_number();
		let deadline = duration.saturating_add(now);

		PendingSwapOf::<T, I>::insert(
			&offered_collection_id,
			&offered_item_id,
			PendingSwap {
				desired_collection: desired_collection_id,
				desired_item: maybe_desired_item_id,
				price: maybe_price.clone(),
				deadline,
			},
		);

		Self::deposit_event(Event::SwapCreated {
			offered_collection: offered_collection_id,
			offered_item: offered_item_id,
			desired_collection: desired_collection_id,
			desired_item: maybe_desired_item_id,
			price: maybe_price,
			deadline,
		});

		Ok(())
	}

	pub(crate) fn do_cancel_swap(
		caller: T::AccountId,
		offered_collection_id: T::CollectionId,
		offered_item_id: T::ItemId,
	) -> DispatchResult {
		let swap = PendingSwapOf::<T, I>::get(&offered_collection_id, &offered_item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		let now = frame_system::Pallet::<T>::block_number();
		if swap.deadline > now {
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
			deadline: swap.deadline,
		});

		Ok(())
	}

	pub(crate) fn do_claim_swap(
		caller: T::AccountId,
		send_collection_id: T::CollectionId,
		send_item_id: T::ItemId,
		receive_collection_id: T::CollectionId,
		receive_item_id: T::ItemId,
		witness_price: Option<PriceWithDirection<ItemPrice<T, I>>>,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Swaps),
			Error::<T, I>::MethodDisabled
		);

		let send_item = Item::<T, I>::get(&send_collection_id, &send_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let receive_item = Item::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownItem)?;
		let swap = PendingSwapOf::<T, I>::get(&receive_collection_id, &receive_item_id)
			.ok_or(Error::<T, I>::UnknownSwap)?;

		ensure!(send_item.owner == caller, Error::<T, I>::NoPermission);
		ensure!(
			swap.desired_collection == send_collection_id && swap.price == witness_price,
			Error::<T, I>::UnknownSwap
		);

		if let Some(desired_item) = swap.desired_item {
			ensure!(desired_item == send_item_id, Error::<T, I>::UnknownSwap);
		}

		let now = frame_system::Pallet::<T>::block_number();
		ensure!(now <= swap.deadline, Error::<T, I>::DeadlineExpired);

		if let Some(ref price) = swap.price {
			match price.direction {
				PriceDirection::Send => T::Currency::transfer(
					&receive_item.owner,
					&send_item.owner,
					price.amount,
					KeepAlive,
				)?,
				PriceDirection::Receive => T::Currency::transfer(
					&send_item.owner,
					&receive_item.owner,
					price.amount,
					KeepAlive,
				)?,
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
			deadline: swap.deadline,
		});

		Ok(())
	}
}
