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
	pub fn do_approve_transfer(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		delegate: T::AccountId,
		deadline: Option<T::BlockNumber>,
		config: CollectionConfig,
	) -> DispatchResult {
		let user_features: BitFlags<UserFeature> = config.user_features.get();
		ensure!(
			!user_features.contains(UserFeature::NonTransferableItems),
			Error::<T>::ItemsNotTransferable
		);

		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			// update the approvals
			item.approvals
				.try_insert(delegate.clone(), deadline)
				.map_err(|_| Error::<T>::MaxApprovalsReached)?;

			Self::deposit_event(Event::ApprovalAdded {
				collection_id,
				item_id,
				owner: item.owner.clone(),
				delegate,
			});

			Ok(())
		})
	}

	pub fn do_remove_transfer_approval(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
		delegate: T::AccountId,
	) -> DispatchResult {
		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			let is_owner = item.owner == caller;

			// remove the approval
			if let Some(deadline) = item.approvals.get(&delegate) {
				// anyone can remove an expired approval
				let mut is_past_deadline = false;
				if let Some(deadline) = deadline {
					let now = frame_system::Pallet::<T>::block_number();
					if deadline < &now {
						is_past_deadline = true;
					}
				}
				if is_past_deadline || is_owner {
					item.approvals.remove(&delegate);
				} else {
					return Err(Error::<T>::NotAuthorized.into())
				}
			} else {
				return Err(Error::<T>::WrongDelegate.into())
			}

			Self::deposit_event(Event::ApprovalRemoved {
				collection_id,
				item_id,
				owner: item.owner.clone(),
				delegate,
			});

			Ok(())
		})
	}

	pub fn do_clear_all_transfer_approvals(
		caller: T::AccountId,
		collection_id: T::CollectionId,
		item_id: T::ItemId,
	) -> DispatchResult {
		Items::<T>::try_mutate(collection_id, item_id, |maybe_item| {
			let item = maybe_item.as_mut().ok_or(Error::<T>::ItemNotFound)?;
			ensure!(item.owner == caller, Error::<T>::NotAuthorized);

			// clear the approvals
			item.approvals = Default::default();

			Self::deposit_event(Event::ApprovalsCleared {
				collection_id,
				item_id,
				owner: item.owner.clone(),
			});

			Ok(())
		})
	}
}
