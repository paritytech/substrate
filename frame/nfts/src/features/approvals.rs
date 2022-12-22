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

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub(crate) fn do_approve_transfer(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
		delegate: T::AccountId,
		maybe_deadline: Option<<T as SystemConfig>::BlockNumber>,
	) -> DispatchResult {
		ensure!(
			Self::is_pallet_feature_enabled(PalletFeature::Approvals),
			Error::<T, I>::MethodDisabled
		);
		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;

		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
			Error::<T, I>::ItemsNonTransferable
		);

		if let Some(check_origin) = maybe_check_origin {
			let is_admin = Self::has_role(&collection, &check_origin, CollectionRole::Admin);
			let permitted = is_admin || check_origin == details.owner;
			ensure!(permitted, Error::<T, I>::NoPermission);
		}

		let now = frame_system::Pallet::<T>::block_number();
		let deadline = maybe_deadline.map(|d| d.saturating_add(now));

		details
			.approvals
			.try_insert(delegate.clone(), deadline)
			.map_err(|_| Error::<T, I>::ReachedApprovalLimit)?;
		Item::<T, I>::insert(&collection, &item, &details);

		Self::deposit_event(Event::TransferApproved {
			collection,
			item,
			owner: details.owner,
			delegate,
			deadline,
		});

		Ok(())
	}

	pub(crate) fn do_cancel_approval(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
		delegate: T::AccountId,
	) -> DispatchResult {
		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;

		let maybe_deadline = details.approvals.get(&delegate).ok_or(Error::<T, I>::NotDelegate)?;

		let is_past_deadline = if let Some(deadline) = maybe_deadline {
			let now = frame_system::Pallet::<T>::block_number();
			now > *deadline
		} else {
			false
		};

		if !is_past_deadline {
			if let Some(check_origin) = maybe_check_origin {
				let is_admin = Self::has_role(&collection, &check_origin, CollectionRole::Admin);
				let permitted = is_admin || check_origin == details.owner;
				ensure!(permitted, Error::<T, I>::NoPermission);
			}
		}

		details.approvals.remove(&delegate);
		Item::<T, I>::insert(&collection, &item, &details);

		Self::deposit_event(Event::ApprovalCancelled {
			collection,
			item,
			owner: details.owner,
			delegate,
		});

		Ok(())
	}

	pub(crate) fn do_clear_all_transfer_approvals(
		maybe_check_origin: Option<T::AccountId>,
		collection: T::CollectionId,
		item: T::ItemId,
	) -> DispatchResult {
		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;

		if let Some(check_origin) = maybe_check_origin {
			let is_admin = Self::has_role(&collection, &check_origin, CollectionRole::Admin);
			let permitted = is_admin || check_origin == details.owner;
			ensure!(permitted, Error::<T, I>::NoPermission);
		}

		details.approvals.clear();
		Item::<T, I>::insert(&collection, &item, &details);

		Self::deposit_event(Event::AllApprovalsCancelled {
			collection,
			item,
			owner: details.owner,
		});

		Ok(())
	}
}
