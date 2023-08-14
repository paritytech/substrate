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
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_transfer(
		collection: T::CollectionId,
		item: T::ItemId,
		dest: T::AccountId,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&mut ItemDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;

		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::ItemLocked);
		ensure!(
			!Self::has_system_attribute(&collection, &item, PalletAttributes::TransferDisabled)?,
			Error::<T, I>::ItemLocked
		);

		let collection_config = Self::get_collection_config(&collection)?;
		ensure!(
			collection_config.is_setting_enabled(CollectionSetting::TransferableItems),
			Error::<T, I>::ItemsNonTransferable
		);

		let item_config = Self::get_item_config(&collection, &item)?;
		ensure!(
			item_config.is_setting_enabled(ItemSetting::Transferable),
			Error::<T, I>::ItemLocked
		);

		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownItem)?;
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &item));
		Account::<T, I>::insert((&dest, &collection, &item), ());
		let origin = details.owner;
		details.owner = dest;

		// The approved accounts have to be reset to None, because otherwise pre-approve attack
		// would be possible, where the owner can approve their second account before making the
		// transaction and then claiming the item back.
		details.approvals.clear();

		Item::<T, I>::insert(&collection, &item, &details);
		ItemPriceOf::<T, I>::remove(&collection, &item);
		PendingSwapOf::<T, I>::remove(&collection, &item);

		Self::deposit_event(Event::Transferred {
			collection,
			item,
			from: origin,
			to: details.owner,
		});
		Ok(())
	}

	pub(crate) fn do_transfer_ownership(
		origin: T::AccountId,
		collection: T::CollectionId,
		owner: T::AccountId,
	) -> DispatchResult {
		let acceptable_collection = OwnershipAcceptance::<T, I>::get(&owner);
		ensure!(acceptable_collection.as_ref() == Some(&collection), Error::<T, I>::Unaccepted);

		Collection::<T, I>::try_mutate(collection, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
			ensure!(origin == details.owner, Error::<T, I>::NoPermission);
			if details.owner == owner {
				return Ok(())
			}

			// Move the deposit to the new owner.
			T::Currency::repatriate_reserved(
				&details.owner,
				&owner,
				details.owner_deposit,
				Reserved,
			)?;
			CollectionAccount::<T, I>::remove(&details.owner, &collection);
			CollectionAccount::<T, I>::insert(&owner, &collection, ());

			details.owner = owner.clone();
			OwnershipAcceptance::<T, I>::remove(&owner);

			Self::deposit_event(Event::OwnerChanged { collection, new_owner: owner });
			Ok(())
		})
	}

	pub(crate) fn do_set_accept_ownership(
		who: T::AccountId,
		maybe_collection: Option<T::CollectionId>,
	) -> DispatchResult {
		let old = OwnershipAcceptance::<T, I>::get(&who);
		match (old.is_some(), maybe_collection.is_some()) {
			(false, true) => {
				frame_system::Pallet::<T>::inc_consumers(&who)?;
			},
			(true, false) => {
				frame_system::Pallet::<T>::dec_consumers(&who);
			},
			_ => {},
		}
		if let Some(collection) = maybe_collection.as_ref() {
			OwnershipAcceptance::<T, I>::insert(&who, collection);
		} else {
			OwnershipAcceptance::<T, I>::remove(&who);
		}
		Self::deposit_event(Event::OwnershipAcceptanceChanged { who, maybe_collection });
		Ok(())
	}

	pub(crate) fn do_force_collection_owner(
		collection: T::CollectionId,
		owner: T::AccountId,
	) -> DispatchResult {
		Collection::<T, I>::try_mutate(collection, |maybe_details| {
			let details = maybe_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
			if details.owner == owner {
				return Ok(())
			}

			// Move the deposit to the new owner.
			T::Currency::repatriate_reserved(
				&details.owner,
				&owner,
				details.owner_deposit,
				Reserved,
			)?;

			CollectionAccount::<T, I>::remove(&details.owner, &collection);
			CollectionAccount::<T, I>::insert(&owner, &collection, ());
			details.owner = owner.clone();

			Self::deposit_event(Event::OwnerChanged { collection, new_owner: owner });
			Ok(())
		})
	}
}
