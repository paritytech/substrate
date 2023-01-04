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
	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		depositor: T::AccountId,
		mint_to: T::AccountId,
		item_config: ItemConfig,
		deposit_collection_owner: bool,
		with_details_and_config: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&CollectionConfigFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!Item::<T, I>::contains_key(collection, item), Error::<T, I>::AlreadyExists);

		Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> DispatchResult {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;

				let collection_config = Self::get_collection_config(&collection)?;
				with_details_and_config(collection_details, &collection_config)?;

				if let Some(max_supply) = collection_config.max_supply {
					ensure!(collection_details.items < max_supply, Error::<T, I>::MaxSupplyReached);
				}

				collection_details.items.saturating_inc();

				let collection_config = Self::get_collection_config(&collection)?;
				let deposit_amount = match collection_config
					.is_setting_enabled(CollectionSetting::DepositRequired)
				{
					true => T::ItemDeposit::get(),
					false => Zero::zero(),
				};
				let deposit_account = match deposit_collection_owner {
					true => collection_details.owner.clone(),
					false => depositor,
				};

				let item_owner = mint_to.clone();
				Account::<T, I>::insert((&item_owner, &collection, &item), ());

				if let Ok(existing_config) = ItemConfigOf::<T, I>::try_get(&collection, &item) {
					ensure!(existing_config == item_config, Error::<T, I>::InconsistentItemConfig);
				} else {
					ItemConfigOf::<T, I>::insert(&collection, &item, item_config);
				}

				T::Currency::reserve(&deposit_account, deposit_amount)?;

				let deposit = ItemDeposit { account: deposit_account, amount: deposit_amount };
				let details = ItemDetails {
					owner: item_owner,
					approvals: ApprovalsOf::<T, I>::default(),
					deposit,
				};
				Item::<T, I>::insert(&collection, &item, details);
				Ok(())
			},
		)?;

		Self::deposit_event(Event::Issued { collection, item, owner: mint_to });
		Ok(())
	}

	pub fn do_burn(
		collection: T::CollectionId,
		item: T::ItemId,
		with_details: impl FnOnce(&ItemDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::ItemLocked);
		let owner = Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> Result<T::AccountId, DispatchError> {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				let details = Item::<T, I>::get(&collection, &item)
					.ok_or(Error::<T, I>::UnknownCollection)?;
				with_details(&details)?;

				// Return the deposit.
				T::Currency::unreserve(&details.deposit.account, details.deposit.amount);
				collection_details.items.saturating_dec();
				Ok(details.owner)
			},
		)?;

		Item::<T, I>::remove(&collection, &item);
		Account::<T, I>::remove((&owner, &collection, &item));
		ItemPriceOf::<T, I>::remove(&collection, &item);
		PendingSwapOf::<T, I>::remove(&collection, &item);
		ItemAttributesApprovalsOf::<T, I>::remove(&collection, &item);

		// NOTE: if item's settings are not empty (e.g. item's metadata is locked)
		// then we keep the record and don't remove it
		let config = Self::get_item_config(&collection, &item)?;
		if !config.has_disabled_settings() {
			ItemConfigOf::<T, I>::remove(&collection, &item);
		}

		Self::deposit_event(Event::Burned { collection, item, owner });
		Ok(())
	}
}
