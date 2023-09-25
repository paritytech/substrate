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

//! This module contains helper methods to perform functionality associated with minting and burning
//! items for the NFTs pallet.

use crate::*;
use frame_support::{pallet_prelude::*, traits::ExistenceRequirement};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Mint a new unique item with the given `collection`, `item`, and other minting configuration
	/// details.
	///
	/// This function performs the minting of a new unique item. It checks if the item does not
	/// already exist in the given collection, and if the max supply limit (if configured) is not
	/// reached. It also reserves the required deposit for the item and sets the item details
	/// accordingly.
	///
	/// # Errors
	///
	/// This function returns a dispatch error in the following cases:
	/// - If the collection ID is invalid ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - If the item already exists in the collection
	///   ([`AlreadyExists`](crate::Error::AlreadyExists)).
	/// - If the item configuration already exists
	///   ([`InconsistentItemConfig`](crate::Error::InconsistentItemConfig)).
	/// - If the max supply limit (if configured) for the collection is reached
	///   ([`MaxSupplyReached`](crate::Error::MaxSupplyReached)).
	/// - If any error occurs in the `with_details_and_config` closure.
	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		maybe_depositor: Option<T::AccountId>,
		mint_to: T::AccountId,
		item_config: ItemConfig,
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
				let deposit_account = match maybe_depositor {
					None => collection_details.owner.clone(),
					Some(depositor) => depositor,
				};

				let item_owner = mint_to.clone();
				Account::<T, I>::insert((&item_owner, &collection, &item), ());

				if let Ok(existing_config) = ItemConfigOf::<T, I>::try_get(&collection, &item) {
					ensure!(existing_config == item_config, Error::<T, I>::InconsistentItemConfig);
				} else {
					ItemConfigOf::<T, I>::insert(&collection, &item, item_config);
					collection_details.item_configs.saturating_inc();
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

	/// Mints a new item using a pre-signed message.
	///
	/// This function allows minting a new item using a pre-signed message. The minting process is
	/// similar to the regular minting process, but it is performed by a pre-authorized account. The
	/// `mint_to` account receives the newly minted item. The minting process is configurable
	/// through the provided `mint_data`. The attributes, metadata, and price of the item are set
	/// according to the provided `mint_data`. The `with_details_and_config` closure is called to
	/// validate the provided `collection_details` and `collection_config` before minting the item.
	///
	/// - `mint_to`: The account that receives the newly minted item.
	/// - `mint_data`: The pre-signed minting data containing the `collection`, `item`,
	///   `attributes`, `metadata`, `deadline`, `only_account`, and `mint_price`.
	/// - `signer`: The account that is authorized to mint the item using the pre-signed message.
	pub(crate) fn do_mint_pre_signed(
		mint_to: T::AccountId,
		mint_data: PreSignedMintOf<T, I>,
		signer: T::AccountId,
	) -> DispatchResult {
		let PreSignedMint {
			collection,
			item,
			attributes,
			metadata,
			deadline,
			only_account,
			mint_price,
		} = mint_data;
		let metadata = Self::construct_metadata(metadata)?;

		ensure!(
			attributes.len() <= T::MaxAttributesPerCall::get() as usize,
			Error::<T, I>::MaxAttributesLimitReached
		);
		if let Some(account) = only_account {
			ensure!(account == mint_to, Error::<T, I>::WrongOrigin);
		}

		let now = frame_system::Pallet::<T>::block_number();
		ensure!(deadline >= now, Error::<T, I>::DeadlineExpired);

		ensure!(
			Self::has_role(&collection, &signer, CollectionRole::Issuer),
			Error::<T, I>::NoPermission
		);

		let item_config = ItemConfig { settings: Self::get_default_item_settings(&collection)? };
		Self::do_mint(
			collection,
			item,
			Some(mint_to.clone()),
			mint_to.clone(),
			item_config,
			|collection_details, _| {
				if let Some(price) = mint_price {
					T::Currency::transfer(
						&mint_to,
						&collection_details.owner,
						price,
						ExistenceRequirement::KeepAlive,
					)?;
				}
				Ok(())
			},
		)?;
		let admin_account = Self::find_account_by_role(&collection, CollectionRole::Admin);
		if let Some(admin_account) = admin_account {
			for (key, value) in attributes {
				Self::do_set_attribute(
					admin_account.clone(),
					collection,
					Some(item),
					AttributeNamespace::CollectionOwner,
					Self::construct_attribute_key(key)?,
					Self::construct_attribute_value(value)?,
					mint_to.clone(),
				)?;
			}
			if !metadata.len().is_zero() {
				Self::do_set_item_metadata(
					Some(admin_account.clone()),
					collection,
					item,
					metadata,
					Some(mint_to.clone()),
				)?;
			}
		}
		Ok(())
	}

	/// Burns the specified item with the given `collection`, `item`, and `with_details`.
	///
	/// # Errors
	///
	/// This function returns a dispatch error in the following cases:
	/// - If the collection ID is invalid ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - If the item is locked ([`ItemLocked`](crate::Error::ItemLocked)).
	pub fn do_burn(
		collection: T::CollectionId,
		item: T::ItemId,
		with_details: impl FnOnce(&ItemDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::ItemLocked);
		ensure!(
			!Self::has_system_attribute(&collection, &item, PalletAttributes::TransferDisabled)?,
			Error::<T, I>::ItemLocked
		);
		let item_config = Self::get_item_config(&collection, &item)?;
		// NOTE: if item's settings are not empty (e.g. item's metadata is locked)
		// then we keep the config record and don't remove it
		let remove_config = !item_config.has_disabled_settings();
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

				if remove_config {
					collection_details.item_configs.saturating_dec();
				}

				// Clear the metadata if it's not locked.
				if item_config.is_setting_enabled(ItemSetting::UnlockedMetadata) {
					if let Some(metadata) = ItemMetadataOf::<T, I>::take(&collection, &item) {
						let depositor_account =
							metadata.deposit.account.unwrap_or(collection_details.owner.clone());

						T::Currency::unreserve(&depositor_account, metadata.deposit.amount);
						collection_details.item_metadatas.saturating_dec();

						if depositor_account == collection_details.owner {
							collection_details
								.owner_deposit
								.saturating_reduce(metadata.deposit.amount);
						}
					}
				}

				Ok(details.owner)
			},
		)?;

		Item::<T, I>::remove(&collection, &item);
		Account::<T, I>::remove((&owner, &collection, &item));
		ItemPriceOf::<T, I>::remove(&collection, &item);
		PendingSwapOf::<T, I>::remove(&collection, &item);
		ItemAttributesApprovalsOf::<T, I>::remove(&collection, &item);

		if remove_config {
			ItemConfigOf::<T, I>::remove(&collection, &item);
		}

		Self::deposit_event(Event::Burned { collection, item, owner });
		Ok(())
	}
}
