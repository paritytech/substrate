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

//! # NFTs Royalty Pallet
//!
//! A pallet for dealing with non-fungible token royalties.
//!
//! ## Related Modules
//!
//! * [`System`](../frame_system/index.html)
//! * [`Support`](../frame_support/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

mod types;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;

use frame_system::Config as SystemConfig;
pub use pallet::*;
pub use scale_info::Type;
pub use types::*;

pub use sp_std::prelude::*;

use frame_support::{
	pallet_prelude::*,
	sp_runtime::Permill,
	traits::{
		tokens::nonfungibles_v2::{
			Buy as NonFungiblesBuy, Inspect as NonFungiblesInspect,
			InspectEnumerable as NonFungiblesInspectEnumerable, Transfer,
		},
		Currency, ExistenceRequirement, ReservableCurrency,
	},
};

/// The log target of this pallet.
pub const LOG_TARGET: &'static str = "runtime::nfts-royalty";

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;
	use sp_std::fmt::Display;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(0);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The currency mechanism, used for paying for deposits.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// The origin which may forcibly set the royalty for a collection or an item
		type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Identifier for the NFT collection.
		type NftCollectionId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// Identifier for the NFT item within a collection.
		type NftItemId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// NonFungibles traits used within this pallet.
		type Nfts: NonFungiblesInspect<
				Self::AccountId,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			> + NonFungiblesInspectEnumerable<
				Self::AccountId,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			> + NonFungiblesBuy<
				Self::AccountId,
				ItemPrice<Self>,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			> + Transfer<Self::AccountId>;

		/// The maximum number of royalty recipients.
		#[pallet::constant]
		type MaxRecipients: Get<u32>;

		/// The amount of funds that must be reserved for storing an item's royalty.
		#[pallet::constant]
		type ItemRoyaltyDeposit: Get<DepositBalanceOf<Self>>;
	}

	/// Items with a royalty.
	#[pallet::storage]
	pub type ItemRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftItemId),
		RoyaltyConfig<T::AccountId, BalanceOf<T>, T::MaxRecipients>,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The royalty recipient of an NFT item has changed.
		ItemRoyaltyRecipientChanged {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			old_royalty_recipient: T::AccountId,
			new_royalty_recipient: T::AccountId,
		},
		/// The royalty percentage and recipients for an NFT item has been set.
		ItemRoyaltySet {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipients: BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients>,
		},
		/// The royalty for an NFT item has been paid.
		RoyaltyPaid {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_amount_paid: BalanceOf<T>,
			royalty_recipient: T::AccountId,
		},
		/// The royalty for an item has been removed.
		ItemRoyaltyRemoved { nft_collection: T::NftCollectionId, nft: T::NftItemId },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The item ID has not royalty associated.
		NoRoyaltyExists,
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// The NFT does not exist.
		NftDoesNotExist,
		/// The NFT already has a royalty.
		RoyaltyAlreadyExists,
		/// The NFT is not for sale.
		NotForSale,
		/// The royalty percentage is invalid.
		InvalidRoyaltyPercentage,
		/// The list of recipients has reach its limit.
		MaxRecipientsLimit,
		// The NFT item still exists.
		NftStillExists,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set the royalty for an existing NFT item.
		///
		/// The origin must be the owner of the `item`.
		///
		/// - `collection`: The NFT collection of the NFT item.
		/// - `item`: The NFT item to set the royalty for.
		/// - `royalty_percentage`: Royalty percentage to be set.
		/// - `recipients`: The list of royalty recipients.
		///
		/// `ItemRoyaltyDeposit` funds of sender are reserved.
		///
		/// Emits `ItemRoyaltySet`.
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn set_item_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			royalty_percentage: Permill,
			recipients: Vec<RoyaltyDetails<T::AccountId>>,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;

			ensure!(
				T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftDoesNotExist
			);

			// Check that the sender is the owner of the item
			ensure!(
				T::Nfts::owner(&collection_id, &item_id) == Some(caller.clone()),
				Error::<T>::NoPermission
			);

			// Check that the sender is also the owner of the collection
			ensure!(
				T::Nfts::collection_owner(&collection_id) == Some(caller.clone()),
				Error::<T>::NoPermission
			);

			T::Currency::reserve(&caller, T::ItemRoyaltyDeposit::get())?;

			// Check whether the item already has a royalty, if so do not allow to set it again
			ensure!(
				<ItemRoyalty<T>>::get((collection_id, item_id)).is_none(),
				Error::<T>::RoyaltyAlreadyExists
			);

			// Ensure that it not pass the limit of recipients
			let royalties_recipients: BoundedVec<_, T::MaxRecipients> =
				recipients.try_into().map_err(|_| Error::<T>::MaxRecipientsLimit)?;

			// Ensure that the sum of the percentages is 100%
			let mut sum = Permill::zero();
			for recipient in royalties_recipients.iter() {
				sum = sum + recipient.royalty_recipient_percentage;
			}
			ensure!(sum == Permill::one(), Error::<T>::InvalidRoyaltyPercentage);

			// Lock the NFT in the NFT pallet
			Self::do_lock_nft(collection_id, item_id)?;

			ItemRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyConfig::<T::AccountId, BalanceOf<T>, T::MaxRecipients> {
					royalty_percentage,
					depositor: Some(caller),
					deposit: T::ItemRoyaltyDeposit::get(),
					recipients: royalties_recipients.clone(),
				},
			);

			Self::deposit_event(Event::ItemRoyaltySet {
				nft_collection: collection_id,
				nft: item_id,
				royalty_percentage,
				royalty_recipients: royalties_recipients,
			});

			Ok(())
		}

		/// Set the `royalty_recipient` of a collection to another account.
		///
		/// The origin must be a `royalty_recipient` of the specified NFT `item`.
		///
		/// - `collection`: The NFT collection of the NFT item.
		/// - `item`: The NFT item in which the `royalty_recipient` will be changed.
		/// - `new_royalty_recipient`: The new royalty recipient to be set.
		///
		/// Emits `ItemRoyaltyRecipientChanged`.
		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn transfer_item_royalty_recipient(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			new_royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;

			let item_royalty = <ItemRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;

			let mut recipients = item_royalty.recipients.clone();
			let index = recipients
				.iter()
				.position(|recipient| recipient.royalty_recipient == caller)
				.ok_or(Error::<T>::NoPermission)?;
			recipients[index].royalty_recipient = new_royalty_recipient.clone();

			ItemRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyConfig::<T::AccountId, BalanceOf<T>, T::MaxRecipients> {
					royalty_percentage: item_royalty.royalty_percentage,
					depositor: item_royalty.depositor,
					deposit: item_royalty.deposit,
					recipients,
				},
			);
			Self::deposit_event(Event::ItemRoyaltyRecipientChanged {
				nft_collection: collection_id,
				nft: item_id,
				old_royalty_recipient: caller,
				new_royalty_recipient,
			});

			Ok(())
		}

		/// Buy an NFT item if it's up for sale and pays the royalty associated to it.
		///
		/// Origin must be Signed and must not be the owner of the NFT `item`.
		///
		/// - `collection`: The NFT collection of the NFT item.
		/// - `item`: The NFT item the sender wants to buy.
		/// - `bid_price`: The price the sender is willing to pay.
		///
		/// Emits `RoyaltyPaid`.
		#[pallet::call_index(2)]
		#[pallet::weight(0)]
		pub fn buy(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			bid_price: ItemPrice<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			// Retrieve the NFT item price
			let item_price =
				T::Nfts::item_price(&collection_id, &item_id).ok_or(Error::<T>::NotForSale)?;

			// Retrieve the Royalty
			let mut item_royalty: RoyaltyConfig<T::AccountId, BalanceOf<T>, T::MaxRecipients> =
				<ItemRoyalty<T>>::get((collection_id, item_id))
					.ok_or(Error::<T>::NoRoyaltyExists)?;

			// Lock the NFT in the NFT pallet
			Self::do_unlock_nft(collection_id, item_id)?;

			T::Nfts::buy_item(&collection_id, &item_id, &origin, &bid_price)?;

			let royalty_amount_to_pay = item_royalty.royalty_percentage * item_price;

			// Pay royalties to recipients
			for royalty_detail in item_royalty.recipients.iter_mut() {
				let individual_royalty_amount_to_pay =
					royalty_detail.royalty_recipient_percentage * royalty_amount_to_pay;
				let royalty_recipient = &royalty_detail.royalty_recipient;

				T::Currency::transfer(
					&origin,
					royalty_recipient,
					individual_royalty_amount_to_pay,
					ExistenceRequirement::KeepAlive,
				)?;

				Self::deposit_event(Event::RoyaltyPaid {
					nft_collection: collection_id,
					nft: item_id,
					royalty_amount_paid: individual_royalty_amount_to_pay,
					royalty_recipient: royalty_recipient.clone(),
				});
			}

			Ok(())
		}

		/// Remove the royalty associated to an NFT item only if the item no longer exists.
		///
		/// This will also redeem the deposit initially paid for creating the item royalty.
		/// If the royalty was set with `ForceOrigin` then no deposit will be redeemed.
		///
		/// Origin must be Signed and must be the depositor of `ItemRoyalty` or the `ForceOrigin`.
		///
		/// - `collection_id`: The `collection_id` that the item belongs to.
		/// - `item_id`: The NFT `item` that no longer exists and has an associated royalty.
		///
		/// Emits `ItemRoyaltyRemoved`.
		#[pallet::call_index(3)]
		#[pallet::weight(0)]
		pub fn remove_item_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
		) -> DispatchResult {
			let who = ensure_signed(origin.clone())?;

			// Only `ForceOrigin` or depositor can remove the item royalty
			ensure!(
				T::ForceOrigin::try_origin(origin.clone()).is_ok()
					|| <ItemRoyalty<T>>::get((collection_id, item_id))
						.map(|item_royalty| item_royalty.depositor == Some(who))
						.unwrap_or(false),
				Error::<T>::NoPermission
			);

			ensure!(
				!T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftStillExists
			);

			// Delete the item from `ItemRoyalty`
			let item_royalty = <ItemRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;

			if let Some(account) = item_royalty.depositor {
				T::Currency::unreserve(&account, item_royalty.deposit);
			}

			Self::deposit_event(Event::ItemRoyaltyRemoved {
				nft_collection: collection_id,
				nft: item_id,
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		///Disable buys and Swaps from the account holding that NFT to the pallet's account.
		fn do_lock_nft(
			nft_collection_id: T::NftCollectionId,
			nft_id: T::NftItemId,
		) -> DispatchResult {
			T::Nfts::disable_transfer(&nft_collection_id, &nft_id)
		}

		/// Enable transfer the NFT to the account returning the tokens.
		fn do_unlock_nft(
			nft_collection_id: T::NftCollectionId,
			nft_id: T::NftItemId,
		) -> DispatchResult {
			T::Nfts::enable_transfer(&nft_collection_id, &nft_id)
		}
	}
}
