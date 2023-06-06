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
//! A pallet for dealing with NFT royalties.
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

use frame_support::{
	pallet_prelude::*,
	sp_runtime::Permill,
	traits::{
		tokens::nonfungibles_v2::{
			Buy as NonFungiblesBuy, Inspect as NonFungiblesInspect,
			InspectEnumerable as NonFungiblesInspectEnumerable,
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

		/// The origin which may forcibly create or destroy an item or otherwise alter privileged
		/// attributes.
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
			>;

		/// The maximum number of royalty recipients.
		#[pallet::constant]
		type MaxRecipients: Get<u32>;

		/// The amount of funds that must be reserved for storing a collection's royalty.
		#[pallet::constant]
		type CollectionRoyaltyDeposit: Get<DepositBalanceOf<Self>>;

		/// The amount of funds that must be reserved for storing an item's royalty.
		#[pallet::constant]
		type ItemRoyaltyDeposit: Get<DepositBalanceOf<Self>>;
	}

	/// The storage for NFT collections with a royalty
	/// This will be the royalty used for all items in the collection unless overridden in `ItemWithRoyalty`
	#[pallet::storage]
	pub type CollectionWithRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::NftCollectionId,
		RoyaltyDetails<T::AccountId>,
		OptionQuery,
	>;

	/// The storage for NFT items with a royalty.
	/// Setting the royalty in this storage will override the royalty set in `CollectionWithRoyalty` only for the specific item.
	#[pallet::storage]
	pub type ItemWithRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftItemId),
		RoyaltyDetails<T::AccountId>,
		OptionQuery,
	>;

	/// The storage for royalty recipient(s) and the percentage of the total royalty each will receive.
	#[pallet::storage]
	pub type CollectionRoyaltyRecipients<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::NftCollectionId,
		BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients>,
	>;

	/// The storage for royalty recipient(s) and the percentage of the total royalty each will receive.
	/// Setting the recipients in this storage will override the recipient(s) set in `CollectionRoyaltyRecipients` only for the specific item.
	#[pallet::storage]
	pub type ItemRoyaltyRecipients<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftItemId),
		BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients>,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The royalty recipient of an NFT collection has changed.
		RecipientCollectionRoyaltyChanged {
			nft_collection: T::NftCollectionId,
			new_royalty_recipient: T::AccountId,
		},
		/// The royalty recipient of an NFT item has changed.
		RecipientItemRoyaltyChanged {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			new_royalty_recipient: T::AccountId,
		},
		/// The royalty percentage and recipient of an already existing NFT item has been set.
		RoyaltySet {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		},
		/// The royalty percentage and recipient for a collection has been set.
		RoyaltyForCollectionSet {
			nft_collection: T::NftCollectionId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		},
		/// The royalty for an NFT item has been paid.
		RoyaltyPaid {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_amount_paid: BalanceOf<T>,
			royalty_recipient: T::AccountId,
		},
		/// The royalty recipients for a collection have been set.
		CollectionRoyaltyRecipientsCreated {
			nft_collection: T::NftCollectionId,
			royalty_recipients: BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients>,
		},
		/// The royalty recipients for an item have been set.
		ItemRoyaltyRecipientsCreated {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_recipients: BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients>,
		},
		/// The royalty for a collection has been removed.
		CollectionRoyaltyRemoved {
			nft_collection: T::NftCollectionId,
		},
		/// The royalty for an item has been removed.
		ItemRoyaltyRemoved {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
		},
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
		/// NFT collection does not exist.
		CollectionDoesNotExist,
		/// The royalty recipient already exists.
		RoyaltyRecipientsAlreadyExist,
		/// The royalty percentage is invalid.
		InvalidRoyaltyPercentage,
		/// The list of recipients has reach its limit.
		MaxRecipientsLimit,
		// The collection still exists.
		CollectionStillExists,
		// The item still exists.
		NftStillExists,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Set the royalty for an existing collection.
		///
		/// The origin must be the actual owner of the `collection` or the `ForceOrigin`.
		///
		/// - `collection_id`: The NFT collection id.
		/// - `royalty_percentage`: Royalty percentage to be set.
		/// - `royalty_recipient`: Account into which the royalty will be sent to.
		///
		/// Emits `RoyaltySet`.
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn set_collection_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;
			
			ensure!(
				T::Nfts::collections().any(|id| id == collection_id),
				Error::<T>::CollectionDoesNotExist
			);

			if let Some(check_owner) = maybe_check_owner {
				ensure!(T::Nfts::collection_owner(&collection_id) == Some(check_owner.clone()), Error::<T>::NoPermission);
				let owner = &check_owner;
				T::Currency::reserve(owner, T::CollectionRoyaltyDeposit::get())?;
			}

			// The collection royalty can only be set once
			ensure!(
				<CollectionWithRoyalty<T>>::get(collection_id).is_none(),
				Error::<T>::RoyaltyAlreadyExists
			);

			// Set the royalty for the collection
			CollectionWithRoyalty::<T>::insert(
				collection_id,
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage,
					royalty_recipient: royalty_recipient.clone(),
				},
			);

			Self::deposit_event(Event::RoyaltyForCollectionSet {
				nft_collection: collection_id,
				royalty_percentage,
				royalty_recipient: royalty_recipient.clone(),
			});

			Ok(())
		}

		/// Set the royalty for an existing item.
		///
		/// The origin must be the actual owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item to set the royalty.
		/// - `royalty_percentage`: Royalty percentage to be set.
		/// - `royalty_recipient`: Account into which the item royalties will be transfered.
		///
		/// Emits `RoyaltySet`.
		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn set_item_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			ensure!(
				T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftDoesNotExist
			);

			if let Some(check_owner) = maybe_check_owner {
				ensure!(
					T::Nfts::owner(&collection_id, &item_id) == Some(check_owner.clone()),
					Error::<T>::NoPermission
				);
				let owner = &check_owner;
				T::Currency::reserve(owner, T::ItemRoyaltyDeposit::get())?;
			}

			// Check whether the item has already a royalty, if so do not allow to set it again
			ensure!(
				<ItemWithRoyalty<T>>::get((collection_id, item_id)).is_none(),
				Error::<T>::RoyaltyAlreadyExists
			);

			ItemWithRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage,
					royalty_recipient: royalty_recipient.clone(),
				},
			);

			Self::deposit_event(Event::RoyaltySet {
				nft_collection: collection_id,
				nft: item_id,
				royalty_percentage,
				royalty_recipient: royalty_recipient.clone(),
			});

			Ok(())
		}


		/// Create royalty recipients for an existing collection.
		///
		/// Origin must be Signed and must not be the owner of the `collection`.
		///
		/// - `collection`: The collection of the item.
		/// - `recipients`: The recipients of the royalties.
		///
		/// Emits `CollectionRoyaltyRecipientsCreated`.
		#[pallet::call_index(2)]
		#[pallet::weight(0)]
		pub fn set_collection_royalty_recipients(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			recipients: Vec<RoyaltyDetails<T::AccountId>>,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			// Ensure that the collection exists
			ensure!(
				T::Nfts::collections().any(|id| id == collection_id),
				Error::<T>::CollectionDoesNotExist
			);
			// Ensure that the sender is the owner of the collection
			if let Some(check_origin) = maybe_check_origin {
				ensure!(
					T::Nfts::collection_owner(&collection_id) == Some(check_origin),
					Error::<T>::NoPermission
				);
			}
			// Ensure that it not pass the limit of recipients
			let royalties_recipients: BoundedVec<_, T::MaxRecipients> =
				recipients.try_into().map_err(|_| Error::<T>::MaxRecipientsLimit)?;

			// Should we do this? Or should we allow to overwrite the recipients that way we have
			// only one extrinsic for creating recipients and updating them. Ensure that the
			// collection does not have any royalty recipients yet
			ensure!(
				!CollectionRoyaltyRecipients::<T>::contains_key(&collection_id),
				Error::<T>::RoyaltyRecipientsAlreadyExist
			);

			// Ensure that the sum of the percentages is 100%
			let mut sum = Permill::zero();
			for recipient in royalties_recipients.iter() {
				sum = sum + recipient.royalty_percentage;
			}
			ensure!(sum == Permill::one(), Error::<T>::InvalidRoyaltyPercentage);

			// Create royalty recipients
			CollectionRoyaltyRecipients::<T>::insert(&collection_id, royalties_recipients.clone());

			Self::deposit_event(Event::CollectionRoyaltyRecipientsCreated {
				nft_collection: collection_id,
				royalty_recipients: royalties_recipients,
			});

			Ok(())
		}

		/// Create royalty recipients for an existing item.
		///
		/// Origin must be Signed and must not be the owner of the `collection`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The id of the item.
		/// - `recipients`: The recipients of the royalties.
		///
		/// Emits `ItemRoyaltyRecipientsCreated`.
		#[pallet::call_index(3)]
		#[pallet::weight(0)]
		pub fn set_item_royalty_recipients(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			recipients: Vec<RoyaltyDetails<T::AccountId>>,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			// Ensure that the item exists
			ensure!(
				T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftDoesNotExist
			);

			// Ensure that the sender is the owner of the item
			if let Some(check_origin) = maybe_check_origin {
				ensure!(
					T::Nfts::owner(&collection_id, &item_id) == Some(check_origin),
					Error::<T>::NoPermission
				);
			}

			// Ensure that it not pass the limit of recipients
			let royalties_recipients: BoundedVec<_, T::MaxRecipients> =
				recipients.try_into().map_err(|_| Error::<T>::MaxRecipientsLimit)?;

			// Check whether the item has already a a list of royalty recipients, if so do not allow to set it again
			ensure!(
				!ItemRoyaltyRecipients::<T>::contains_key((&collection_id, &item_id)),
				Error::<T>::RoyaltyRecipientsAlreadyExist
			);


			// Ensure that the sum of the percentages is 100%
			let mut sum = Permill::zero();
			for recipient in royalties_recipients.iter() {
				sum = sum + recipient.royalty_percentage;
			}
			ensure!(sum == Permill::one(), Error::<T>::InvalidRoyaltyPercentage);

			// Create royalty recipients
			ItemRoyaltyRecipients::<T>::insert((&collection_id, &item_id), royalties_recipients.clone());

			Self::deposit_event(Event::ItemRoyaltyRecipientsCreated {
				nft_collection: collection_id,
				nft: item_id,
				royalty_recipients: royalties_recipients,
			});

			Ok(())
		}

		/// Transfer the royalties associated to a collection to another royalty_recipient.
		///
		/// The origin must be the actual royalty_recipient of the `collection`.
		///
		/// - `collection`: The collection of the item to be burned.
		/// - `new_royalty_recipient`: Account into which the item royalties will be transfered.
		///
		/// Emits `RecipientCollectionRoyaltyChanged`.
		#[pallet::call_index(4)]
		#[pallet::weight(0)]
		pub fn transfer_collection_royalty_recipient(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			new_royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;

			let item_royalties = <CollectionWithRoyalty<T>>::take(collection_id)
				.ok_or(Error::<T>::NoRoyaltyExists)?;
			ensure!(item_royalties.royalty_recipient == caller, Error::<T>::NoPermission);

			CollectionWithRoyalty::<T>::insert(
				collection_id,
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage: item_royalties.royalty_percentage,
					royalty_recipient: new_royalty_recipient.clone(),
				},
			);
			Self::deposit_event(Event::RecipientCollectionRoyaltyChanged {
				nft_collection: collection_id,
				new_royalty_recipient,
			});

			Ok(())
		}

		/// Transfer the royalties associated to an item to another royalty_recipient.
		///
		/// The origin must be the actual royalty_recipient of the `item`.
		///
		/// - `collection`: The collection of the item to be burned.
		/// - `item`: The item to be burned.
		/// - `new_royalty_recipient`: Account into which the item royalties will be transfered.
		///
		/// Emits `RecipientItemRoyaltyChanged`.
		#[pallet::call_index(5)]
		#[pallet::weight(0)]
		pub fn transfer_item_royalty_recipient(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			new_royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;

			let item_royalties = <ItemWithRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;
			ensure!(item_royalties.royalty_recipient == caller, Error::<T>::NoPermission);

			ItemWithRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage: item_royalties.royalty_percentage,
					royalty_recipient: new_royalty_recipient.clone(),
				},
			);
			Self::deposit_event(Event::RecipientItemRoyaltyChanged {
				nft_collection: collection_id,
				nft: item_id,
				new_royalty_recipient,
			});

			Ok(())
		}

		/// Allows to buy an item if it's up for sale and pays the royalty associated to it.
		///
		/// Origin must be Signed and must not be the owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item the sender wants to buy.
		/// - `bid_price`: The price the sender is willing to pay.
		///
		/// Emits `RoyaltyPaid`.
		#[pallet::call_index(6)]
		#[pallet::weight(0)]
		pub fn buy(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			bid_price: ItemPrice<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			// Retrieve price of the item
			let item_price =
				T::Nfts::item_price(&collection_id, &item_id).ok_or(Error::<T>::NotForSale)?;

			// Buy the item within NFT pallet
			T::Nfts::buy_item(&collection_id, &item_id, &origin, &bid_price)?;

			// Item royalty supersedes collection royalty
			let item_royalty: RoyaltyDetails<T::AccountId>;
			if let Some(nft_item_royalty) = <ItemWithRoyalty<T>>::get((collection_id, item_id))  {
				item_royalty = nft_item_royalty;
			} else {
				item_royalty = <CollectionWithRoyalty<T>>::get(collection_id).ok_or(Error::<T>::NoRoyaltyExists)?;
			}

			// Transfer royalty to the royalty recipient or recipients, by default just the recipiend
			let mut royalties_recipients: BoundedVec<RoyaltyDetails<T::AccountId>, T::MaxRecipients> = 
				[
					RoyaltyDetails {
						royalty_percentage: Permill::one(),
						royalty_recipient: item_royalty.royalty_recipient
					}
				].to_vec().try_into().unwrap();

			// Item royalty recipients supersede collection royalty recipients
			// Get the item royalty recipients
			if let Some(recipients) = <ItemRoyaltyRecipients<T>>::get((collection_id, item_id))  {
				royalties_recipients = recipients;
			} else if let Some(recipients) = <CollectionRoyaltyRecipients<T>>::get(collection_id)  {
				royalties_recipients = recipients;
			}
			let royalty_amount_to_pay =  item_royalty.royalty_percentage * item_price;

			// Iterate to transfer to all the recipients
			for royalty_detail in royalties_recipients.iter_mut() {
				let individual_royalty_amount_to_pay =  royalty_detail.royalty_percentage * royalty_amount_to_pay;
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

		/// Remove the royalty associated to a collection only if the collection no longer exists.
		/// 
		/// This will also redeem the deposit initially paid for creating the collection royalty.
		/// If the royalty was set with `ForceOrigin` then no deposit will be redeemed.
		///
		/// Origin must be Signed and must be the owner of `CollectionWithRoyalty` or the `ForceOrigin`.
		///
		/// - `collection_id`: The `collection_id` that has an associated royalty that no longer exists.
		///
		/// Emits `CollectionRoyaltyRemoved`.
		#[pallet::call_index(7)]
		#[pallet::weight(0)]
		pub fn remove_collection_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
			.map(|_| None)
			.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;
		
			ensure!(
				T::Nfts::collections().any(|id| id == collection_id),
				Error::<T>::CollectionStillExists
			);

			if let Some(check_owner) = maybe_check_owner {
				ensure!(T::Nfts::collection_owner(&collection_id) == Some(check_owner.clone()), Error::<T>::NoPermission);
				let owner = &check_owner;
				T::Currency::unreserve(owner, T::CollectionRoyaltyDeposit::get());
			}

			// Delete the collection from `CollectionWithRoyalty`
			<CollectionWithRoyalty<T>>::remove(collection_id);

			// Delete the list of recipients from `CollectionRoyaltyRecipients`
			<CollectionRoyaltyRecipients<T>>::remove(collection_id);

			Self::deposit_event(Event::CollectionRoyaltyRemoved {
				nft_collection: collection_id,
			});

			Ok(())
		}

		/// Remove the royalty associated to an item only if the item no longer exists.
		/// 
		/// This will also redeem the deposit initially paid for creating the item royalty.
		/// If the royalty was set with `ForceOrigin` then no deposit will be redeemed.
		///
		/// Origin must be Signed and must be the owner of `ItemWithRoyalty` or the `ForceOrigin`.
		///
		/// - `collection_id`: The `collection_id` that the item belongs to.
		/// - `item_id`: The `item_id` that has an associated royalty that no longer exists.
		///
		/// Emits `ItemRoyaltyRemoved`.
		#[pallet::call_index(8)]
		#[pallet::weight(0)]
		pub fn remove_item_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
		) -> DispatchResult {
			let maybe_check_owner = T::ForceOrigin::try_origin(origin)
			.map(|_| None)
			.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			ensure!(
				T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftStillExists
			);

			if let Some(check_owner) = maybe_check_owner {
				ensure!(
					T::Nfts::owner(&collection_id, &item_id) == Some(check_owner.clone()),
					Error::<T>::NoPermission
				);
				let owner = &check_owner;
				T::Currency::unreserve(owner, T::CollectionRoyaltyDeposit::get());
			}

			// Delete the item from `ItemWithRoyalty`
			<ItemWithRoyalty<T>>::remove((collection_id, item_id));

			// Delete the list of recipients from `ItemRoyaltyRecipients`
			<ItemRoyaltyRecipients<T>>::remove((collection_id, item_id));

			Self::deposit_event(Event::ItemRoyaltyRemoved {
				nft_collection: collection_id,
				nft: item_id,
			});

			Ok(())
		}
	}

	

	impl<T: Config> Pallet<T> {
		// private functions
	}
}
