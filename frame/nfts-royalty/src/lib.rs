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
use sp_runtime::traits::StaticLookup;
pub use types::*;

/// The log target of this pallet.
pub const LOG_TARGET: &'static str = "runtime::nfts-royalty";

type AccountIdLookupOf<T> = <<T as SystemConfig>::Lookup as StaticLookup>::Source;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	// TODO: Probably a better way to do this than importing from pallet_nfts.
	use frame_system::pallet_prelude::*;
	use pallet_nfts::{ItemConfig, ItemSettings};
	use sp_std::fmt::Display;

	use frame_support::{
		pallet_prelude::*,
		sp_runtime::Permill,
		traits::{
			tokens::nonfungibles_v2::{
				Inspect as NonFungiblesInspect, InspectEnumerable as NonFungiblesInspectEnumerable,
				Mutate as NonFungiblesMutate, Buy as NonFungiblesBuy
			},
			ReservableCurrency, Currency, ExistenceRequirement
		},
	};
	pub type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
	pub type ItemPrice<T> = BalanceOf<T>;

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
			> + NonFungiblesMutate<Self::AccountId, ItemConfig>
			+ NonFungiblesInspectEnumerable<
				Self::AccountId,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			> 
			+ NonFungiblesBuy<
				Self::AccountId,
				ItemPrice<Self>,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			>;
	}

	/// The storage for NFT collections with a royalty
	#[pallet::storage]
	#[pallet::getter(fn nft_collection_with_royalty)]
	pub type NftCollectionWithRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::NftCollectionId,
		RoyaltyDetails<T::AccountId>,
		OptionQuery,
	>;

	/// The storage for NFT items with a royalty.
	#[pallet::storage]
	#[pallet::getter(fn nft_with_royalty)]
	pub type NftWithRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftItemId),
		RoyaltyDetails<T::AccountId>,
		OptionQuery,
	>;

	// Storage for multiple royalty recipients and the percentage of the royalty they receive.
	#[pallet::storage]
	#[pallet::getter(fn royalty_recipients)]
	pub type RoyaltyRecipients<T: Config> =
		StorageMap<_, Blake2_128Concat, T::NftCollectionId, Vec<(T::AccountId, Permill)>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// An NFT with royalty has been successfully minted.
		Minted {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		},
		/// An NFT item was destroyed.
		Burned { nft_collection: T::NftCollectionId, nft: T::NftItemId },
		/// The royalty recipient of an NFT item has changed.
		RecipientChanged {
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
		RoyaltyRecipientsCreated {
			nft_collection: T::NftCollectionId,
			royalty_recipients: Vec<(T::AccountId, Permill)>,
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
		InvalidRoyaltyPercentage
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Mint an item of a particular collection with a royalty.
		///
		/// The origin must be Signed and the sender must comply with the `mint_settings` rules.
		///
		/// - `collection`: The collection of the item to be minted.
		/// - `item`: An identifier of the new item.
		/// - `mint_to`: Account into which the item will be minted.
		/// - `item_settings`: The item's settings.
		///
		///
		/// Emits `Minted` event when successful.
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn mint(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			mint_to: AccountIdLookupOf<T>,
			item_settings: ItemSettings,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let mint_to = T::Lookup::lookup(mint_to)?;

			let item_config = ItemConfig { settings: item_settings };
			T::Nfts::mint_into(&collection_id, &item_id, &mint_to, &item_config, false)?;

			NftWithRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage,
					royalty_recipient: royalty_recipient.clone(),
				},
			);

			Self::deposit_event(Event::Minted {
				nft_collection: collection_id,
				nft: item_id,
				royalty_percentage,
				royalty_recipient: royalty_recipient.clone(),
			});

			Ok(())
		}

		/// Destroy a single item and delete the royalties associated to it.
		///
		/// The origin must conform to `ForceOrigin` or must be Signed and the signing account must
		/// be the owner of the `item`.
		///
		/// - `collection`: The collection of the item to be burned.
		/// - `item`: The item to be burned.
		///
		/// Emits `Burned`.
		///
		#[pallet::call_index(1)]
		#[pallet::weight(0)]
		pub fn burn(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?
				.unwrap();

			<NftWithRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;

			T::Nfts::burn(&collection_id, &item_id, Some(&maybe_check_origin))?;

			Self::deposit_event(Event::Burned {
				nft_collection: collection_id,
				nft: item_id,
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
		/// Emits `RecipientChanged`.
		///
		#[pallet::call_index(2)]
		#[pallet::weight(0)]
		pub fn transfer_royalty_recipient(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			new_royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let caller = ensure_signed(origin)?;

			let item_royalties = <NftWithRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;
			ensure!(item_royalties.royalty_recipient == caller, Error::<T>::NoPermission);

			NftWithRoyalty::<T>::insert(
				(collection_id, item_id),
				RoyaltyDetails::<T::AccountId> {
					royalty_percentage: item_royalties.royalty_percentage,
					royalty_recipient: new_royalty_recipient.clone(),
				},
			);
			Self::deposit_event(Event::RecipientChanged {
				nft_collection: collection_id,
				nft: item_id,
				new_royalty_recipient,
			});

			Ok(())
		}

		/// Set the royalties associated to an already existing item.
		///
		/// The origin must be the actual owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item to set the royalty.
		/// - `royalty_percentage`: Royalty percentage to be set.
		/// - `royalty_recipient`: Account into which the item royalties will be transfered.
		///
		/// Emits `RoyaltySet`.
		///
		#[pallet::call_index(3)]
		#[pallet::weight(0)]
		pub fn set_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			if let Some(check_origin) = maybe_check_origin {
				ensure!(
					T::Nfts::owner(&collection_id, &item_id) == Some(check_origin),
					Error::<T>::NoPermission
				);
			}

			ensure!(
				T::Nfts::items(&collection_id).any(|id| id == item_id),
				Error::<T>::NftDoesNotExist
			);

			// Check whether the item has already a royalty, if so do not allow to set it again
			ensure!(
				<NftWithRoyalty<T>>::get((collection_id, item_id)).is_none(),
				Error::<T>::RoyaltyAlreadyExists
			);

			NftWithRoyalty::<T>::insert(
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

		/// Set the royalty for an existing collection.
		///
		/// The origin must be the actual owner of the `item`.
		///
		/// - `collection`: The NFT collection.
		/// - `royalty_percentage`: Royalty percentage to be set.
		/// - `royalty_recipient`: Account into which the royalty will be sent to.
		///
		/// Emits `RoyaltySet`.
		///
		#[pallet::call_index(4)]
		#[pallet::weight(0)]
		pub fn set_collection_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?;

			if let Some(check_origin) = maybe_check_origin {
				todo!("Ensure owner of collection");
			}

			todo!("Ensure collection exists");

			// Set a royalty for the entire collection
			NftCollectionWithRoyalty::<T>::insert(
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

		/// Allows to buy an item if it's up for sale and pays the royalties associated to it.
		///
		/// Origin must be Signed and must not be the owner of the `item`.
		///
		/// - `collection`: The collection of the item.
		/// - `item`: The item the sender wants to buy.
		/// - `bid_price`: The price the sender is willing to pay.
		///
		/// Emits `RoyaltyPaid`.
		///
		#[pallet::call_index(5)]
		#[pallet::weight(0)]
		pub fn buy(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			bid_price: ItemPrice<T>,
		) -> DispatchResult {
			let origin = ensure_signed(origin)?;

			// Retrieve price of the item
			let item_price = T::Nfts::item_price(&collection_id, &item_id).ok_or(Error::<T>::NotForSale)?;

			// Buy the item within NFT pallet
			T::Nfts::buy_item(&collection_id, &item_id, &origin, &bid_price)?;

			// Pay the royalty to the royalty owner
			let item_royalty = <NftWithRoyalty<T>>::get((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;

			let royalty_amount_to_pay = item_royalty.royalty_percentage * item_price;

			T::Currency::transfer(
				&origin,
				&item_royalty.royalty_recipient,
				royalty_amount_to_pay,
				ExistenceRequirement::KeepAlive,
			)?;

			Self::deposit_event(Event::RoyaltyPaid {
				nft_collection: collection_id,
				nft: item_id,
				royalty_amount_paid: royalty_amount_to_pay,
				royalty_recipient: item_royalty.royalty_recipient,
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
		/// Emits `RoyaltyRecipientsCreated`.
		///
		#[pallet::call_index(6)]
		#[pallet::weight(0)]
		pub fn set_collection_royalty_recipients(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			recipients: Vec<(T::AccountId, Permill)>,
		) -> DispatchResult {
			let _origin = ensure_signed(origin)?;

			// TODO: Ensure that the collection exists

			// TODO: Ensure that the sender is the owner of the collection

			// Should we do this? Or should we allow to overwrite the recipients that way we have only one extrinsic for creating recipients and updating them.
			// Ensure that the collection does not have any royalty recipients yet
			ensure!(
				!RoyaltyRecipients::<T>::contains_key(&collection_id),
				Error::<T>::RoyaltyRecipientsAlreadyExist
			);

			// Ensure that the sum of the percentages is 100%
			let mut sum = Permill::zero();
			for (_, percentage) in recipients.iter() {
				sum = sum + *percentage;
			}
			ensure!(sum == Permill::one(), Error::<T>::InvalidRoyaltyPercentage);

			// Create royalty recipients
			RoyaltyRecipients::<T>::insert(&collection_id, recipients.clone());

			Self::deposit_event(Event::RoyaltyRecipientsCreated {
				nft_collection: collection_id,
				royalty_recipients: recipients.clone(),
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		// private functions
	}
}
