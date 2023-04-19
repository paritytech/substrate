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
				Mutate as NonFungiblesMutate,
			},
			ReservableCurrency,
		},
	};

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

		/// Identifier for the collection of NFT.
		type NftCollectionId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// The type used to identify an NFT within a collection.
		type NftItemId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// Registry for minted NFTs.
		type Nfts: NonFungiblesInspect<
				Self::AccountId,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			> + NonFungiblesMutate<Self::AccountId, ItemConfig>
			+ NonFungiblesInspectEnumerable<
				Self::AccountId,
				ItemId = Self::NftItemId,
				CollectionId = Self::NftCollectionId,
			>;
	}

	/// The storage for NFTs with a royalty.
	#[pallet::storage]
	#[pallet::getter(fn nft_with_royalty)]
	pub type NftWithRoyalty<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftItemId),
		RoyaltyDetails<T::AccountId>,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// An NFT royalty was successfully created.
		NftRoyaltyCreated {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
		},
		/// An NFT royalty was destroyed.
		NftRoyaltyBurned { nft_collection: T::NftCollectionId, nft: T::NftItemId },
		/// The NFT royalty whas been transfered.
		NftRoyaltyTransfered {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			new_royalty_recipient: T::AccountId,
		},
		/// The NFT royalty percentage of an existing NFT item was set.
		NftRoyaltySet {
			nft_collection: T::NftCollectionId,
			nft: T::NftItemId,
			royalty_percentage: Permill,
			royalty_recipient: T::AccountId,
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
		/// Emits `NftRoyaltyCreated` event when successful.
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn mint_item_with_royalty(
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

			Self::deposit_event(Event::NftRoyaltyCreated {
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
		pub fn burn_item_with_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
		) -> DispatchResult {
			let maybe_check_origin = T::ForceOrigin::try_origin(origin)
				.map(|_| None)
				.or_else(|origin| ensure_signed(origin).map(Some).map_err(DispatchError::from))?
				.unwrap();

			// TODO: Decide if throws an error if has not royalties or just burn it
			<NftWithRoyalty<T>>::take((collection_id, item_id))
				.ok_or(Error::<T>::NoRoyaltyExists)?;

			T::Nfts::burn(&collection_id, &item_id, Some(&maybe_check_origin))?;

			Self::deposit_event(Event::NftRoyaltyBurned {
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
		/// Emits `NftRoyaltyTransfered`.
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
			Self::deposit_event(Event::NftRoyaltyTransfered {
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
		/// Emits `NftRoyaltyTransfered`.
		///
		#[pallet::call_index(3)]
		#[pallet::weight(0)]
		pub fn set_item_with_royalty(
			origin: OriginFor<T>,
			collection_id: T::NftCollectionId,
			item_id: T::NftItemId,
			item_settings: ItemSettings,
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
			let item_config = ItemConfig { settings: item_settings };
			// TODO: Not sure how to check if an item exists
			// Use Inspect Enumberable
			// ensure!(T::Nfts::items(&collection_id).find(|id| id == item_id), Error::<T>::NftDoesNotExist);

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

			Self::deposit_event(Event::NftRoyaltySet {
				nft_collection: collection_id,
				nft: item_id,
				royalty_percentage,
				royalty_recipient: royalty_recipient.clone(),
			});

			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		// private functions
	}
}
