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

//! * NFT Fractionalization pallet
//!
//! This pallet provides the basic functionality that should allow users
//! to leverage partial ownership, transfers, and sales, of illiquid assets,
//! whether real-world assets represented by their digital twins, or NFTs,
//! or original NFTs.
//!
//! The functionality allows a user to lock an NFT they own, create a new
//! fungible asset, and mint a set amount of tokens (`fractions`).
//!
//! It also allows the user to burn 100% of the asset and to unlock the NFT
//! into their account.
//!
//! ### Functions
//!
//! * `fractionalize`: lock the NFT, create and mint new asset.
//! * `unify`: return 100% of the asset, unlock the NFT.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod types;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;

pub mod weights;

use frame_system::Config as SystemConfig;
pub use pallet::*;
pub use scale_info::Type;
pub use types::*;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;
	use scale_info::prelude::{format, string::String};
	use sp_runtime::traits::{One, Zero};
	use sp_std::{fmt::Display, prelude::*};

	use frame_support::{
		dispatch::DispatchResult,
		pallet_prelude::*,
		sp_runtime::traits::{AccountIdConversion, StaticLookup},
		traits::{
			fungibles::{
				metadata::{CalcMetadataDeposit, Mutate as MutateMetadata},
				Create, Destroy, Inspect, Mutate,
			},
			tokens::{
				nonfungibles_v2::{Inspect as NonFungiblesInspect, Transfer},
				AssetId, Balance as AssetBalance,
			},
			Currency, ExistenceRequirement, ReservableCurrency,
		},
		BoundedVec, PalletId,
	};

	pub type AssetIdOf<T> =
		<<T as Config>::Assets as Inspect<<T as SystemConfig>::AccountId>>::AssetId;
	pub type AssetBalanceOf<T> =
		<<T as Config>::Assets as Inspect<<T as SystemConfig>::AccountId>>::Balance;
	pub type DepositOf<T> =
		<<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
	pub type AccountIdLookupOf<T> = <<T as SystemConfig>::Lookup as StaticLookup>::Source;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The currency mechanism, used for paying for deposits.
		type Currency: ReservableCurrency<Self::AccountId>;

		#[pallet::constant]
		type Deposit: Get<DepositOf<Self>>;

		/// Identifier for the collection of NFT.
		type NftCollectionId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// The type used to identify an NFT within a collection.
		type NftId: Member + Parameter + MaxEncodedLen + Copy + Display;

		/// The type used to describe the amount of fractions converted into assets.
		type AssetBalance: AssetBalance;

		/// The type used to identify the assets created during fractionalization.
		type AssetId: AssetId;

		/// Registry for the minted assets.
		type Assets: Inspect<Self::AccountId, AssetId = Self::AssetId, Balance = Self::AssetBalance>
			+ Create<Self::AccountId>
			+ Destroy<Self::AccountId>
			+ Mutate<Self::AccountId>
			+ MutateMetadata<Self::AccountId>
			+ CalcMetadataDeposit<<Self::Currency as Currency<Self::AccountId>>::Balance>;

		/// Registry for minted NFTs.
		type Nfts: NonFungiblesInspect<
				Self::AccountId,
				ItemId = Self::NftId,
				CollectionId = Self::NftCollectionId,
			> + Transfer<Self::AccountId>;

		/// The pallet's id, used for deriving its sovereign account ID.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// The newly created asset's symbol.
		#[pallet::constant]
		type NewAssetSymbol: Get<BoundedVec<u8, Self::StringLimit>>;

		/// The newly created asset's name.
		#[pallet::constant]
		type NewAssetName: Get<BoundedVec<u8, Self::StringLimit>>;

		/// The maximum length of a name or symbol stored on-chain.
		#[pallet::constant]
		type StringLimit: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// Keeps track of the corresponding NFT ID, asset ID and amount minted.
	#[pallet::storage]
	#[pallet::getter(fn nft_to_asset)]
	pub type NftToAsset<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		(T::NftCollectionId, T::NftId),
		Details<AssetIdOf<T>, AssetBalanceOf<T>, DepositOf<T>, T::AccountId>,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// An NFT was successfully fractionalized.
		NftFractionalized {
			nft_collection: T::NftCollectionId,
			nft: T::NftId,
			fractions: AssetBalanceOf<T>,
			asset: AssetIdOf<T>,
			beneficiary: T::AccountId,
		},
		/// An NFT was successfully returned back.
		NftUnified {
			nft_collection: T::NftCollectionId,
			nft: T::NftId,
			asset: AssetIdOf<T>,
			beneficiary: T::AccountId,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Asset ID does not correspond to locked NFT. 
		IncorrectAssetId,
		/// The signing account has no permission to do the operation.
		NoPermission,
		/// NFT doesn't exist.
		NftNotFound,
		/// NFT has not yet been fractionalised.
		NftNotFractionalized,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Lock the NFT and mint a new fungible asset.
		///
		/// The dispatch origin for this call must be Signed.
		/// The origin must be the owner of the NFT they are trying to lock.
		///
		/// `Deposit` funds of sender are reserved.
		///
		/// - `nft_collection_id`: The ID used to identify the collection of the NFT.
		/// Is used within the context of `pallet_nfts`.
		/// - `nft_id`: The ID used to identify the NFT within the given collection.
		/// Is used within the context of `pallet_nfts`.
		/// - `asset_id`: The ID of the new asset. It must not exist.
		/// Is used within the context of `pallet_assets`.
		/// - `beneficiary`: The account that will receive the newly created asset.
		/// - `fractions`: The amount to be minted of the newly created asset.
		///
		/// Emits `NftFractionalized` event when successful.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::fractionalize())]
		pub fn fractionalize(
			origin: OriginFor<T>,
			nft_collection_id: T::NftCollectionId,
			nft_id: T::NftId,
			asset_id: AssetIdOf<T>,
			beneficiary: AccountIdLookupOf<T>,
			fractions: AssetBalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			let nft_owner =
				T::Nfts::owner(&nft_collection_id, &nft_id).ok_or(Error::<T>::NftNotFound)?;
			ensure!(nft_owner == who, Error::<T>::NoPermission);

			let pallet_account = Self::get_pallet_account();
			let deposit = T::Deposit::get();
			T::Currency::reserve(&nft_owner, deposit)?;
			Self::do_lock_nft(nft_collection_id, nft_id)?;
			Self::do_create_asset(asset_id, pallet_account.clone())?;
			Self::do_mint_asset(asset_id, &beneficiary, fractions)?;
			Self::do_set_metadata(asset_id, &who, &pallet_account, &nft_collection_id, &nft_id)?;

			NftToAsset::<T>::insert(
				(nft_collection_id, nft_id),
				Details { asset: asset_id, fractions, asset_creator: nft_owner, deposit },
			);

			Self::deposit_event(Event::NftFractionalized {
				nft_collection: nft_collection_id,
				nft: nft_id,
				fractions,
				asset: asset_id,
				beneficiary,
			});

			Ok(())
		}

		/// Burn the whole amount of the asset and return back the locked NFT.
		///
		/// The dispatch origin for this call must be Signed.
		///
		/// `Deposit` funds will be returned to `asset_creator`.
		///
		/// - `nft_collection_id`: The ID used to identify the collection of the NFT.
		/// Is used within the context of `pallet_nfts`.
		/// - `nft_id`: The ID used to identify the NFT within the given collection.
		/// Is used within the context of `pallet_nfts`.
		/// - `asset_id`: The ID of the asset being returned and destroyed. Must match
		/// the original ID of the created asset, corresponding to the NFT.
		/// Is used within the context of `pallet_assets`.
		/// - `beneficiary`: The account that will receive the unified NFT.
		///
		/// Emits `NftUnified` event when successful.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::unify())]
		pub fn unify(
			origin: OriginFor<T>,
			nft_collection_id: T::NftCollectionId,
			nft_id: T::NftId,
			asset_id: AssetIdOf<T>,
			beneficiary: AccountIdLookupOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let beneficiary = T::Lookup::lookup(beneficiary)?;

			NftToAsset::<T>::try_mutate_exists((nft_collection_id, nft_id), |maybe_details| {
				let details = maybe_details.take().ok_or(Error::<T>::NftNotFractionalized)?;
				ensure!(details.asset == asset_id, Error::<T>::IncorrectAssetId);

				let deposit = details.deposit;
				let asset_creator = details.asset_creator;
				Self::do_burn_asset(asset_id, &who, details.fractions)?;
				Self::do_unlock_nft(nft_collection_id, nft_id, &beneficiary)?;
				T::Currency::unreserve(&asset_creator, deposit);

				Self::deposit_event(Event::NftUnified {
					nft_collection: nft_collection_id,
					nft: nft_id,
					asset: asset_id,
					beneficiary,
				});

				Ok(())
			})
		}
	}

	impl<T: Config> Pallet<T> {
		/// The account ID of the pallet.
		///
		/// This actually does computation. If you need to keep using it, then make sure you cache
		/// the value and only call this once.
		fn get_pallet_account() -> T::AccountId {
			T::PalletId::get().into_account_truncating()
		}

		/// Transfer the NFT from the account holding that NFT to the pallet's account.
		fn do_lock_nft(nft_collection_id: T::NftCollectionId, nft_id: T::NftId) -> DispatchResult {
			T::Nfts::lock(&nft_collection_id, &nft_id)
		}

		/// Transfer the NFT to the account returning the tokens.
		fn do_unlock_nft(
			nft_collection_id: T::NftCollectionId,
			nft_id: T::NftId,
			account: &T::AccountId,
		) -> DispatchResult {
			T::Nfts::unlock(&nft_collection_id, &nft_id)?;
			T::Nfts::transfer(&nft_collection_id, &nft_id, account)
		}

		/// Create the new asset.
		fn do_create_asset(asset_id: AssetIdOf<T>, admin: T::AccountId) -> DispatchResult {
			T::Assets::create(asset_id, admin, false, One::one())
		}

		/// Mint the `amount` of tokens with `asset_id` into the beneficiary's account.
		fn do_mint_asset(
			asset_id: AssetIdOf<T>,
			beneficiary: &T::AccountId,
			amount: AssetBalanceOf<T>,
		) -> DispatchResult {
			T::Assets::mint_into(asset_id, beneficiary, amount)
		}

		/// Burn tokens from the account.
		fn do_burn_asset(
			asset_id: AssetIdOf<T>,
			account: &T::AccountId,
			amount: AssetBalanceOf<T>,
		) -> DispatchResult {
			T::Assets::burn_from(asset_id, account, amount)?;
			T::Assets::start_destroy(asset_id, None)
		}

		/// Set the metadata for the newly created asset.
		fn do_set_metadata(
			asset_id: AssetIdOf<T>,
			depositor: &T::AccountId,
			pallet_account: &T::AccountId,
			nft_collection_id: &T::NftCollectionId,
			nft_id: &T::NftId,
		) -> DispatchResult {
			let name = format!("{} {nft_collection_id}-{nft_id}", String::from_utf8_lossy(&T::NewAssetName::get()));
			let symbol: &[u8] = &T::NewAssetSymbol::get();
			let deposit = T::Assets::calc(name.as_bytes(), symbol);


			if deposit != Zero::zero() {
				T::Currency::transfer(
					&depositor,
					&pallet_account,
					deposit,
					ExistenceRequirement::KeepAlive,
				)?;
			}
			T::Assets::set(asset_id, &pallet_account, name.into(), symbol.into(), 0)
		}
	}
}
