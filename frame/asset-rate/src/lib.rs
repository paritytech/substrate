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

//! # Asset Rate Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The AssetRate pallet provides means of setting conversion rates for some asset to native
//! balance.
//!
//! The supported dispatchable functions are documented in the [`Call`] enum.
//!
//! ### Terminology
//!
//! * **Asset balance**: The balance type of an arbitrary asset. The network might only know about
//!   the identifier of the asset and nothing more.
//! * **Native balance**: The balance type of the network's native currency.
//!
//! ### Goals
//!
//! The asset-rate system in Substrate is designed to make the following possible:
//!
//! * Providing a soft conversion for the balance of supported assets to a default asset class.
//! * Updating existing conversion rates.
//!
//! ## Interface
//!
//! ### Permissioned Functions
//!
//! * `create`: Creates a new asset conversion rate.
//! * `remove`: Removes an existing asset conversion rate.
//! * `update`: Overwrites an existing assert conversion rate.
//!
//! Please refer to the [`Call`] enum and its associated variants for documentation on each
//! function.
//!
//! ### Assumptions
//!
//! * Conversion rates are only used as estimates, and are not designed to be precise or closely
//!   tracking real world values.
//! * All conversion rates reflect the ration of some asset to native, e.g. native = asset * rate.

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::{
	fungible::Inspect,
	tokens::{Balance, ConversionFromAssetBalance},
};
use sp_runtime::{traits::Zero, FixedPointNumber, FixedPointOperand, FixedU128};

pub use pallet::*;
pub use weights::WeightInfo;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

// Type alias for `frame_system`'s account id.
type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
// This pallet's asset id and balance type.
type AssetIdOf<T> = <T as Config>::AssetId;
// Generic fungible balance type.
type BalanceOf<T> = <<T as Config>::Currency as Inspect<AccountIdOf<T>>>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The runtime event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The origin permissioned to create a conversion rate for an asset.
		type CreateOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin permissioned to remove an existing conversion rate for an asset.
		type RemoveOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The origin permissioned to update an existiing conversion rate for an asset.
		type UpdateOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The units in which we record balances.
		type Balance: Balance + FixedPointOperand;

		/// The currency mechanism for this pallet.
		type Currency: Inspect<Self::AccountId, Balance = Self::Balance>;

		/// The identifier for the class of asset.
		type AssetId: frame_support::traits::tokens::AssetId;
	}

	/// Maps an asset to its fixed point representation in the native balance.
	///
	/// E.g. `native_amount = asset_amount * ConversionRateToNative::<T>::get(asset_id)`
	#[pallet::storage]
	pub type ConversionRateToNative<T: Config> =
		StorageMap<_, Blake2_128Concat, T::AssetId, FixedU128, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		// Some `asset_id` conversion rate was created.
		AssetRateCreated { asset_id: T::AssetId, rate: FixedU128 },
		// Some `asset_id` conversion rate was removed.
		AssetRateRemoved { asset_id: T::AssetId },
		// Some existing `asset_id` conversion rate was updated from `old` to `new`.
		AssetRateUpdated { asset_id: T::AssetId, old: FixedU128, new: FixedU128 },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The given asset ID is unknown.
		UnknownAssetId,
		/// The given asset ID already has an assigned conversion rate and cannot be re-created.
		AlreadyExists,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Initialize a conversion rate to native balance for the given asset.
		///
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::create())]
		pub fn create(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			rate: FixedU128,
		) -> DispatchResult {
			T::CreateOrigin::ensure_origin(origin)?;

			ensure!(
				!ConversionRateToNative::<T>::contains_key(asset_id),
				Error::<T>::AlreadyExists
			);
			ConversionRateToNative::<T>::set(asset_id, Some(rate));

			Self::deposit_event(Event::AssetRateCreated { asset_id, rate });
			Ok(())
		}

		/// Update the conversion rate to native balance for the given asset.
		///
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::update())]
		pub fn update(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			rate: FixedU128,
		) -> DispatchResult {
			T::UpdateOrigin::ensure_origin(origin)?;

			let mut old = FixedU128::zero();
			ConversionRateToNative::<T>::mutate(asset_id, |maybe_rate| {
				if let Some(r) = maybe_rate {
					old = *r;
					*r = rate;

					Ok(())
				} else {
					Err(Error::<T>::UnknownAssetId)
				}
			})?;

			Self::deposit_event(Event::AssetRateUpdated { asset_id, old, new: rate });
			Ok(())
		}

		/// Remove an existing conversion rate to native balance for the given asset.
		///
		/// ## Complexity
		/// - O(1)
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::remove())]
		pub fn remove(origin: OriginFor<T>, asset_id: T::AssetId) -> DispatchResult {
			T::RemoveOrigin::ensure_origin(origin)?;

			ensure!(
				ConversionRateToNative::<T>::contains_key(asset_id),
				Error::<T>::UnknownAssetId
			);
			ConversionRateToNative::<T>::remove(asset_id);

			Self::deposit_event(Event::AssetRateRemoved { asset_id });
			Ok(())
		}
	}
}

/// Exposes conversion of an arbitrary balance of an asset to native balance.
impl<T> ConversionFromAssetBalance<BalanceOf<T>, AssetIdOf<T>, BalanceOf<T>> for Pallet<T>
where
	T: Config,
	BalanceOf<T>: FixedPointOperand + Zero,
{
	type Error = pallet::Error<T>;

	fn from_asset_balance(
		balance: BalanceOf<T>,
		asset_id: AssetIdOf<T>,
	) -> Result<BalanceOf<T>, pallet::Error<T>> {
		let rate = pallet::ConversionRateToNative::<T>::get(asset_id)
			.ok_or(pallet::Error::<T>::UnknownAssetId.into())?;
		Ok(rate.saturating_mul_int(balance))
	}
}
