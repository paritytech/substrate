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

#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::traits::{
	fungible::Inspect,
	tokens::{Balance, BalanceConversion},
};
use frame_system::WeightInfo;
use sp_runtime::{traits::Zero, FixedPointNumber, FixedPointOperand, FixedU128};

pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

// #[cfg(feature = "runtime-benchmarks")]
// mod benchmarking;

// Type alias for `frame_system`'s account id.
type AccountIdOf<T> = <T as frame_system::Config>::AccountId;
// This pallet's asset id and balance type.
type AssetIdOf<T> = <T as Config>::AssetId;
// Generic fungible balance type.
type BalanceOf<T> = <<T as Config>::Currency as Inspect<AccountIdOf<T>>>::Balance;

// TODO: Pallet description

// #[frame_support::pallet]
// TODO: Remove
#[frame_support::pallet(dev_mode)]
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
		type AssetId: Member + Parameter + Copy + MaybeSerializeDeserialize + MaxEncodedLen;
	}

	#[pallet::storage]
	#[pallet::getter(fn conversion_rate_to_native)]
	/// Maps an asset to its fixed point representation in the native balance.
	pub(super) type ConversionRateToNative<T: Config> =
		StorageMap<_, Blake2_128Concat, T::AssetId, FixedU128, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		// Some `asset_id` conversion rate was created.
		Created { asset_id: T::AssetId, rate: FixedU128 },
		// Some `asset_id` conversion rate was removed.
		Removed { asset_id: T::AssetId },
		// Some existing `asset_id` conversion rate was updated from `old` to `new`.
		Updated { asset_id: T::AssetId, old: FixedU128, new: FixedU128 },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The given asset ID is unknown.
		Unknown,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn create(
			origin: OriginFor<T>,
			asset_id: T::AssetId,
			rate: FixedU128,
		) -> DispatchResult {
			T::CreateOrigin::ensure_origin(origin)?;

			ConversionRateToNative::<T>::set(asset_id, Some(rate));

			Self::deposit_event(Event::Created { asset_id, rate });
			Ok(())
		}

		#[pallet::call_index(1)]
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
					Err(Error::<T>::Unknown)
				}
			})?;

			Self::deposit_event(Event::Updated { asset_id, old, new: rate });
			Ok(())
		}

		#[pallet::call_index(2)]
		pub fn remove(origin: OriginFor<T>, asset_id: T::AssetId) -> DispatchResult {
			T::RemoveOrigin::ensure_origin(origin)?;

			ensure!(ConversionRateToNative::<T>::contains_key(asset_id), Error::<T>::Unknown);
			ConversionRateToNative::<T>::remove(asset_id);

			Self::deposit_event(Event::Removed { asset_id });
			Ok(())
		}
	}
}

impl<T> BalanceConversion<BalanceOf<T>, AssetIdOf<T>, BalanceOf<T>> for Pallet<T>
where
	T: Config,
	BalanceOf<T>: FixedPointOperand + Zero,
{
	type Error = pallet::Error<T>;

	fn to_asset_balance(
		balance: BalanceOf<T>,
		asset_id: AssetIdOf<T>,
	) -> Result<BalanceOf<T>, pallet::Error<T>> {
		let rate = Pallet::<T>::conversion_rate_to_native(asset_id)
			.ok_or(pallet::Error::<T>::Unknown.into())?;
		Ok(rate.saturating_mul_int(balance))
	}
}
