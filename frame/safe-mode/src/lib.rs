// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Safe Mode Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Safe Mode pallet allows a chain to halt specified transactions for a period of time in case
//! some problem or vulnerability was found on the network which could cause problems.
//!
//! Safe mode can be enabled by any user, as long as they are willing to pay the costs required to
//! enable it. Returning funds for st
#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::DispatchResult;

use frame_support::traits::{Contains, Currency, LockableCurrency, ExistenceRequirement};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub use pallet::*;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

#[frame_support::pallet]
pub mod pallet {
	use super::{DispatchResult, *};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The default call filter that will be used by the chain when things are running normally.
		type BaseCallFilter: Contains<Self::Call>;

		/// The safe call filter that will be used by the chain when safe mode is enabled.
		type SafeModeCallFilter: Contains<Self::Call>;

		/// The currency mechanism.
		type Currency: LockableCurrency<Self::AccountId>;

		/// The amount of currency that needs to be "burned" to enable safe mode.
		type BurnAmount: Get<BalanceOf<Self>>;

		/// The location where burned funds go.
		type BurnDestination: Get<Self::AccountId>;

		/// An origin to disable safemode. Most often some governance.
		type DisableOrigin: EnsureOrigin<Self::Origin>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	/// The `AccountId` of the sudo key.
	#[pallet::storage]
	pub(super) type Enabled<T: Config> = StorageValue<_, bool, ValueQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Safe mode has just been enabled by a user.
		SafeModeEnabled { who: T::AccountId },
		/// Safe mode disabled.
		SafeModeDisabled,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			// TODO: Potentially disable safe mode after some period of time?
			0
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {

		/// Enable safemode
		#[pallet::weight(0)]
		pub fn enable_safemode(
			origin: OriginFor<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let burn_account = T::BurnDestination::get();
			let burn_amount = T::BurnAmount::get();

			T::Currency::transfer(&who, &burn_account, burn_amount, ExistenceRequirement::AllowDeath)?;

			Enabled::<T>::set(true);
			Self::deposit_event(Event::SafeModeEnabled { who });
			Ok(())
		}

		/// Disable safemode
		#[pallet::weight(0)]
		pub fn disable_safemode(
			origin: OriginFor<T>,
		) -> DispatchResult {
			T::DisableOrigin::ensure_origin(origin)?;
			Enabled::<T>::set(false);
			Self::deposit_event(Event::SafeModeDisabled);
			Ok(())
		}

	}
}

impl<T: Config> Contains<T::Call> for Pallet<T> {
	fn contains(call: &T::Call) -> bool {
		if Enabled::<T>::get() {
			T::SafeModeCallFilter::contains(call)
		} else {
			<T as Config>::BaseCallFilter::contains(call)
		}
	}
}
