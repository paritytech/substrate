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

//! <!-- markdown-link-check-disable -->
//! # Default Config Pallet Example
//!
//! A simple example of a FRAME pallet that utilizes [`frame_support::derive_impl`] to
//! implement a `DefaultConfig` for testing purposes.
//!
//! See the source code for `tests.rs` to see the relevant
//! [`derive_impl`](`frame_support::derive_impl`) example.
//!
//! Note that this pallet makes use of `dev_mode` for ease of use, since the point of this
//! example is the tests, not the pallet itself. See `pallet-dev-mode` for a more detailed
//! example of the capabilities of `dev_mode`.

// Ensure we're `no_std` when compiling for WASM.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::dispatch::DispatchResult;
use frame_system::ensure_signed;

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;

#[cfg(test)]
mod tests;

/// A type alias for the balance type from this pallet's point of view.
type BalanceOf<T> = <T as pallet_balances::Config>::Balance;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: pallet_balances::Config + frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	// Simple declaration of the `Pallet` type. It is placeholder we use to implement traits and
	// method.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn add_person(origin: OriginFor<T>, id: T::AccountId) -> DispatchResult {
			ensure_root(origin)?;

			if let Some(mut people) = People::<T>::get() {
				people.push(id.clone());
				People::<T>::set(Some(people));
			} else {
				People::<T>::set(Some(vec![id.clone()]));
			}

			// Let's deposit an event to let the outside world know this happened.
			Self::deposit_event(Event::AddPeople { account: id });

			Ok(())
		}

		#[pallet::call_index(1)]
		pub fn set_points(
			origin: OriginFor<T>,
			#[pallet::compact] new_value: T::Balance,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			// Put the new value into storage.
			<Points<T>>::insert(&sender, new_value);

			Self::deposit_event(Event::SetPoints { account: sender, balance: new_value });

			Ok(())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		AddPeople { account: T::AccountId },
		SetPoints { account: T::AccountId, balance: BalanceOf<T> },
	}

	#[pallet::storage]
	pub type People<T: Config> = StorageValue<_, Vec<T::AccountId>>;

	#[pallet::storage]
	pub type Points<T: Config> = StorageMap<_, _, T::AccountId, T::Balance>;
}
