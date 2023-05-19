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
//! # Dev Mode Example Pallet
//!
//! A simple example of a FRAME pallet demonstrating
//! the ease of requirements for a pallet in dev mode.
//!
//! Run `cargo doc --package pallet-dev-mode --open` to view this pallet's documentation.
//!
//! **Dev mode is not meant to be used in production.**

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::dispatch::DispatchResult;
use frame_system::ensure_signed;

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;

#[cfg(test)]
mod tests;

/// A type alias for the balance type from this pallet's point of view.
type BalanceOf<T> = <T as pallet_balances::Config>::Balance;

/// Enable `dev_mode` for this pallet.
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
		/// No need to define a `weight` attribute here because of `dev_mode`.
		pub fn add_dummy(origin: OriginFor<T>, id: T::AccountId) -> DispatchResult {
			ensure_root(origin)?;

			if let Some(mut dummies) = Dummy::<T>::get() {
				dummies.push(id.clone());
				Dummy::<T>::set(Some(dummies));
			} else {
				Dummy::<T>::set(Some(vec![id.clone()]));
			}

			// Let's deposit an event to let the outside world know this happened.
			Self::deposit_event(Event::AddDummy { account: id });

			Ok(())
		}

		#[pallet::call_index(1)]
		/// No need to define a `weight` attribute here because of `dev_mode`.
		pub fn set_bar(
			origin: OriginFor<T>,
			#[pallet::compact] new_value: T::Balance,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			// Put the new value into storage.
			<Bar<T>>::insert(&sender, new_value);

			Self::deposit_event(Event::SetBar { account: sender, balance: new_value });

			Ok(())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		AddDummy { account: T::AccountId },
		SetBar { account: T::AccountId, balance: BalanceOf<T> },
	}

	/// The MEL requirement for bounded pallets is skipped by `dev_mode`.
	/// This means that all storages are marked as unbounded.
	/// This is equivalent to specifying `#[pallet::unbounded]` on this type definitions.
	/// When the dev_mode is removed, we would need to implement implement `MaxEncodedLen`.
	#[pallet::storage]
	pub type Dummy<T: Config> = StorageValue<_, Vec<T::AccountId>>;

	/// The Hasher requirement is skipped by `dev_mode`. So, second parameter can be `_`
	/// and `Blake2_128Concat` is used as a default.
	/// When the dev_mode is removed, we would need to specify the hasher like so:
	/// `pub type Bar<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, T::Balance>;`.
	#[pallet::storage]
	pub type Bar<T: Config> = StorageMap<_, _, T::AccountId, T::Balance>;
}
