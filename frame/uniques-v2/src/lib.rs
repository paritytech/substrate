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

#![cfg_attr(not(feature = "std"), no_std)]

mod types;
mod user_features;

pub use pallet::*;
pub use types::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type TokenId: Member + Parameter + Default + Copy + MaxEncodedLen;

		type DefaultSystemConfig: Get<SystemFeatures>;
	}

	/// Maps a unique token id to it's config.
	#[pallet::storage]
	pub(super) type TokenConfigs<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::TokenId,
		TokenConfig,
	>;

	/// Maps a unique token id to it's administrator.
	#[pallet::storage]
	pub(super) type Admins<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::TokenId,
		T::AccountId,
		OptionQuery,
	>;


	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		TokenCreated { id: T::TokenId }
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// The token is not configured to do this operation.
		NotConfigured,
		/// A token with this ID is already taken.
		TokenIdTaken,
		/// A token with this ID does not exist.
		TokenNotFound,
		/// The calling user is not authorized to make this call.
		NotAuthorized,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn create(origin: OriginFor<T>, id: T::TokenId, config: UserFeatures) -> DispatchResult {
			let _sender = ensure_signed(origin)?;
			ensure!(!TokenConfigs::<T>::contains_key(id), Error::<T>::TokenIdTaken);
			let default_system_config = T::DefaultSystemConfig::get();
			let config = TokenConfig {
				system_features: default_system_config,
				user_features: config,
			};
			TokenConfigs::<T>::insert(id, config);
			Self::deposit_event(Event::<T>::TokenCreated { id });
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_admin(origin: OriginFor<T>, id: T::TokenId, new_admin: T::AccountId) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = TokenConfigs::<T>::get(id).ok_or(Error::<T>::TokenNotFound)?;
			Self::do_set_admin(id, config, Some(sender), new_admin)?;
			Ok(())
		}
	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {}
}
