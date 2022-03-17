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

mod general_features;
mod types;
mod user_features;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod mock;

pub use pallet::*;
pub use types::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::traits::{Currency, ReservableCurrency};
	use sp_runtime::traits::Hash;

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId>;

		type CollectionId: Member + Parameter + Default + Copy + MaxEncodedLen;

		/// This is the limit for metadata
		type MetadataBound: Get<u32>; // = up to 10 kb;

		type DefaultSystemConfig: Get<SystemFeatures>;
	}

	pub type CollectionIdOf<T> = <T as frame_system::Config>::Hash;
	pub type MetadataOf<T> = BoundedVec<u8, <T as Config>::MetadataBound>;
	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

	/// Maps a unique collection id to it's config.
	#[pallet::storage]
	pub(super) type CollectionConfigs<T: Config> =
		StorageMap<_, Blake2_128Concat, CollectionIdOf<T>, CollectionConfig>;

	/// Maps a unique collection id to it's administrator.
	#[pallet::storage]
	pub(super) type Admins<T: Config> =
		StorageMap<_, Blake2_128Concat, CollectionIdOf<T>, T::AccountId, OptionQuery>;

	/// Maps a collection id to it's metadata.
	#[pallet::storage]
	pub(super) type Collections<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		CollectionIdOf<T>,
		Collection<CollectionIdOf<T>, T::AccountId, BalanceOf<T>, MetadataOf<T>>,
		OptionQuery,
	>;

	/// Maps a collection id to it's items.
	#[pallet::storage]
	pub(super) type CollectionMap<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		CollectionIdOf<T>,
		Blake2_128Concat,
		T::CollectionId,
		Item<T::CollectionId, T::AccountId, BalanceOf<T>, MetadataOf<T>>,
		OptionQuery,
	>;

	// Your Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CollectionCreated { id: CollectionIdOf<T> },
	}

	// Your Pallet's error messages.
	#[pallet::error]
	pub enum Error<T> {
		/// The collection is not configured to do this operation.
		NotConfigured,
		/// A collection with this ID is already taken.
		CollectionIdTaken,
		/// A collection with this ID does not exist.
		CollectionNotFound,
		/// The calling user is not authorized to make this call.
		NotAuthorized,
		/// The hint provided by the user was incorrect.
		BadHint,
	}

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn create(
			origin: OriginFor<T>,
			maybe_salt: Option<u64>,
			config: UserFeatures,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;

			let id = if let Some(salt) = maybe_salt {
				let bytes = (sender, salt).encode();
				T::Hashing::hash(&bytes)
			} else {
				// TODO update logic
				let bytes = sender.encode();
				T::Hashing::hash(&bytes)
			};

			ensure!(!CollectionConfigs::<T>::contains_key(id), Error::<T>::CollectionIdTaken);

			let default_system_config = T::DefaultSystemConfig::get();
			let config =
				CollectionConfig { system_features: default_system_config, user_features: config };
			CollectionConfigs::<T>::insert(id, config);
			Self::deposit_event(Event::<T>::CollectionCreated { id });
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_admin(
			origin: OriginFor<T>,
			id: CollectionIdOf<T>,
			new_admin: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_admin(id, config, Some(sender), new_admin)?;
			Ok(())
		}

		#[pallet::weight(
			0
			// todo
			//Self::config_to_weight(config_hint)
		)]
		pub fn transfer(
			origin: OriginFor<T>,
			id: CollectionIdOf<T>,
			receiver: T::AccountId,
			config_hint: CollectionConfig,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(config == config_hint, Error::<T>::BadHint);
			Self::do_transfer(id, config, sender, receiver, None)?;
			Ok(())
		}
	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {}
}
