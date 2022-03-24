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
use sp_runtime::traits::{StaticLookup};

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::traits::{Currency, ReservableCurrency};
	use sp_runtime::traits::{CheckedAdd, One};

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Currency: ReservableCurrency<Self::AccountId>;

		type CollectionId: Member + Parameter + Default + Copy + MaxEncodedLen + CheckedAdd + One;

		type ItemId: Member + Parameter + Default + Copy + MaxEncodedLen + CheckedAdd + One;

		/// This is the limit for metadata
		type MetadataLimit: Get<u32>; // = up to 10 kb;

		type DefaultSystemConfig: Get<SystemFeatures>;

		/// The maximum length of an attribute key.
		#[pallet::constant]
		type AttributeKeyLimit: Get<u32>;

		/// The maximum length of an attribute value.
		#[pallet::constant]
		type AttributeValueLimit: Get<u32>;
	}

	pub type MetadataOf<T> = BoundedVec<u8, <T as Config>::MetadataLimit>;
	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	pub type AttributeKeyOf<T> = BoundedVec<u8, <T as Config>::AttributeKeyLimit>;
	pub type AttributeValueOf<T> = BoundedVec<u8, <T as Config>::AttributeValueLimit>;

	/// Maps a unique collection id to it's config.
	#[pallet::storage]
	pub(super) type CollectionConfigs<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionConfig,
	>;

	/// Maps a unique collection id to it's administrator.
	#[pallet::storage]
	pub(super) type Admins<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		T::AccountId,
		OptionQuery
	>;

	/// Maps a collection id to it's metadata.
	#[pallet::storage]
	pub(super) type Collections<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Collection<T::CollectionId, T::AccountId, BalanceOf<T>>,
		OptionQuery,
	>;

	/// Keeps track of the number of collections in existence.
	#[pallet::storage]
	pub(super) type CountForCollections<T: Config> = StorageValue<_, T::CollectionId, ValueQuery>;

	#[pallet::storage]
	/// Metadata of an collection.
	pub(super) type CollectionMetadataOf<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		CollectionMetadata<MetadataOf<T>>,
		OptionQuery,
	>;

	/// Maps a collection id to it's items.
	#[pallet::storage]
	pub(super) type Items<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		Item<T::ItemId, T::AccountId, BalanceOf<T>>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Metadata of an asset instance.
	pub(super) type ItemMetadataOf<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::CollectionId,
		Blake2_128Concat,
		T::ItemId,
		ItemMetadata<MetadataOf<T>>,
		OptionQuery,
	>;

	#[pallet::storage]
	/// Collection and items attributes.
	pub(super) type Attributes<T: Config> = StorageNMap<
		_,
		(
			NMapKey<Blake2_128Concat, T::CollectionId>,
			NMapKey<Blake2_128Concat, Option<T::ItemId>>,
			NMapKey<Blake2_128Concat, AttributeKeyOf<T>>,
		),
		AttributeValueOf<T>,
		OptionQuery,
	>;

	// Pallet's events.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CollectionCreated { id: T::CollectionId },
		CollectionMetadataSet { id: T::CollectionId, data: MetadataOf<T> },
		CollectionLocked { id: T::CollectionId },
		CollectionDestroyed { id: T::CollectionId },
		CollectionOwnerChanged { id: T::CollectionId, new_owner: T::AccountId },
		AttributeSet {
			id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
			value: AttributeValueOf<T>,
		},
		AttributeCleared {
			id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
		},
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
		/// The collection is locked.
		CollectionIsLocked,
		/// The calling user is not authorized to make this call.
		NotAuthorized,
		/// The hint provided by the user was incorrect.
		BadHint,
		/// An overflow has occurred.
		Overflow,
		/// Invalid witness data given.
		BadWitness,
	}

	// Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn create(
			origin: OriginFor<T>,
			config: UserFeatures,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_create_collection(sender, config)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn lock_collection(
			origin: OriginFor<T>,
			id: T::CollectionId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_lock_collection(id, sender, config)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn destroy_collection(
			origin: OriginFor<T>,
			id: T::CollectionId,
			witness: DestroyWitness,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_destroy_collection(id, sender, config, witness)?;
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn transfer_ownership(
			origin: OriginFor<T>,
			id: T::CollectionId,
			new_owner: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let new_owner = T::Lookup::lookup(new_owner)?;
			Self::do_transfer_ownership(id, sender, new_owner);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn set_attribute(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
			value: AttributeValueOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_set_attributes(sender, collection_id, maybe_item, key, value);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn clear_attribute(
			origin: OriginFor<T>,
			collection_id: T::CollectionId,
			maybe_item: Option<T::ItemId>,
			key: AttributeKeyOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			Self::do_clear_attribute(sender, collection_id, maybe_item, key);
			Ok(())
		}

		// BASIC METHODS:
		// +store collection's owner
		// +lock a collection (add isLocked flag) => applies to the initial metadata change and burn method
		//   +|- is_frozen vs. is_locked
		// +destroy collection => if is not locked
		// +transfer ownership

		// PART 2:
		// +collection metadata + attributes

		// PART 3:
		// +structure => will affect collection destruction
		// mint items
		// max supply => applies to mint
		// max items per user => applies to mint and transfer
		// isTransferable => applies to transfer
		// transfer items
		// items metadata + attributes. Metadata could be changed by the collection's owner only
		// burn item

		#[pallet::weight(0)]
		pub fn set_admin(
			origin: OriginFor<T>,
			id: T::CollectionId,
			new_admin: T::AccountId,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_admin(id, config, Some(sender), new_admin)?;
			Ok(())
		}

		// TODO: #[pallet::weight( Self::config_to_weight(config_hint) )]
		#[pallet::weight(0)]
		pub fn transfer(
			origin: OriginFor<T>,
			id: T::CollectionId,
			receiver: T::AccountId,
			config_hint: CollectionConfig,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			ensure!(config == config_hint, Error::<T>::BadHint);
			Self::do_transfer(id, config, sender, receiver, None)?;
			Ok(())
		}

		// set collection metadata
		#[pallet::weight(0)]
		pub fn set_collection_metadata(
			origin: OriginFor<T>,
			id: T::CollectionId,
			data: MetadataOf<T>,
		) -> DispatchResult {
			let sender = ensure_signed(origin)?;
			let config = CollectionConfigs::<T>::get(id).ok_or(Error::<T>::CollectionNotFound)?;
			Self::do_set_collection_metadata(id, config, sender, data)?;
			Ok(())
		}
	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {}
}
