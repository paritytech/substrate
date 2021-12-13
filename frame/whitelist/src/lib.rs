// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! # Whitelist Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! Allow some configurable origin: [`Config::WhitelistOrigin`] to whitelist some hash of a call,
//! and allow another configurable origin: [`Config::DispatchWhitelistedOrigin`] to dispatch them
//! with the root origin.
//!
//! In the meantime the call corresponding to the hash must have been submitted to the to the
//! pre-image handler [`PreimageProvider`].

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use sp_runtime::traits::Dispatchable;
use sp_std::prelude::*;

use codec::{Decode, Encode, FullCodec, MaxEncodedLen};
use frame_support::{
	ensure,
	traits::{PreimageProvider, PreimageRecipient},
	weights::{GetDispatchInfo, PostDispatchInfo},
};
use scale_info::TypeInfo;
use weights::WeightInfo;

use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;

pub use pallet::*;

#[derive(Clone, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct Preimage<BoundedVec, Balance, AccountId> {
	preimage: BoundedVec,
	deposit: Option<(AccountId, Balance)>,
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching call type.
		type Call: IsType<<Self as frame_system::Config>::Call>
			+ Dispatchable<Origin = Self::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ FullCodec
			+ From<frame_system::Call<Self>>;

		/// Required origin for whitelisting a call.
		type WhitelistOrigin: EnsureOrigin<Self::Origin>;

		/// Required origin for dispatching whitelisted call with root origin.
		type DispatchWhitelistedOrigin: EnsureOrigin<Self::Origin>;

		/// The handler of pre-images.
		// NOTE: recipient is only needed for benchmarks.
		type PreimageProvider: PreimageProvider<Self::Hash> + PreimageRecipient<Self::Hash>;

		/// The weight information for this pallet.
		type WeightInfo: weights::WeightInfo;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::generate_storage_info]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CallWhitelisted { call_hash: T::Hash },
		WhitelistedCallRemoved { call_hash: T::Hash },
		WhitelistedCallDispatched { call_hash: T::Hash },
	}

	#[pallet::error]
	pub enum Error<T> {
		UnavailablePreImage,
		UndecodableCall,
		InvalidCallWeightWitness,
		CallIsNotWhitelisted,
		CallAlreadyWhitelisted,
	}

	#[pallet::storage]
	pub type WhitelistedCall<T: Config> = StorageMap<_, Twox64Concat, T::Hash, (), OptionQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(T::WeightInfo::whitelist_call())]
		pub fn whitelist_call(origin: OriginFor<T>, call_hash: T::Hash) -> DispatchResult {
			T::WhitelistOrigin::ensure_origin(origin)?;

			ensure!(
				!WhitelistedCall::<T>::contains_key(call_hash),
				Error::<T>::CallAlreadyWhitelisted,
			);

			WhitelistedCall::<T>::insert(call_hash, ());
			T::PreimageProvider::request_preimage(&call_hash);

			Self::deposit_event(Event::<T>::CallWhitelisted { call_hash });

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::remove_whitelisted_call())]
		pub fn remove_whitelisted_call(origin: OriginFor<T>, call_hash: T::Hash) -> DispatchResult {
			T::WhitelistOrigin::ensure_origin(origin)?;

			WhitelistedCall::<T>::take(call_hash).ok_or(Error::<T>::CallIsNotWhitelisted)?;

			T::PreimageProvider::unrequest_preimage(&call_hash);

			Self::deposit_event(Event::<T>::WhitelistedCallRemoved { call_hash });

			Ok(())
		}

		#[pallet::weight(
			T::WeightInfo::dispatch_whitelisted_call().saturating_add(*call_weight_witness)
		)]
		pub fn dispatch_whitelisted_call(
			origin: OriginFor<T>,
			call_hash: T::Hash,
			call_weight_witness: Weight,
		) -> DispatchResultWithPostInfo {
			T::DispatchWhitelistedOrigin::ensure_origin(origin)?;

			ensure!(
				WhitelistedCall::<T>::contains_key(call_hash),
				Error::<T>::CallIsNotWhitelisted,
			);

			let call = T::PreimageProvider::get_preimage(&call_hash)
				.ok_or(Error::<T>::UnavailablePreImage)?;

			let call = <T as Config>::Call::decode(&mut &call[..])
				.map_err(|_| Error::<T>::UndecodableCall)?;

			ensure!(
				call.get_dispatch_info().weight <= call_weight_witness,
				Error::<T>::InvalidCallWeightWitness
			);

			WhitelistedCall::<T>::remove(call_hash);

			T::PreimageProvider::unrequest_preimage(&call_hash);

			let result = call.dispatch(frame_system::Origin::<T>::Root.into());

			Self::deposit_event(Event::<T>::WhitelistedCallDispatched { call_hash });

			result
		}
	}
}
