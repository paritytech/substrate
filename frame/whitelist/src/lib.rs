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
//! In the meantime the call corresponding to the hash must have been submitted to the pre-image
//! handler [`pallet::Config::Preimages`].

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;
pub use weights::WeightInfo;

use codec::{DecodeLimit, Encode, FullCodec};
use frame_support::{
	dispatch::{GetDispatchInfo, PostDispatchInfo},
	ensure,
	traits::{Hash as PreimageHash, QueryPreimage, StorePreimage},
	weights::Weight,
	Hashable,
};
use scale_info::TypeInfo;
use sp_runtime::traits::Dispatchable;
use sp_std::prelude::*;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: IsType<<Self as frame_system::Config>::RuntimeCall>
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ FullCodec
			+ TypeInfo
			+ From<frame_system::Call<Self>>
			+ Parameter;

		/// Required origin for whitelisting a call.
		type WhitelistOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Required origin for dispatching whitelisted call with root origin.
		type DispatchWhitelistedOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The handler of pre-images.
		type Preimages: QueryPreimage + StorePreimage;

		/// The weight information for this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CallWhitelisted { call_hash: PreimageHash },
		WhitelistedCallRemoved { call_hash: PreimageHash },
		WhitelistedCallDispatched { call_hash: PreimageHash, result: DispatchResultWithPostInfo },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The preimage of the call hash could not be loaded.
		UnavailablePreImage,
		/// The call could not be decoded.
		UndecodableCall,
		/// The weight of the decoded call was higher than the witness.
		InvalidCallWeightWitness,
		/// The call was not whitelisted.
		CallIsNotWhitelisted,
		/// The call was already whitelisted; No-Op.
		CallAlreadyWhitelisted,
	}

	#[pallet::storage]
	pub type WhitelistedCall<T: Config> =
		StorageMap<_, Twox64Concat, PreimageHash, (), OptionQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(T::WeightInfo::whitelist_call())]
		pub fn whitelist_call(origin: OriginFor<T>, call_hash: PreimageHash) -> DispatchResult {
			T::WhitelistOrigin::ensure_origin(origin)?;

			ensure!(
				!WhitelistedCall::<T>::contains_key(call_hash),
				Error::<T>::CallAlreadyWhitelisted,
			);

			WhitelistedCall::<T>::insert(call_hash, ());
			T::Preimages::request(&call_hash);

			Self::deposit_event(Event::<T>::CallWhitelisted { call_hash });

			Ok(())
		}

		#[pallet::weight(T::WeightInfo::remove_whitelisted_call())]
		pub fn remove_whitelisted_call(
			origin: OriginFor<T>,
			call_hash: PreimageHash,
		) -> DispatchResult {
			T::WhitelistOrigin::ensure_origin(origin)?;

			WhitelistedCall::<T>::take(call_hash).ok_or(Error::<T>::CallIsNotWhitelisted)?;

			T::Preimages::unrequest(&call_hash);

			Self::deposit_event(Event::<T>::WhitelistedCallRemoved { call_hash });

			Ok(())
		}

		#[pallet::weight(
			T::WeightInfo::dispatch_whitelisted_call(*call_encoded_len)
				.saturating_add(*call_weight_witness)
		)]
		pub fn dispatch_whitelisted_call(
			origin: OriginFor<T>,
			call_hash: PreimageHash,
			call_encoded_len: u32,
			call_weight_witness: Weight,
		) -> DispatchResultWithPostInfo {
			T::DispatchWhitelistedOrigin::ensure_origin(origin)?;

			ensure!(
				WhitelistedCall::<T>::contains_key(call_hash),
				Error::<T>::CallIsNotWhitelisted,
			);

			let call = T::Preimages::fetch(&call_hash, Some(call_encoded_len))
				.map_err(|_| Error::<T>::UnavailablePreImage)?;

			let call = <T as Config>::RuntimeCall::decode_all_with_depth_limit(
				sp_api::MAX_EXTRINSIC_DEPTH,
				&mut &call[..],
			)
			.map_err(|_| Error::<T>::UndecodableCall)?;

			ensure!(
				call.get_dispatch_info().weight.all_lte(call_weight_witness),
				Error::<T>::InvalidCallWeightWitness
			);

			let actual_weight = Self::clean_and_dispatch(call_hash, call).map(|w| {
				w.saturating_add(T::WeightInfo::dispatch_whitelisted_call(call_encoded_len))
			});

			Ok(actual_weight.into())
		}

		#[pallet::weight({
			let call_weight = call.get_dispatch_info().weight;
			let call_len = call.encoded_size() as u32;

			T::WeightInfo::dispatch_whitelisted_call_with_preimage(call_len)
				.saturating_add(call_weight)
		})]
		pub fn dispatch_whitelisted_call_with_preimage(
			origin: OriginFor<T>,
			call: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResultWithPostInfo {
			T::DispatchWhitelistedOrigin::ensure_origin(origin)?;

			let call_hash = call.blake2_256().into();

			ensure!(
				WhitelistedCall::<T>::contains_key(call_hash),
				Error::<T>::CallIsNotWhitelisted,
			);

			let call_len = call.encoded_size() as u32;
			let actual_weight = Self::clean_and_dispatch(call_hash, *call).map(|w| {
				w.saturating_add(T::WeightInfo::dispatch_whitelisted_call_with_preimage(call_len))
			});

			Ok(actual_weight.into())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Clean whitelisting/preimage and dispatch call.
	///
	/// Return the call actual weight of the dispatched call if there is some.
	fn clean_and_dispatch(
		call_hash: PreimageHash,
		call: <T as Config>::RuntimeCall,
	) -> Option<Weight> {
		WhitelistedCall::<T>::remove(call_hash);

		T::Preimages::unrequest(&call_hash);

		let result = call.dispatch(frame_system::Origin::<T>::Root.into());

		let call_actual_weight = match result {
			Ok(call_post_info) => call_post_info.actual_weight,
			Err(call_err) => call_err.post_info.actual_weight,
		};

		Self::deposit_event(Event::<T>::WhitelistedCallDispatched { call_hash, result });

		call_actual_weight
	}
}
