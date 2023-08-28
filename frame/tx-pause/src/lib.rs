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
#![deny(rustdoc::broken_intra_doc_links)]

mod benchmarking;
pub mod mock;
mod tests;
pub mod weights;

use frame_support::{
	dispatch::GetDispatchInfo,
	pallet_prelude::*,
	traits::{CallMetadata, Contains, GetCallMetadata, IsSubType, IsType},
	DefaultNoBound,
};
use frame_system::pallet_prelude::*;
use sp_runtime::{traits::Dispatchable, DispatchResult};
use sp_std::{convert::TryInto, prelude::*};

pub use pallet::*;
pub use weights::*;

/// The stringy name of a pallet from [`GetCallMetadata`] for [`Config::RuntimeCall`] variants.
pub type PalletNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;

/// The stringy name of a call (within a pallet) from [`GetCallMetadata`] for
/// [`Config::RuntimeCall`] variants.
pub type PalletCallNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;

/// A fully specified pallet ([`PalletNameOf`]) and optional call ([`PalletCallNameOf`])
/// to partially or fully specify an item a variant of a  [`Config::RuntimeCall`].
pub type RuntimeCallNameOf<T> = (PalletNameOf<T>, PalletCallNameOf<T>);

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: Parameter
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin>
			+ GetDispatchInfo
			+ GetCallMetadata
			+ From<frame_system::Call<Self>>
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// The only origin that can pause calls.
		type PauseOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The only origin that can un-pause calls.
		type UnpauseOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Contains all calls that cannot be paused.
		///
		/// The `TxMode` pallet cannot pause its own calls, and does not need to be explicitly
		/// added here.
		type WhitelistedCalls: Contains<RuntimeCallNameOf<Self>>;

		/// Maximum length for pallet name and call name SCALE encoded string names.
		///
		/// TOO LONG NAMES WILL BE TREATED AS PAUSED.
		#[pallet::constant]
		type MaxNameLen: Get<u32>;

		// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	/// The set of calls that are explicitly paused.
	#[pallet::storage]
	pub type PausedCalls<T: Config> =
		StorageMap<_, Blake2_128Concat, RuntimeCallNameOf<T>, (), OptionQuery>;

	#[pallet::error]
	pub enum Error<T> {
		/// The call is paused.
		IsPaused,

		/// The call is unpaused.
		IsUnpaused,

		/// The call is whitelisted and cannot be paused.
		Unpausable,

		// The pallet or call does not exist in the runtime.
		NotFound,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// This pallet, or a specific call is now paused.
		CallPaused { full_name: RuntimeCallNameOf<T> },
		/// This pallet, or a specific call is now unpaused.
		CallUnpaused { full_name: RuntimeCallNameOf<T> },
	}

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	#[derive(DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		/// Initially paused calls.
		pub paused: Vec<RuntimeCallNameOf<T>>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			for call in &self.paused {
				Pallet::<T>::ensure_can_pause(&call).expect("Genesis data is known good; qed");
				PausedCalls::<T>::insert(&call, ());
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Pause a call.
		///
		/// Can only be called by [`Config::PauseOrigin`].
		/// Emits an [`Event::CallPaused`] event on success.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::pause())]
		pub fn pause(origin: OriginFor<T>, full_name: RuntimeCallNameOf<T>) -> DispatchResult {
			T::PauseOrigin::ensure_origin(origin)?;

			Self::do_pause(full_name).map_err(Into::into)
		}

		/// Un-pause a call.
		///
		/// Can only be called by [`Config::UnpauseOrigin`].
		/// Emits an [`Event::CallUnpaused`] event on success.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::unpause())]
		pub fn unpause(origin: OriginFor<T>, ident: RuntimeCallNameOf<T>) -> DispatchResult {
			T::UnpauseOrigin::ensure_origin(origin)?;

			Self::do_unpause(ident).map_err(Into::into)
		}
	}
}

impl<T: Config> Pallet<T> {
	pub(crate) fn do_pause(ident: RuntimeCallNameOf<T>) -> Result<(), Error<T>> {
		Self::ensure_can_pause(&ident)?;
		PausedCalls::<T>::insert(&ident, ());
		Self::deposit_event(Event::CallPaused { full_name: ident });

		Ok(())
	}

	pub(crate) fn do_unpause(ident: RuntimeCallNameOf<T>) -> Result<(), Error<T>> {
		Self::ensure_can_unpause(&ident)?;
		PausedCalls::<T>::remove(&ident);
		Self::deposit_event(Event::CallUnpaused { full_name: ident });

		Ok(())
	}

	/// Return whether this call is paused.
	pub fn is_paused(full_name: &RuntimeCallNameOf<T>) -> bool {
		if T::WhitelistedCalls::contains(full_name) {
			return false
		}

		<PausedCalls<T>>::contains_key(full_name)
	}

	/// Same as [`Self::is_paused`] but for inputs unbound by max-encoded-len.
	pub fn is_paused_unbound(pallet: Vec<u8>, call: Vec<u8>) -> bool {
		let pallet = PalletNameOf::<T>::try_from(pallet);
		let call = PalletCallNameOf::<T>::try_from(call);

		match (pallet, call) {
			(Ok(pallet), Ok(call)) => Self::is_paused(&(pallet, call)),
			_ => true,
		}
	}

	/// Ensure that this call can be paused.
	pub fn ensure_can_pause(full_name: &RuntimeCallNameOf<T>) -> Result<(), Error<T>> {
		// SAFETY: The `TxPause` pallet can never pause itself.
		if full_name.0.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return Err(Error::<T>::Unpausable)
		}

		if T::WhitelistedCalls::contains(&full_name) {
			return Err(Error::<T>::Unpausable)
		}
		if Self::is_paused(&full_name) {
			return Err(Error::<T>::IsPaused)
		}
		Ok(())
	}

	/// Ensure that this call can be un-paused.
	pub fn ensure_can_unpause(full_name: &RuntimeCallNameOf<T>) -> Result<(), Error<T>> {
		if Self::is_paused(&full_name) {
			// SAFETY: Everything that is paused, can be un-paused.
			Ok(())
		} else {
			Err(Error::IsUnpaused)
		}
	}
}

impl<T: pallet::Config> Contains<<T as frame_system::Config>::RuntimeCall> for Pallet<T>
where
	<T as frame_system::Config>::RuntimeCall: GetCallMetadata,
{
	/// Return whether the call is allowed to be dispatched.
	fn contains(call: &<T as frame_system::Config>::RuntimeCall) -> bool {
		let CallMetadata { pallet_name, function_name } = call.get_call_metadata();
		!Pallet::<T>::is_paused_unbound(pallet_name.into(), function_name.into())
	}
}

impl<T: Config> frame_support::traits::TransactionPause for Pallet<T> {
	type CallIdentifier = RuntimeCallNameOf<T>;

	fn is_paused(full_name: Self::CallIdentifier) -> bool {
		Self::is_paused(&full_name)
	}

	fn can_pause(full_name: Self::CallIdentifier) -> bool {
		Self::ensure_can_pause(&full_name).is_ok()
	}

	fn pause(
		full_name: Self::CallIdentifier,
	) -> Result<(), frame_support::traits::TransactionPauseError> {
		Self::do_pause(full_name).map_err(Into::into)
	}

	fn unpause(
		full_name: Self::CallIdentifier,
	) -> Result<(), frame_support::traits::TransactionPauseError> {
		Self::do_unpause(full_name).map_err(Into::into)
	}
}

impl<T: Config> From<Error<T>> for frame_support::traits::TransactionPauseError {
	fn from(err: Error<T>) -> Self {
		match err {
			Error::<T>::NotFound => Self::NotFound,
			Error::<T>::Unpausable => Self::Unpausable,
			Error::<T>::IsPaused => Self::AlreadyPaused,
			Error::<T>::IsUnpaused => Self::AlreadyUnpaused,
			_ => Self::Unknown,
		}
	}
}
