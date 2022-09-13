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

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;

use frame_support::{
	pallet_prelude::*,
	traits::{CallMetadata, Contains, GetCallMetadata},
};
use frame_system::pallet_prelude::*;
use sp_std::{convert::TryInto, prelude::*};

pub use pallet::*;

pub type PalletNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;
pub type FunctionNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The only origin that can pause calls.
		type PauseOrigin: EnsureOrigin<Self::Origin>;

		/// The only origin that can un-pause calls.
		type UnpauseOrigin: EnsureOrigin<Self::Origin>;

		/// Pallets that are safe and can never be paused.
		///
		/// The tx-pause pallet is always assumed to be safe itself.
		type UnpausablePallets: Contains<PalletNameOf<Self>>;

		/// Maximum length for pallet- and function-names.
		///
		/// Too long names will not be truncated but handled like
		/// [`Self::PauseTooLongNames`] specifies.
		#[pallet::constant]
		type MaxNameLen: Get<u32>;

		/// Specifies if functions and pallets with too long names should be treated as paused.
		///
		/// Setting this to `true` ensures that all calls that
		/// are callable, are also pause-able.
		/// Otherwise there could be a situation where a call
		/// is callable but not pause-able, which would could be exploited.
		#[pallet::constant]
		type PauseTooLongNames: Get<bool>;

		// Weight information for extrinsics in this pallet.
		//type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The call is (already or still) paused.
		IsPaused,

		/// The call is (already or still) unpaused.
		IsUnpaused,

		/// The call is listed as safe and cannot be paused.
		IsUnpausable,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// This call got paused.
		CallPaused(PalletNameOf<T>, FunctionNameOf<T>),
		/// This call got un-paused.
		CallUnpaused(PalletNameOf<T>, FunctionNameOf<T>),
	}

	/// The set of calls that are explicitly paused.
	#[pallet::storage]
	#[pallet::getter(fn paused_calls)]
	pub type PausedCalls<T: Config> =
		StorageMap<_, Blake2_128Concat, (PalletNameOf<T>, FunctionNameOf<T>), (), OptionQuery>;

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// The initially paused calls.
		pub paused: Vec<(PalletNameOf<T>, FunctionNameOf<T>)>,
		pub _phantom: PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		// NOTE: `derive(Default)` does not work together with `#[pallet::genesis_config]`.
		// We therefore need to add a trivial default impl.
		fn default() -> Self {
			Self { paused: Default::default(), _phantom: PhantomData }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			for (pallet, function) in &self.paused {
				PausedCalls::<T>::insert((pallet, function), ());
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Pause a call.
		///
		/// Can only be called by [`Config::PauseOrigin`].
		/// Emits an [`Event::CallPaused`] event on success.
		#[pallet::weight(0)]
		pub fn pause_call(
			origin: OriginFor<T>,
			pallet: PalletNameOf<T>,
			function: FunctionNameOf<T>,
		) -> DispatchResult {
			T::PauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_pause(&pallet, &function)?;
			PausedCalls::<T>::insert((&pallet, &function), ());
			Self::deposit_event(Event::CallPaused(pallet, function));

			Ok(())
		}

		/// Un-pause a call.
		///
		/// Can only be called by [`Config::UnpauseOrigin`].
		/// Emits an [`Event::CallUnpaused`] event on success.
		#[pallet::weight(0)]
		pub fn unpause_call(
			origin: OriginFor<T>,
			pallet: PalletNameOf<T>,
			function: FunctionNameOf<T>,
		) -> DispatchResult {
			T::UnpauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_unpause(&pallet, &function)?;
			PausedCalls::<T>::remove((&pallet, &function));
			Self::deposit_event(Event::CallUnpaused(pallet, function));

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return whether this call is paused.
	pub fn is_paused_unbound(pallet: Vec<u8>, function: Vec<u8>) -> bool {
		let pallet = PalletNameOf::<T>::try_from(pallet);
		let function = FunctionNameOf::<T>::try_from(function);

		match (pallet, function) {
			(Ok(pallet), Ok(function)) => Self::is_paused(&pallet, &function),
			_ => T::PauseTooLongNames::get(),
		}
	}

	/// Return whether this call is paused.
	pub fn is_paused(pallet: &PalletNameOf<T>, function: &FunctionNameOf<T>) -> bool {
		<PausedCalls<T>>::contains_key((pallet, function))
	}

	/// Ensure that this call can be paused.
	pub fn ensure_can_pause(
		pallet: &PalletNameOf<T>,
		function: &FunctionNameOf<T>,
	) -> Result<(), Error<T>> {
		// The `TxPause` pallet can never be paused.
		if pallet.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return Err(Error::<T>::IsUnpausable)
		}
		if T::UnpausablePallets::contains(&pallet) {
			return Err(Error::<T>::IsUnpausable)
		}
		if Self::is_paused(pallet, function) {
			return Err(Error::<T>::IsPaused)
		}
		Ok(())
	}

	/// Ensure that this call can be un-paused.
	pub fn ensure_can_unpause(
		pallet: &PalletNameOf<T>,
		function: &FunctionNameOf<T>,
	) -> Result<(), Error<T>> {
		if Self::is_paused(pallet, function) {
			// SAFETY: Everything that is paused, can be un-paused.
			Ok(())
		} else {
			Err(Error::IsUnpaused)
		}
	}
}

impl<T: pallet::Config> Contains<T::Call> for Pallet<T>
where
	<T as frame_system::Config>::Call: GetCallMetadata,
{
	/// Return whether the call is allowed to be dispatched.
	fn contains(call: &T::Call) -> bool {
		let CallMetadata { pallet_name, function_name } = call.get_call_metadata();
		!Pallet::<T>::is_paused_unbound(pallet_name.into(), function_name.into())
	}
}
