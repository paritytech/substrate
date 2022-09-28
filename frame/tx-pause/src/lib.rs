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

mod benchmarking;
#[cfg(test)]
pub mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use frame_support::{
	dispatch::GetDispatchInfo,
	pallet_prelude::*,
	traits::{CallMetadata, Contains, GetCallMetadata, IsSubType, IsType},
};
use frame_system::pallet_prelude::*;
use sp_runtime::{traits::Dispatchable, DispatchResult};
use sp_std::{convert::TryInto, prelude::*};

pub use pallet::*;
pub use weights::*;

pub type PalletNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;
pub type CallNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The overarching call type.
		type RuntimeCall: Parameter
			+ Dispatchable<Origin = Self::Origin>
			+ GetDispatchInfo
			+ GetCallMetadata
			+ From<frame_system::Call<Self>>
			+ IsSubType<Call<Self>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>;

		/// The only origin that can pause calls.
		type PauseOrigin: EnsureOrigin<Self::Origin>;

		/// The only origin that can un-pause calls.
		type UnpauseOrigin: EnsureOrigin<Self::Origin>;

		/// Contains all calls that cannot be paused.
		///
		/// The `TxMode` pallet cannot pause it's own calls, and does not need to be explicitly
		/// added here.
		type UnfilterableCalls: Contains<<Self as Config>::RuntimeCall>;

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
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The call is (already or still) paused.
		IsPaused,

		/// The call is (already or still) unpaused.
		IsUnpaused,

		/// The call is listed as safe and cannot be paused.
		IsUnpausable,

		/// The call has a name exceeds [`MaxNameLen`].
		IsTooLong,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// This call got paused.
		CallPaused(PalletNameOf<T>, CallNameOf<T>),
		/// This call got un-paused.
		CallUnpaused(PalletNameOf<T>, CallNameOf<T>),
	}

	/// The set of calls that are explicitly paused.
	#[pallet::storage]
	#[pallet::getter(fn paused_calls)]
	pub type PausedCalls<T: Config> =
		StorageMap<_, Blake2_128Concat, (PalletNameOf<T>, CallNameOf<T>), (), OptionQuery>;

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// The initially paused calls.
		pub paused: Vec<(PalletNameOf<T>, CallNameOf<T>)>,
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
		#[pallet::weight(T::WeightInfo::pause_call())]
		pub fn pause_call(
			origin: OriginFor<T>,
			c: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResult {
			T::PauseOrigin::ensure_origin(origin)?;

			let (pallet, call) = Self::try_get_bounded_names(&c)?;

			Self::ensure_can_pause(&c)?;
			PausedCalls::<T>::insert((&pallet, &call), ());
			Self::deposit_event(Event::CallPaused(pallet, call));

			Ok(())
		}

		// TODO add preset pause functionality (set of calls) See proxy and ProyType in node runtime
		// pub fn pause_preset(
		// 	origin: OriginFor<T>,
		// 	preset: PausePresets,
		// ) {
		// 	loop
		// 		do_pause_call() // run over a pre-config vec of calls for each type of PausePreset
		// 		// we can use the same storage, a vec of all paused calls.
		// }

		/// Un-pause a call.
		///
		/// Can only be called by [`Config::UnpauseOrigin`].
		/// Emits an [`Event::CallUnpaused`] event on success.
		#[pallet::weight(T::WeightInfo::unpause_call())]
		pub fn unpause_call(
			origin: OriginFor<T>,
			c: Box<<T as Config>::RuntimeCall>,
		) -> DispatchResult {
			T::UnpauseOrigin::ensure_origin(origin)?;

			let (pallet, call) = Self::try_get_bounded_names(&c)?;

			Self::ensure_can_unpause(&c)?;
			PausedCalls::<T>::remove((&pallet, &call));
			Self::deposit_event(Event::CallUnpaused(pallet, call));

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return whether this call is paused.
	pub fn is_paused_unbound(pallet: Vec<u8>, call: Vec<u8>) -> bool {
		let pallet = PalletNameOf::<T>::try_from(pallet);
		let call = CallNameOf::<T>::try_from(call);

		match (pallet, call) {
			(Ok(pallet), Ok(call)) => Self::is_paused(&pallet, &call),
			_ => T::PauseTooLongNames::get(),
		}
	}

	/// Return whether this call is paused.
	pub fn is_paused(pallet: &PalletNameOf<T>, call: &CallNameOf<T>) -> bool {
		<PausedCalls<T>>::contains_key((pallet, call))
	}

	/// Ensure that this call can be paused.
	pub fn ensure_can_pause(c: &<T as Config>::RuntimeCall) -> Result<(), Error<T>> {
		let (pallet, call) = Self::try_get_bounded_names(&c)?;

		// The `TxPause` pallet can never be paused.
		if pallet == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return Err(Error::<T>::IsUnpausable)
		}
		if T::UnfilterableCalls::contains(c) {
			return Err(Error::<T>::IsUnpausable)
		}
		if Self::is_paused(&pallet, &call) {
			return Err(Error::<T>::IsPaused)
		}
		Ok(())
	}

	/// Ensure that this call can be un-paused.
	pub fn ensure_can_unpause(c: &<T as Config>::RuntimeCall) -> Result<(), Error<T>> {
		let (pallet, call) = Self::try_get_bounded_names(&c)?;

		if Self::is_paused(&pallet, &call) {
			// SAFETY: Everything that is paused, can be un-paused.
			Ok(())
		} else {
			Err(Error::IsUnpaused)
		}
	}

	/// Get bounded names of calls in pallets from runtime call.
	pub fn try_get_bounded_names(
		c: &<T as Config>::RuntimeCall,
	) -> Result<(PalletNameOf<T>, CallNameOf<T>), Error<T>>
	where
		<T as Config>::RuntimeCall: GetCallMetadata,
	{
		let CallMetadata { pallet_name, function_name } = c.get_call_metadata();

		let pallet = PalletNameOf::<T>::try_from(pallet_name.as_bytes().to_vec());
		let call = CallNameOf::<T>::try_from(function_name.as_bytes().to_vec());

		match (pallet, call) {
			(Ok(pallet), Ok(call)) => Ok((pallet, call)),
			_ => Err(Error::IsTooLong), /* TODO consider better method than custom error just for
			                             * this? */
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
