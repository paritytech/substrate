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
pub type FullNameOf<T> = (PalletNameOf<T>, Option<CallNameOf<T>>);

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
		type UnfilterableCallNames: Contains<FullNameOf<Self>>;

		/// Maximum length for pallet and call SCALE encoded string names.
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

		// The call does not exist in the runtime.
		NoSuchCall,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// This call is now paused. \[pallet_name, call_name\]
		CallPaused { pallet_name: PalletNameOf<T>, call_name: CallNameOf<T> },
		/// This call is now unpaused. \[pallet_name, call_name\]
		CallUnpaused { pallet_name: PalletNameOf<T>, call_name: CallNameOf<T> },
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
			for (pallet_name, call_name) in &self.paused {
				PausedCalls::<T>::insert((pallet_name, call_name), ());
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
			pallet_name: PalletNameOf<T>,
			call_name: CallNameOf<T>,
		) -> DispatchResult {
			T::PauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_pause(&pallet_name, &call_name)?;
			PausedCalls::<T>::insert((&pallet_name, &call_name), ());
			Self::deposit_event(Event::CallPaused { pallet_name, call_name });

			Ok(())
		}

		/// Un-pause a call.
		///
		/// Can only be called by [`Config::UnpauseOrigin`].
		/// Emits an [`Event::CallUnpaused`] event on success.
		#[pallet::weight(T::WeightInfo::unpause_call())]
		pub fn unpause_call(
			origin: OriginFor<T>,
			pallet_name: PalletNameOf<T>,
			call_name: CallNameOf<T>,
		) -> DispatchResult {
			T::UnpauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_unpause(&pallet_name, &call_name)?;
			PausedCalls::<T>::remove((&pallet_name, &call_name));
			Self::deposit_event(Event::CallUnpaused { pallet_name, call_name });

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return whether this call is paused.
	pub fn is_paused_unbound(pallet_name: Vec<u8>, call_name: Vec<u8>) -> bool {
		let pallet_name = PalletNameOf::<T>::try_from(pallet_name);
		let call_name = CallNameOf::<T>::try_from(call_name);

		match (pallet_name, call_name) {
			(Ok(pallet_name), Ok(call_name)) => Self::is_paused(&pallet_name, &call_name),
			_ => T::PauseTooLongNames::get(),
		}
	}

	/// Return whether this call is paused.
	pub fn is_paused(pallet_name: &PalletNameOf<T>, call_name: &CallNameOf<T>) -> bool {
		<PausedCalls<T>>::contains_key((pallet_name, call_name))
	}

	/// Ensure that this call can be paused.
	pub fn ensure_can_pause(
		pallet_name: &PalletNameOf<T>,
		call_name: &CallNameOf<T>,
	) -> Result<(), Error<T>> {
		// The `TxPause` pallet can never be paused.
		if pallet_name.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return Err(Error::<T>::IsUnpausable)
		}
		let full_name: FullNameOf<T> = (pallet_name.clone(), Some(call_name.clone()));
		if T::UnfilterableCallNames::contains(&full_name) {
			return Err(Error::<T>::IsUnpausable)
		}
		if Self::is_paused(&pallet_name, &call_name) {
			return Err(Error::<T>::IsPaused)
		}
		Ok(())
	}

	/// Ensure that this call can be un-paused.
	pub fn ensure_can_unpause(
		pallet_name: &PalletNameOf<T>,
		call_name: &CallNameOf<T>,
	) -> Result<(), Error<T>> {
		if Self::is_paused(&pallet_name, &call_name) {
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
