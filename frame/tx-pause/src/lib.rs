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

//! # Transaction Pause Pallet
//!
//! The Transaction Pause pallet provides a dynamic call filter that can be controlled with
//! extrinsics. This pallet may be used to disable dispatch of specific calls within a runtime.
//!
//! - [`Config`]
//! - [`Call`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Transaction Pause pallet provides functions for:
//!
//! - Setting a dynamic list of [`FullNameOf`] items that are matched against to filter these calls.
//! - Setting [`Config::WhitelistCallNames`] that cannot be paused by this pallet.
//! - Repatriating a reserved balance to a beneficiary account that exists.
//! - Transferring a balance between accounts (when not reserved).
//! - Slashing an account balance.
//! - Account creation and removal.
//! - Managing total issuance.
//! - Setting and managing locks.
//!
//! Can also be used as call-filter by the runtime together with the SafeMode
//!
//! TODO expand an link to safe mode in docs.
//!
//! ### Terminology
//!
//! - **Pause**: The ability to dispatch of a specific call becomes disabled.
//! - **Unpause**: The ability to dispatch of a specific call becomes enabled, if it was paused.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `pause` - Pause a pallet or optionally a specific call within a pallet.
//! - `unpause` - Unpause a pallet or optionally a specific call within a pallet.
//!
//! ## Usage
//!
//! The following examples show how to use the Transaction Pause pallet in your custom pallet.
//! TODO check doc links
//! ### Example within a runtime's [`pallet-frame-system::BaseCallFilter`] configuration:
//!
//! ```ignore
//! impl frame_system::Config for Runtime {
//! 	…
//! 	type BaseCallFilter = InsideBoth<DefaultFilter, InsideBoth<TxPause, SafeMode>>;
//! 	…
//! }
//! ```
//!
//! ## Genesis config
//!
//! The Transaction Pause pallet may be configured to pause calls on genesis with it's
//! [`GenesisConfig`].
//!
//! ## Assumptions
//!
//! * TODO

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

/// The stringy name of a pallet from [`GetCallMetadata`] for [`Config::RuntimeCall`] variants.
pub type PalletNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;
/// The stringy name of a call (within a pallet) from [`GetCallMetadata`] for
/// [`Config::RuntimeCall`] variants.
pub type CallNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;
/// The presently paused calls within a pallet.
#[derive(Encode, Decode, TypeInfo, Clone, PartialEq, Debug, MaxEncodedLen)]
pub enum PausedCallsOf<T: Config> {
	/// Specific calls in this pallet are paused, by their name.
	TheseCalls(BoundedVec<CallNameOf<T>, <T as Config>::MaxPausableCalls>),
	/// All calls of this pallet are paused.
	AllCalls,
	// Note: A pallet with `NoCalls` paused should not exist.
}

//TODO is this correct and sufficient? Or is `NoCalls` item needed?
impl<T: Config> Default for PausedCallsOf<T> {
	fn default() -> PausedCallsOf<T> {
		PausedCallsOf::<T>::AllCalls
	}
}

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
		type WhitelistCallNames: Contains<(PalletNameOf<Self>, PausedCallsOf<Self>)>;

		/// Maximum length for pallet and call SCALE encoded string names.
		///
		/// Too long names will not be truncated but handled like
		/// [`Self::PauseTooLongNames`] specifies.
		#[pallet::constant]
		type MaxNameLen: Get<u32>;

		/// Maximum calls within a pallet that may be paused.
		///
		/// Pallets with more total calls may be paused completely, or a subset of calls up to this
		/// number.
		#[pallet::constant]
		type MaxPausableCalls: Get<u32>;

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
		/// The pallet for this call is (already or still) paused.
		PalletPaused,

		/// The call is (already or still) paused.
		IsPaused,

		/// The call is (already or still) unpaused.
		IsUnpaused,

		/// The call is listed as safe and cannot be paused.
		IsUnpausable,

		/// There are too many calls paused to include another.
		TooManyPaused,

		/// The pallet or call does not exist in the runtime.
		NotFound,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A pallet call was paused. These calls are now paused for this pallet. \[pallet_name,
		/// paused_calls\]
		CallsPaused { pallet_name: PalletNameOf<T>, paused_calls: PausedCallsOf<T> },
		/// A pallet call was unpaused. These calls are still paused for this pallet.
		/// \[pallet_name, paused_calls\]
		CallsUnpaused { pallet_name: PalletNameOf<T>, paused_calls: PausedCallsOf<T> },
	}

	/// The paused calls for a pallet.
	/// Ether [`PausedCallsOf::AllCalls`] or a sorted, [`BoundedBTreeSet`] of
	/// [`PausedCallsOf::TheseCalls`] are paused.
	#[pallet::storage]
	#[pallet::getter(fn paused_calls)]
	pub type PausedCalls<T: Config> =
		StorageMap<_, Blake2_128Concat, PalletNameOf<T>, PausedCallsOf<T>, ValueQuery>;

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// The initially paused calls.
		pub paused: Vec<(PalletNameOf<T>, BoundedVec<CallNameOf<T>, <T>::MaxPausableCalls>)>,
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
			for (pallet_name, paused_call_names) in &self.paused {
				if paused_call_names.iter().find(|&&call| call == CallNameOf::<T>::try_from(b"AllCalls".to_vec()).unwrap()).is_some() {
					PausedCalls::<T>::insert(pallet_name, PausedCallsOf::<T>::AllCalls);
					continue
				}
				PausedCalls::<T>::insert(pallet_name, PausedCallsOf::<T>::TheseCalls(*paused_call_names));
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Pause a pallet, or set of specific calls for it, by name.
		///
		/// Can only be called by [`Config::PauseOrigin`].
		/// Emits an [`Event::CallsPaused`] event on success.
		#[pallet::weight(T::WeightInfo::pause())]
		pub fn pause_calls(
			origin: OriginFor<T>,
			pallet_name: PalletNameOf<T>,
			call_names: PausedCallsOf<T>,
		) -> DispatchResult {
			T::PauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_pause(&pallet_name, &call_names)?;
			let paused_calls = Self::insert_pause(&pallet_name, &call_names)?;
			Self::deposit_event(Event::CallsPaused { pallet_name, paused_calls });

			Ok(())
		}

		/// Unpause a specific call within a pallet, by their names.
		///
		/// Can only be called by [`Config::UnpauseOrigin`].
		/// Emits an [`Event::CallsUnpaused`] event on success.
		#[pallet::weight(T::WeightInfo::unpause())]
		pub fn unpause_calls(
			origin: OriginFor<T>,
			pallet_name: PalletNameOf<T>,
			call_names: PausedCallsOf<T>,
		) -> DispatchResult {
			T::UnpauseOrigin::ensure_origin(origin)?;

			Self::ensure_can_unpause(&pallet_name, &call_names)?;
			let paused_calls = Self::remove_pause(&pallet_name, &call_names)?;
			Self::deposit_event(Event::CallsUnpaused { pallet_name, paused_calls });
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return whether this pallet or call is paused.
	pub fn is_paused_unbound(pallet_name: Vec<u8>, call_name: Vec<u8>) -> bool {
		let pallet_name = PalletNameOf::<T>::try_from(pallet_name);
		let call_name = CallNameOf::<T>::try_from(call_name);

		match (pallet_name, call_name) {
			(Ok(pallet_name), Ok(call_name)) => {
				Self::is_call_paused(&pallet_name, &call_name)
			},
			_ => T::PauseTooLongNames::get(),
		}
	}

	/// Return whether a specific a call in a pallet is paused.
	fn is_paused(pallet_name: &PalletNameOf<T>, these_pause_calls_of: &PausedCallsOf<T>) -> bool {
		// TODO should these safety checks only be a write time? in the ensure_is_paused below.
		// Reason for: this reduces `is_paused_unbound` resources needed, as it's called in
		// `contains` for the BaseCallFilter for **every call made to this chain**

		// SAFETY: The `TxPause` pallet can never be paused.
		if pallet_name.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return false
		}

		// SAFETY: Everything that is whitelisted cannot be paused,
		// including calls within paused pallets.
		if T::WhitelistCallNames::contains(&(pallet_name.clone(), these_pause_calls_of.clone())) {
			return false
		};

		if let Ok(present_paused_calls_of) = <PausedCalls<T>>::try_get(pallet_name) {
			match present_paused_calls_of {
				PausedCallsOf::<T>::AllCalls => return true,
				PausedCallsOf::<T>::TheseCalls(present_paused_calls) => {
					if let PausedCallsOf::<T>::TheseCalls(these_calls) = these_pause_calls_of {
						for call in these_calls {
							if these_calls.contains(&call) {
								return true
							}
						}
					}
				},
			}
		}

		false
	}

	/// Return whether a specific a call in a pallet is paused.
	fn is_call_paused(pallet_name: &PalletNameOf<T>, call_name: &CallNameOf<T>) -> bool {
		if let Ok(present_paused_calls_of) = <PausedCalls<T>>::try_get(pallet_name) {
			// TODO is there a better way to instanciate the bounded vec here?
			// cargo complains of a From impl needed :(
			let mut call_vec: BoundedVec<CallNameOf<T>, <T as Config>::MaxPausableCalls> = BoundedVec::with_bounded_capacity(1);
			call_vec.force_push(*call_name);

			let these_pause_calls_of = PausedCallsOf::<T>::TheseCalls(call_vec);
			match present_paused_calls_of {
				PausedCallsOf::<T>::AllCalls => return true,
				PausedCallsOf::<T>::TheseCalls(present_paused_calls) => {
					if let PausedCallsOf::<T>::TheseCalls(these_calls) = these_pause_calls_of {
						for call in these_calls {
							if these_calls.contains(&call) {
								return true
							}
						}
					}
				},
			}
		}

		false
	}

	/// Ensure that a pallet or set of calls in a pallet can be paused.
	pub fn ensure_can_pause(
		pallet_name: &PalletNameOf<T>,
		these_pause_calls_of: &PausedCallsOf<T>,
	) -> Result<(), Error<T>> {
		if Self::is_paused(pallet_name, these_pause_calls_of) {
			return Err(Error::IsPaused)
		}
		Ok(())
	}

	/// Ensure that a pallet or set of calls in a pallet can be unpaused.
	pub fn ensure_can_unpause(
		pallet_name: &PalletNameOf<T>,
		these_pause_calls_of: &PausedCallsOf<T>,
	) -> Result<(), Error<T>> {
		if Self::is_paused(pallet_name, these_pause_calls_of) {
			// SAFETY: Everything that is paused, can be un-paused.
			Ok(())
		} else {
			Err(Error::IsUnpaused)
		}
	}

	/// Update the paused calls of a pallet and return it's present [`PausedCallsOf`].
	fn insert_pause(
		pallet_name: &PalletNameOf<T>,
		call_names: &PausedCallsOf<T>,
	) -> Result<PausedCallsOf<T>, Error<T>> {
		let presently_paused_calls = PausedCalls::<T>::try_get(&pallet_name).map_err(|_| Error::<T>::NotFound)?;
		match presently_paused_calls {
			PausedCallsOf::<T>::AllCalls => {
				return Err(Error::IsPaused)
			}
			PausedCallsOf::<T>::TheseCalls(paused_call_names) => {
				// TODO can we get a bounded vec "overloaded" to dedup or use some better method to compare elements and add if needed?
				// BoundedBTreeSet would be a better fit for this!
				let unbounded_names: Vec<BoundedVec<u8, <T as Config>::MaxNameLen>> = paused_call_names.iter().chain(call_names.iter()).collect();
				let bounded_names = unbounded_names.dedup().try_into().map_err(Error::<T>::TooManyPaused)?;
				PausedCalls::<T>::mutate_exists(&pallet_name, &bounded_names);
				return Ok(call_names)
			}
		}
		// PausedCalls::<T>::try_mutate(&pallet_name, |paused_calls| {
		// 	if let PausedCallsOf::<T>::AllCalls = paused_calls {
		// 		return Err(Error::PalletPaused)
		// 	} 
		// 	if let PausedCallsOf::<T>::TheseCalls(paused_call_names) = paused_calls {
		// 		let is_new_pause = paused_call_names
		// 			.try_push(*call_name)
		// 			.map_err(|_| Error::<T>::TooManyPaused)?;
		// 		match is_new_pause {
		// 			false => return Err(Error::<T>::IsPaused),
		// 			true => return Ok(PausedCallsOf::<T>::TheseCalls(*paused_call_names)),
		// 		}
		// 	} else {
		// 		return Err(Error::IsPaused)
		// 	}
		// })
		// .map_err(|_| Error::<T>::NotFound)
	}

	/// Update the paused calls of a pallet and return it's present [`PausedCallsOf`].
	/// Errors if the call is not found to be an existing pause, or the entire pallet is
	/// paused already, and we cannot remove a specific call pause.  
	fn remove_pause(
		pallet_name: &PalletNameOf<T>,
		call_names: &PausedCallsOf<T>,
	) -> Result<PausedCallsOf<T>, Error<T>> {
		let presently_paused_calls = PausedCalls::<T>::try_get(&pallet_name).map_err(|_| Error::<T>::NotFound)?;
			match presently_paused_calls {
				PausedCallsOf::<T>::AllCalls => {
					if call_names == PausedCallsOf::<T>::AllCalls {
						PausedCalls::<T>::remove(&pallet_name);
						return Ok(call_names)
					} else {
						// TODO note that you must remove `AllCalls` and then insert `TheseCalls(...)` as we cannot, in a guaranteed bounded way,
						// take the list of all calls for a pallet and return all but the ones specified to remove.    
						return Err(Error::<T>::PalletPaused)
					}
				}
				PausedCallsOf::<T>::TheseCalls(paused_call_names) => {
					let new_names: Vec<BoundedVec<u8, <T as Config>::MaxNameLen>> = paused_call_names.iter().chain(call_names.iter()).collect().dedup();
					let new_names: BoundedVec<BoundedVec<u8, <T as Config>::MaxNameLen>, <T as Config>::MaxPausableCalls> = new_names.try_into().map_err(Error::<T>::TooManyPaused)?;
					PausedCalls::<T>::set(&pallet_name, &bounded_names);
					return Ok(call_names)
				}
			}
		// PausedCalls::<T>::try_mutate(&pallet_name, |paused_calls_of| {
		// 	match paused_calls_of {
		// 		PausedCallsOf::<T>::AllCalls => {
		// 			if call_names == PausedCallsOf::<T>::AllCalls {
		// 				return Ok();
		// 			}
		// 		}
		// 		PausedCallsOf::<T>::TheseCalls(paused_call_names) => {

		// 		}
		// 	}
		// 	if let PausedCallsOf::<T>::TheseCalls(paused_call_names) = paused_calls_of {
		// 		let maybe_paused_position = paused_call_names.iter().position(|&call| call == *call_name);
		// 		match maybe_paused_position {
		// 			Some(position) => {
		// 				paused_call_names.remove(position);
		// 				return Ok(PausedCallsOf::<T>::TheseCalls(*paused_call_names))
		// 			},
		// 			None => return Err(Error::<T>::IsUnpaused),
		// 		}
		// 	} else {
		// 		return Err(Error::IsUnpaused)
		// 	}
		// })
		// .map_err(|_| Error::<T>::NotFound)
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
