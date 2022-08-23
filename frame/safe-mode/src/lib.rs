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

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	pallet_prelude::*,
	traits::{CallMetadata, Contains, GetCallMetadata},
};
use frame_system::pallet_prelude::OriginFor;
use sp_std::convert::TryInto;

mod benchmarking;
mod mock;
mod tests;

pub use pallet::*;

pub(crate) type PalletNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;
pub(crate) type ExtrinsicNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLen>;

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

		/// The only origin that can ban calls.
		type BanOrigin: EnsureOrigin<Self::Origin>;

		/// The only origin that can un-ban calls.
		type UnBanOrigin: EnsureOrigin<Self::Origin>;

		/// Pallets that are safe and can never be banned.
		///
		/// The safe-mode pallet is assumed to be safe itself and does not need to be added here.
		type SafePallets: Contains<PalletNameOf<Self>>;

		/// Maximum length for pallet- and extrinsic-names.
		///
		/// Too long names will not be truncated but handled like
		/// [`Self::BanTooLongNames`] specifies.
		#[pallet::constant]
		type MaxNameLen: Get<u32>;

		/// Defines if extrinsics and pallets with too long names should be treated as banned.
		///
		/// `true` means that overflowing names will be handled as banned.
		/// Setting this to `true` ensures that all extrinsics that
		/// are callable, are also ban-able.
		/// Otherwise there could be a situation where an extrinsic
		/// is callable but not ban-able, which would could be exploited.
		#[pallet::constant]
		type BanTooLongNames: Get<bool>;

		// Weight information for extrinsics in this pallet.
		//type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The call is banned.
		IsBanned,

		/// The call is not banned.
		IsNotBanned,

		/// The call is listed as safe and cannot be banned.
		IsSafe,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The call was banned.
		CallBanned(PalletNameOf<T>, ExtrinsicNameOf<T>),

		/// The call was un-banned.
		CallUnBanned(PalletNameOf<T>, ExtrinsicNameOf<T>),
	}

	/// The set of calls that are explicitly banned.
	#[pallet::storage]
	pub type BannedCalls<T: Config> =
		StorageMap<_, Blake2_128Concat, (PalletNameOf<T>, ExtrinsicNameOf<T>), (), OptionQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Ban a call.
		///
		/// Can only be called by [`Config::BanOrigin`].
		/// Emits an [`Event::CallBanned`] event on success.
		#[pallet::weight(0)]
		pub fn ban_call(
			origin: OriginFor<T>,
			pallet: PalletNameOf<T>,
			extrinsic: ExtrinsicNameOf<T>,
		) -> DispatchResult {
			T::BanOrigin::ensure_origin(origin)?;

			Self::ensure_can_ban(&pallet, &extrinsic)?;
			BannedCalls::<T>::insert((&pallet, &extrinsic), ());
			Self::deposit_event(Event::CallBanned(pallet, extrinsic));

			Ok(())
		}

		/// Un-ban a call.
		///
		/// Can only be called by [`Config::UnBanOrigin`].
		/// Emits an [`Event::CallUnBanned`] event on success.
		#[pallet::weight(0)]
		pub fn unban_call(
			origin: OriginFor<T>,
			pallet: PalletNameOf<T>,
			extrinsic: ExtrinsicNameOf<T>,
		) -> DispatchResult {
			T::UnBanOrigin::ensure_origin(origin)?;

			Self::ensure_can_unban(&pallet, &extrinsic)?;
			BannedCalls::<T>::remove((&pallet, &extrinsic));
			Self::deposit_event(Event::CallUnBanned(pallet, extrinsic));

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return whether the call is banned.
	pub fn is_banned_unbound(pallet: Vec<u8>, extrinsic: Vec<u8>) -> bool {
		let pallet = PalletNameOf::<T>::try_from(pallet);
		let extrinsic = ExtrinsicNameOf::<T>::try_from(extrinsic);

		match (pallet, extrinsic) {
			(Ok(pallet), Ok(extrinsic)) => Self::is_banned(&pallet, &extrinsic),
			_ => T::BanTooLongNames::get(),
		}
	}

	/// Return whether the call is banned.
	pub fn is_banned(pallet: &PalletNameOf<T>, extrinsic: &ExtrinsicNameOf<T>) -> bool {
		/*
		TODO: These checks should be superfluous since we use `ensure_can_ban`.
		// The safe-mode pallet is never banned.
		if pallet.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return false
		}
		// Any `safe` pallet is never banned.
		if T::SafePallets::contains(&pallet) {
			return false
		}
		*/
		<BannedCalls<T>>::contains_key((pallet, extrinsic))
	}

	/// Ensure that the call can be banned.
	pub fn ensure_can_ban(
		pallet: &PalletNameOf<T>,
		extrinsic: &ExtrinsicNameOf<T>,
	) -> Result<(), Error<T>> {
		if pallet.as_ref() == <Self as PalletInfoAccess>::name().as_bytes().to_vec() {
			return Err(Error::<T>::IsSafe)
		}
		if T::SafePallets::contains(&pallet) {
			return Err(Error::<T>::IsSafe)
		}
		if Self::is_banned(pallet, extrinsic) {
			return Err(Error::<T>::IsBanned)
		}
		Ok(())
	}

	/// Ensure that the call can be un-banned.
	pub fn ensure_can_unban(
		pallet: &PalletNameOf<T>,
		extrinsic: &ExtrinsicNameOf<T>,
	) -> Result<(), Error<T>> {
		if Self::is_banned(pallet, extrinsic) {
			// SAFETY: Everything that is banned, can be un-banned.
			Ok(())
		} else {
			Err(Error::IsNotBanned)
		}
	}
}

impl<T: pallet::Config> Contains<T::Call> for Pallet<T>
where
	<T as frame_system::Config>::Call: GetCallMetadata,
{
	/// Returns whether the call is allowed to be called.
	fn contains(call: &T::Call) -> bool {
		let CallMetadata { pallet_name, function_name } = call.get_call_metadata();
		!Pallet::<T>::is_banned_unbound(pallet_name.into(), function_name.into())
	}
}
