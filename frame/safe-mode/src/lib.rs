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

use frame_support::{
	pallet_prelude::*,
	traits::{
		CallMetadata, Contains, Currency, Defensive, GetCallMetadata, PalletInfoAccess,
		ReservableCurrency,
	},
};
use frame_system::pallet_prelude::*;
use sp_runtime::traits::Saturating;
use sp_std::{convert::TryInto, prelude::*};

mod benchmarking;
mod mock;
mod tests;

pub use pallet::*;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

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

		/// Contains all calls that can be dispatched when the safe-mode is enabled.
		///
		/// The `SafeMode` pallet is always included and does not need to be added here.
		type SafeModeFilter: Contains<Self::Call>;

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// How long the safe-mode will stay active when enabled with [`Pallet::enable`].
		#[pallet::constant]
		type EnableDuration: Get<Self::BlockNumber>;
		/// How much the safe-mode can be extended by each [`Pallet::extend`] call.
		///
		/// This does not impose a hard limit as the safe-mode can be extended multiple times.
		#[pallet::constant]
		type ExtendDuration: Get<Self::BlockNumber>;

		#[pallet::constant]
		type EnableStakeAmount: Get<Option<BalanceOf<Self>>>;
		#[pallet::constant]
		type ExtendStakeAmount: Get<Option<BalanceOf<Self>>>;

		type EnableOrigin: EnsureOrigin<Self::Origin>;
		type ExtendOrigin: EnsureOrigin<Self::Origin>;
		type DisableOrigin: EnsureOrigin<Self::Origin>;

		// Weight information for extrinsics in this pallet.
		//type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The safe-mode is (already) enabled.
		IsEnabled,

		/// The safe-mode is (already) disabled.
		IsDisabled,

		CannotStake,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The safe-mode was enabled until inclusively this \[block number\].
		Enabled(T::BlockNumber),

		/// The safe-mode was extended until inclusively this \[block number\].
		Extended(T::BlockNumber),

		/// The safe-mode was disabled for a specific \[reason\].
		Disabled(DisableReason),
	}

	/// The reason why the safe-mode was disabled.
	#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum DisableReason {
		/// The safe-mode was automatically disabled after `EnableDuration` had passed.
		Timeout,

		/// The safe-mode was forcefully disabled by the [`Config::DisableOrigin`] origin.
		Force,
	}

	/// Contains the last block number that the safe-mode will stay enabled.
	///
	/// This is set to `None` if the safe-mode is disabled.
	/// The safe-mode is automatically disabled when the current block number is greater than this.
	#[pallet::storage]
	pub type Enabled<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;

	#[pallet::storage]
	pub type Stakes<T: Config> =
		StorageMap<_, Blake2_128Concat, T::AccountId, BalanceOf<T>, ValueQuery>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Enable the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// Reserves `EnableStakeAmount` from the caller's account.
		/// Errors if the safe-mode is already enabled.
		/// Can be permanently disabled by configuring `EnableStakeAmount` to `None`.
		#[pallet::weight(0)]
		pub fn enable(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_enable(Some(who))
		}

		/// Enable the safe-mode by force for [`Config::EnableDuration`] blocks.
		///
		/// Can only be called by the [`Config::EnableOrigin`] origin.
		/// Errors if the safe-mode is already enabled.
		/// Emits an [`Event::Enabled`] event on success.
		#[pallet::weight(0)]
		pub fn force_enable(origin: OriginFor<T>) -> DispatchResult {
			T::EnableOrigin::ensure_origin(origin)?;

			Self::do_enable(None)
		}

		/// Extend the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// Reserves `ExtendStakeAmount` from the caller's account.
		/// Errors if the safe-mode is disabled.
		/// Can be permanently disabled by configuring `ExtendStakeAmount` to `None`.
		#[pallet::weight(0)]
		pub fn extend(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_extend(Some(who))
		}

		/// Extend the safe-mode by force for [`Config::ExtendDuration`] blocks.
		///
		/// Errors if the safe-mode is disabled.
		/// Can only be called by the [`Config::ExtendOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_extend(origin: OriginFor<T>) -> DispatchResult {
			T::ExtendOrigin::ensure_origin(origin)?;

			Self::do_extend(None)
		}

		/// Disable the safe-mode by force.
		///
		/// Will be automatically called after the safe-mode period ran out.
		/// Errors if the safe-mode is disabled.
		/// Can only be called by the [`Config::DisableOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_disable(origin: OriginFor<T>) -> DispatchResult {
			T::DisableOrigin::ensure_origin(origin.clone())?;

			Self::do_disable(DisableReason::Force)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Automatically disables the safe-mode when the period ran out.
		///
		/// Bypasses any call filters to avoid getting rejected by them.
		fn on_initialize(current: T::BlockNumber) -> Weight {
			match Enabled::<T>::get() {
				Some(limit) if current > limit => {
					let _ = Self::do_disable(DisableReason::Timeout)
						.defensive_proof("Must be disabled; qed");
					T::DbWeight::get().reads_writes(1, 1)
				},
				_ => T::DbWeight::get().reads(1), // TODO benchmark
			}
		}
	}
}

impl<T: Config> Pallet<T> {
	pub fn do_enable(who: Option<T::AccountId>) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::EnableStakeAmount::get().ok_or(Error::<T>::CannotStake)?;
			Self::reserve(who, stake)?;
		}

		ensure!(!Enabled::<T>::exists(), Error::<T>::IsEnabled);
		let limit =
			<frame_system::Pallet<T>>::block_number().saturating_add(T::EnableDuration::get());
		Enabled::<T>::put(limit);
		Self::deposit_event(Event::Enabled(limit));
		Ok(())
	}

	pub fn do_extend(who: Option<T::AccountId>) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::ExtendStakeAmount::get().ok_or(Error::<T>::CannotStake)?;
			Self::reserve(who, stake)?;
		}

		let limit = Enabled::<T>::take()
			.ok_or(Error::<T>::IsDisabled)?
			.saturating_add(T::ExtendDuration::get());
		Enabled::<T>::put(limit);
		Self::deposit_event(Event::<T>::Extended(limit));
		Ok(())
	}

	fn reserve(who: T::AccountId, stake: BalanceOf<T>) -> DispatchResult {
		T::Currency::reserve(&who, stake)?;
		Stakes::<T>::mutate(&who, |s| s.saturating_accrue(stake));
		Ok(())
	}

	/// Logic of the [`crate::Pallet::force_disable`] extrinsic.
	///
	/// Does not check the origin. Errors if the safe-mode is already disabled.
	pub fn do_disable(reason: DisableReason) -> DispatchResult {
		let _limit = Enabled::<T>::take().ok_or(Error::<T>::IsDisabled)?;
		Self::deposit_event(Event::Disabled(reason));
		Ok(())
	}

	/// Return whether the `safe-mode` is currently enabled.
	pub fn is_enabled() -> bool {
		Enabled::<T>::exists()
	}

	/// Return whether this call is allowed to be dispatched.
	pub fn can_dispatch(call: &T::Call) -> bool
	where
		T::Call: GetCallMetadata,
	{
		// The `SafeMode` pallet can always be dispatched.
		let CallMetadata { pallet_name, .. } = call.get_call_metadata();
		if pallet_name == <Pallet<T> as PalletInfoAccess>::name() {
			return true
		}

		if Self::is_enabled() {
			T::SafeModeFilter::contains(call)
		} else {
			true
		}
	}
}

impl<T: pallet::Config> Contains<T::Call> for Pallet<T>
where
	T::Call: GetCallMetadata,
{
	/// Return whether this call is allowed to be dispatched.
	fn contains(call: &T::Call) -> bool {
		Pallet::<T>::can_dispatch(call)
	}
}
