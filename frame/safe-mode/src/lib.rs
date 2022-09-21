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
pub mod weights;

use frame_support::{
	pallet_prelude::*,
	traits::{
		CallMetadata, Contains, Currency, Defensive, GetCallMetadata, PalletInfoAccess,
		ReservableCurrency,
	},
	weights::Weight,
};
use frame_system::pallet_prelude::*;
use sp_runtime::traits::Saturating;
use sp_std::{convert::TryInto, prelude::*};

pub use pallet::*;
pub use weights::*;

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
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Contains all calls that can be dispatched even when the safe-mode is enabled.
		///
		/// The `SafeMode` pallet is always included and does not need to be added here.
		type SafeModeFilter: Contains<Self::RuntimeCall>;

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// How long the safe-mode will stay active when enabled with [`Pallet::enable`].
		#[pallet::constant]
		type EnableDuration: Get<Self::BlockNumber>;

		/// For how many blocks the safe-mode can be extended by each [`Pallet::extend`] call.
		///
		/// This does not impose a hard limit as the safe-mode can be extended multiple times.
		#[pallet::constant]
		type ExtendDuration: Get<Self::BlockNumber>;

		/// The amount that will be reserved upon calling [`Pallet::enable`].
		///
		/// `None` disables the possibility of permissionlessly enabling the safe-mode.
		#[pallet::constant]
		type EnableStakeAmount: Get<Option<BalanceOf<Self>>>;

		/// The amount that will be reserved upon calling [`Pallet::extend`].
		///
		/// `None` disables the possibility of permissionlessly extending the safe-mode.
		#[pallet::constant]
		type ExtendStakeAmount: Get<Option<BalanceOf<Self>>>;

		/// The origin that can call [`Pallet::force_enable`].
		///
		/// The `Success` value is the number of blocks that this origin can enter into safe-mode.
		type ForceEnableOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that can call [`Pallet::force_extend`].
		///
		/// The `Success` value is the number of blocks that this origin can extend the safe-mode.
		type ForceExtendOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that can call [`Pallet::force_disable`].
		type ForceDisableOrigin: EnsureOrigin<Self::Origin>;

		/// The origin that can call [`Pallet::repay_stake`] and [`Pallet::slash_stake`].
		type RepayOrigin: EnsureOrigin<Self::Origin>;

		// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The safe-mode is (already or still) enabled.
		IsEnabled,

		/// The safe-mode is (already or still) disabled.
		IsDisabled,

		/// A value that is required for the extrinsic was not configured.
		NotConfigured,

		/// There is no balance staked.
		NotStaked,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The safe-mode was enabled until inclusively this \[block\].
		Enabled(T::BlockNumber),

		/// The safe-mode was extended until inclusively this \[block\].
		Extended(T::BlockNumber),

		/// The safe-mode was disabled for a specific \[reason\].
		Disabled(DisableReason),

		/// An account got repaid its stake. \[account, amount\]
		StakeRepaid(T::AccountId, BalanceOf<T>),

		/// An account got slashed its stake. \[account, amount\]
		StakeSlashed(T::AccountId, BalanceOf<T>),
	}

	/// The reason why the safe-mode was disabled.
	#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum DisableReason {
		/// The safe-mode was automatically disabled after its duration ran out.
		Timeout,

		/// The safe-mode was forcefully disabled by [`Pallet::force_disable`].
		Force,
	}

	/// Contains the last block number that the safe-mode will stay enabled.
	///
	/// This is set to `None` if the safe-mode is disabled.
	/// The safe-mode is automatically disabled when the current block number is greater than this.
	#[pallet::storage]
	#[pallet::getter(fn enabled)]
	pub type Enabled<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;

	/// Holds the stake that was reserved from a user at a specific block number.
	#[pallet::storage]
	#[pallet::getter(fn stakes)]
	pub type Stakes<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		T::AccountId,
		Blake2_128Concat,
		T::BlockNumber,
		BalanceOf<T>,
		OptionQuery,
	>;

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// The blocknumber up to which inclusively the safe-mode will be enabled.
		pub enabled: Option<T::BlockNumber>,
		pub _phantom: PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		// NOTE: `derive(Default)` does not work together with `#[pallet::genesis_config]`.
		// We therefore need to add a trivial default impl.
		fn default() -> Self {
			Self { enabled: None, _phantom: PhantomData }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			if let Some(block) = self.enabled {
				Enabled::<T>::put(block);
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Enable the safe-mode permissionlessly for [`Config::EnableDuration`] blocks.
		///
		/// Reserves `EnableStakeAmount` from the caller's account.
		/// Errors if the safe-mode is already enabled.
		/// Can be permanently disabled by configuring `EnableStakeAmount` to `None`.
		#[pallet::weight(T::WeightInfo::enable())]
		// #[pallet::weight(0)]
		pub fn enable(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_enable(Some(who), T::EnableDuration::get())
		}

		/// Enable the safe-mode by force for a per-origin configured number of blocks.
		///
		/// Errors if the safe-mode is already enabled.
		/// Emits an [`Event::Enabled`] event on success.
		/// Can only be called by the [`Config::ForceEnableOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_enable(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceEnableOrigin::ensure_origin(origin)?;

			Self::do_enable(None, duration)
		}

		/// Extend the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// Reserves `ExtendStakeAmount` from the caller's account.
		/// Errors if the safe-mode is disabled.
		/// Can be permanently disabled by configuring `ExtendStakeAmount` to `None`.
		#[pallet::weight(0)]
		pub fn extend(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_extend(Some(who), T::ExtendDuration::get())
		}

		/// Extend the safe-mode by force a per-origin configured number of blocks.
		///
		/// Errors if the safe-mode is disabled.
		/// Can only be called by the [`Config::ForceExtendOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_extend(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceExtendOrigin::ensure_origin(origin)?;

			Self::do_extend(None, duration)
		}

		/// Disable the safe-mode by force.
		///
		/// Will be automatically called after the safe-mode period ran out.
		/// Errors if the safe-mode is disabled.
		/// Can only be called by the [`Config::ForceDisableOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_disable(origin: OriginFor<T>) -> DispatchResult {
			T::ForceDisableOrigin::ensure_origin(origin.clone())?;

			Self::do_disable(DisableReason::Force)
		}

		/// Repay an honest account that put the chain into safe-mode earlier.
		///
		/// Errors if the safe-mode is already enabled.
		/// Emits a [`Event::StakeRepaid`] event on success.
		/// Can only be called by the [`Config::RepayOrigin`] origin.
		#[pallet::weight(0)]
		pub fn repay_stake(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: T::BlockNumber,
		) -> DispatchResult {
			T::RepayOrigin::ensure_origin(origin.clone())?;

			Self::do_repay_stake(account, block)
		}

		/// Slash a dishonest account that put the chain into safe-mode earlier.
		///
		/// Errors if the safe-mode is already enabled.
		/// Emits a [`Event::StakeSlashed`] event on success.
		/// Can only be called by the [`Config::RepayOrigin`] origin.
		#[pallet::weight(0)]
		pub fn slash_stake(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: T::BlockNumber,
		) -> DispatchResult {
			T::RepayOrigin::ensure_origin(origin.clone())?;

			Self::do_slash_stake(account, block)
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
	/// Logic for the [`crate::Pallet::enable`] and [`crate::Pallet::force_enable`] calls.
	fn do_enable(who: Option<T::AccountId>, duration: T::BlockNumber) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::EnableStakeAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, stake)?;
		}

		ensure!(!Enabled::<T>::exists(), Error::<T>::IsEnabled);
		let limit = <frame_system::Pallet<T>>::block_number().saturating_add(duration);
		Enabled::<T>::put(limit);
		Self::deposit_event(Event::Enabled(limit));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::extend`] and [`crate::Pallet::force_extend`] calls.
	fn do_extend(who: Option<T::AccountId>, duration: T::BlockNumber) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::ExtendStakeAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, stake)?;
		}

		let limit = Enabled::<T>::take().ok_or(Error::<T>::IsDisabled)?.saturating_add(duration);
		Enabled::<T>::put(limit);
		Self::deposit_event(Event::<T>::Extended(limit));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::force_disable`] call.
	///
	/// Does not check the origin. Errors if the safe-mode is already disabled.
	fn do_disable(reason: DisableReason) -> DispatchResult {
		let _limit = Enabled::<T>::take().ok_or(Error::<T>::IsDisabled)?;
		Self::deposit_event(Event::Disabled(reason));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::repay_stake`] call.
	///
	/// Does not check the origin. Errors if the safe-mode is enabled.
	fn do_repay_stake(account: T::AccountId, block: T::BlockNumber) -> DispatchResult {
		ensure!(!Self::is_enabled(), Error::<T>::IsEnabled);
		let stake = Stakes::<T>::take(&account, block).ok_or(Error::<T>::NotStaked)?;

		T::Currency::unreserve(&account, stake);
		Self::deposit_event(Event::<T>::StakeRepaid(account, stake));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::slash_stake`] call.
	///
	/// Does not check the origin. Errors if the safe-mode is enabled.
	fn do_slash_stake(account: T::AccountId, block: T::BlockNumber) -> DispatchResult {
		ensure!(!Self::is_enabled(), Error::<T>::IsEnabled);
		let stake = Stakes::<T>::take(&account, block).ok_or(Error::<T>::NotStaked)?;

		T::Currency::slash_reserved(&account, stake);
		Self::deposit_event(Event::<T>::StakeSlashed(account, stake));
		Ok(())
	}

	/// Reserve `stake` amount from `who` and store it in `Stakes`.
	fn reserve(who: T::AccountId, stake: BalanceOf<T>) -> DispatchResult {
		T::Currency::reserve(&who, stake)?;
		let block = <frame_system::Pallet<T>>::block_number();
		let current_stake = Stakes::<T>::get(&who, block).unwrap_or_default();
		Stakes::<T>::insert(&who, block, current_stake.saturating_add(stake));
		Ok(())
	}

	/// Return whether the `safe-mode` is currently enabled.
	pub fn is_enabled() -> bool {
		Enabled::<T>::exists()
	}

	/// Return whether this call is allowed to be dispatched.
	pub fn is_allowed(call: &T::RuntimeCall) -> bool
	where
		T::RuntimeCall: GetCallMetadata,
	{
		let CallMetadata { pallet_name, .. } = call.get_call_metadata();
		// The `SafeMode` pallet can always be dispatched.
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

impl<T: pallet::Config> Contains<T::RuntimeCall> for Pallet<T>
where
	T::RuntimeCall: GetCallMetadata,
{
	/// Return whether this call is allowed to be dispatched.
	fn contains(call: &T::RuntimeCall) -> bool {
		Pallet::<T>::is_allowed(call)
	}
}
