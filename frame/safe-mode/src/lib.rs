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

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Contains all calls that can be dispatched even when the safe-mode is activated.
		///
		/// The `SafeMode` pallet is always included and does not need to be added here.
		type SafeModeFilter: Contains<Self::RuntimeCall>;

		/// How long the safe-mode will stay active when activated with [`Pallet::activate`].
		#[pallet::constant]
		type ActivateDuration: Get<Self::BlockNumber>;

		/// For how many blocks the safe-mode can be extended by each [`Pallet::extend`] call.
		///
		/// This does not impose a hard limit as the safe-mode can be extended multiple times.
		#[pallet::constant]
		type ExtendDuration: Get<Self::BlockNumber>;

		/// The amount that will be reserved upon calling [`Pallet::activate`].
		///
		/// `None` disallows permissionlessly enabling the safe-mode.
		#[pallet::constant]
		type ActivateStakeAmount: Get<Option<BalanceOf<Self>>>;

		/// The amount that will be reserved upon calling [`Pallet::extend`].
		///
		/// `None` disallows permissionlessly extending the safe-mode.
		#[pallet::constant]
		type ExtendStakeAmount: Get<Option<BalanceOf<Self>>>;

		/// The origin that can call [`Pallet::force_activate`].
		///
		/// The `Success` value is the number of blocks that this origin can activate safe-mode for.
		type ForceActivateOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that can call [`Pallet::force_extend`].
		///
		/// The `Success` value is the number of blocks that this origin can extend the safe-mode.
		type ForceExtendOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that can call [`Pallet::force_inactivate`].
		type ForceInactivateOrigin: EnsureOrigin<Self::Origin>;

		/// The origin that can call [`Pallet::repay_stake`] and [`Pallet::slash_stake`].
		type RepayOrigin: EnsureOrigin<Self::Origin>;

		// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The safe-mode is (already or still) active.
		IsActive,

		/// The safe-mode is (already or still) inactive.
		IsInactive,

		/// A value that is required for the extrinsic was not configured.
		NotConfigured,

		/// There is no balance staked.
		NotStaked,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The safe-mode was activated until inclusively this \[block\].
		Activated(T::BlockNumber),

		/// The safe-mode was extended until inclusively this \[block\].
		Extended(T::BlockNumber),

		/// Exited safe-mode for a specific \[reason\].
		Exited(ExitReason),

		/// An account got repaid its stake. \[account, amount\]
		StakeRepaid(T::AccountId, BalanceOf<T>),

		/// An account got slashed its stake. \[account, amount\]
		StakeSlashed(T::AccountId, BalanceOf<T>),
	}

	/// The reason why the safe-mode was exited.
	#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum ExitReason {
		/// The safe-mode was automatically exited after its duration ran out.
		Timeout,

		/// The safe-mode was forcefully exited by [`Pallet::force_inactivate`].
		Force,
	}

	/// Contains the last block number that the safe-mode will stay activated.
	///
	/// This is set to `None` if the safe-mode is inactive.
	/// The safe-mode is automatically inactivated when the current block number is greater than this.
	#[pallet::storage]
	#[pallet::getter(fn active)]
	pub type ActiveUntil<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;

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
		pub active: Option<T::BlockNumber>,
		pub _phantom: PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		// NOTE: `derive(Default)` does not work together with `#[pallet::genesis_config]`.
		// We therefore need to add a trivial default impl.
		fn default() -> Self {
			Self { active: None, _phantom: PhantomData }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			if let Some(block) = self.active {
				ActiveUntil::<T>::put(block);
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Activate safe-mode permissionlessly for [`Config::ActivateDuration`] blocks.
		///
		/// Reserves [`Config::ActivateStakeAmount`] from the caller's account.
		/// Emits an [`Event::Activated`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is already activated.
		/// 
		/// ### Safety
		/// 
		/// Can be permanently disabled by configuring [`Config::ActivateStakeAmount`] to `None`.
		#[pallet::weight(T::WeightInfo::activate())]
		// #[pallet::weight(0)]
		pub fn activate(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_activate(Some(who), T::ActivateDuration::get())
		}

		/// Activate safe-mode by force for a per-origin configured number of blocks.
		///
		/// Emits an [`Event::Activated`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is already activated.
		/// 
		/// ### Safety
		/// 
		/// Can only be called by the [`Config::ForceActivateOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_activate(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceActivateOrigin::ensure_origin(origin)?;

			Self::do_activate(None, duration)
		}

		/// Extend the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// Reserves [`Config::ExtendStakeAmount`] from the caller's account.
		/// Errors with [`Error::IsInactive`] if the safe-mode is active.
		/// 
		/// ### Safety
		/// 
		/// Can be permanently disabled by configuring [`Config::ActivateStakeAmount`] to `None`.
		#[pallet::weight(0)]
		pub fn extend(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_extend(Some(who), T::ExtendDuration::get())
		}

		/// Extend the safe-mode by force a per-origin configured number of blocks.
		///
		/// Errors with [`Error::IsInactive`] if the safe-mode is inactive.
		/// 
		/// ### Safety
		/// 
		/// Can only be called by the [`Config::ForceExtendOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_extend(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceExtendOrigin::ensure_origin(origin)?;

			Self::do_extend(None, duration)
		}

		/// Inactivate safe-mode by force.
		///
		/// Note: safe-mode will be automatically inactivated by [`Pallet::on_initialize`] hook after the block height is greater than [`ActiveUntil`] found in storage.
		/// Errors with [`Error::IsInactive`] if the safe-mode is inactive.
		/// 
		/// ### Safety
		/// 
		/// Can only be called by the [`Config::ForceInactivateOrigin`] origin.
		#[pallet::weight(0)]
		pub fn force_inactivate(origin: OriginFor<T>) -> DispatchResult {
			T::ForceInactivateOrigin::ensure_origin(origin.clone())?;

			Self::do_inactivate(ExitReason::Force)
		}

		/// Repay an honest account that activated safe-mode earlier.
		///
		/// Emits a [`Event::StakeRepaid`] event on success.
		/// Errors if the safe-mode is already activated.
		/// 
 		/// ### Safety
		/// 
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
		/// Errors if the safe-mode is already activated.
		/// Emits a [`Event::StakeSlashed`] event on success.
		/// 
		/// ### Safety
		/// 
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
		/// Automatically inactivates the safe-mode when the period ran out.
		///
		/// Bypasses any call filters to avoid getting rejected by them.
		fn on_initialize(current: T::BlockNumber) -> Weight {
			match ActiveUntil::<T>::get() {
				Some(limit) if current > limit => {
					let _ = Self::do_inactivate(ExitReason::Timeout)
						.defensive_proof("Must be inactive; qed");
					T::DbWeight::get().reads_writes(1, 1)
				},
				_ => T::DbWeight::get().reads(1), // TODO benchmark
			}
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Logic for the [`crate::Pallet::activate`] and [`crate::Pallet::force_activate`] calls.
	fn do_activate(who: Option<T::AccountId>, duration: T::BlockNumber) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::ActivateStakeAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, stake)?;
		}

		ensure!(!ActiveUntil::<T>::exists(), Error::<T>::IsActive);
		let limit = <frame_system::Pallet<T>>::block_number().saturating_add(duration);
		ActiveUntil::<T>::put(limit);
		Self::deposit_event(Event::Activated(limit));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::extend`] and [`crate::Pallet::force_extend`] calls.
	fn do_extend(who: Option<T::AccountId>, duration: T::BlockNumber) -> DispatchResult {
		if let Some(who) = who {
			let stake = T::ExtendStakeAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, stake)?;
		}

		let limit = ActiveUntil::<T>::take().ok_or(Error::<T>::IsInactive)?.saturating_add(duration);
		ActiveUntil::<T>::put(limit);
		Self::deposit_event(Event::<T>::Extended(limit));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::force_inactivate`] call.
	///
	/// Errors if the safe-mode is already inactive.
	/// Does not check the origin.
	fn do_inactivate(reason: ExitReason) -> DispatchResult {
		let _limit = ActiveUntil::<T>::take().ok_or(Error::<T>::IsInactive)?;
		Self::deposit_event(Event::Exited(reason));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::repay_stake`] call.
	///
	/// Errors if the safe-mode is active.
	/// Does not check the origin.
	fn do_repay_stake(account: T::AccountId, block: T::BlockNumber) -> DispatchResult {
		ensure!(!Self::is_activated(), Error::<T>::IsActive);
		let stake = Stakes::<T>::take(&account, block).ok_or(Error::<T>::NotStaked)?;

		T::Currency::unreserve(&account, stake);
		Self::deposit_event(Event::<T>::StakeRepaid(account, stake));
		Ok(())
	}

	/// Logic for the [`crate::Pallet::slash_stake`] call.
	///
	/// Errors if the safe-mode is activated.
	/// Does not check the origin. 
	fn do_slash_stake(account: T::AccountId, block: T::BlockNumber) -> DispatchResult {
		ensure!(!Self::is_activated(), Error::<T>::IsActive);
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

	/// Return whether the `safe-mode` is currently activated.
	pub fn is_activated() -> bool {
		ActiveUntil::<T>::exists()
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

		if Self::is_activated() {
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
