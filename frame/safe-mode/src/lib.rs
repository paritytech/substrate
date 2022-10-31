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
	pallet_prelude::*,
	traits::{
		CallMetadata, Contains, Currency, Defensive, GetCallMetadata, NamedReservableCurrency,
		PalletInfoAccess,
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

		/// Currency type for this pallet, used for reservations.
		type Currency: NamedReservableCurrency<
			Self::AccountId,
			ReserveIdentifier = Self::BlockNumber,
		>;

		/// Contains all runtime calls in any pallet that can be dispatched even while the safe-mode
		/// is active.
		///
		/// The safe-mode pallet cannot disable it's own calls, and does not need to be explicitly
		/// added here.
		type WhitelistCalls: Contains<Self::RuntimeCall>;

		/// How long the safe-mode will stay active with [`Pallet::activate`].
		#[pallet::constant]
		type ActivationDuration: Get<Self::BlockNumber>;

		/// For how many blocks the safe-mode can be extended by each [`Pallet::extend`] call.
		///
		/// This does not impose a hard limit as the safe-mode can be extended multiple times.
		#[pallet::constant]
		type ExtendDuration: Get<Self::BlockNumber>;

		/// The amount that will be reserved upon calling [`Pallet::activate`].
		///
		/// `None` disallows permissionlessly enabling the safe-mode.
		#[pallet::constant]
		type ActivateReservationAmount: Get<Option<BalanceOf<Self>>>;

		/// The amount that will be reserved upon calling [`Pallet::extend`].
		///
		/// `None` disallows permissionlessly extending the safe-mode.
		#[pallet::constant]
		type ExtendReservationAmount: Get<Option<BalanceOf<Self>>>;

		/// The origin that may call [`Pallet::force_activate`].
		///
		/// The `Success` value is the number of blocks that this origin can activate safe-mode for.
		type ForceActivateOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that may call [`Pallet::force_extend`].
		///
		/// The `Success` value is the number of blocks that this origin can extend the safe-mode.
		type ForceExtendOrigin: EnsureOrigin<Self::Origin, Success = Self::BlockNumber>;

		/// The origin that may call [`Pallet::force_activate`].
		type ForceDeactivateOrigin: EnsureOrigin<Self::Origin>;

		/// The origin that may call [`Pallet::force_release_reservation`] and
		/// [`Pallet::slash_reservation`].
		type ForceReservationOrigin: EnsureOrigin<Self::Origin>;

		/// The minimal duration a deposit will remain reserved after safe-mode is activated or
		/// extended, unless [`Pallet::force_release_reservation`] is successfully dispatched
		/// sooner.
		///
		/// Every reservation is tied to a specific activation or extension, thus each reservation
		/// can be release independently after the delay for it has passed.
		///
		/// `None` disallows permissionlessly releasing the safe-mode reservations.
		#[pallet::constant]
		type ReleaseDelay: Get<Option<Self::BlockNumber>>;

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

		/// There is no balance reserved.
		NoReservation,

		/// This reservation cannot be released yet.
		CannotReleaseYet,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The safe-mode was activated until inclusively this \[block\].
		Activated { block: T::BlockNumber },

		/// The safe-mode was extended until inclusively this \[block\].
		Extended { block: T::BlockNumber },

		/// Exited safe-mode for a specific \[reason\].
		Exited { reason: ExitReason },

		/// An account had a reserve released that was reserved at a specific block. \[account,
		/// block, amount\]
		ReservationReleased { account: T::AccountId, block: T::BlockNumber, amount: BalanceOf<T> },

		/// An account had reserve slashed that was reserved at a specific block. \[account, block,
		/// amount\]
		ReservationSlashed { account: T::AccountId, block: T::BlockNumber, amount: BalanceOf<T> },
	}

	/// The reason why the safe-mode was exited.
	#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum ExitReason {
		/// The safe-mode was automatically exited after its duration ran out.
		Timeout,

		/// The safe-mode was forcefully exited by [`Pallet::force_deactivate`].
		Force,
	}

	/// Contains the last block number that the safe-mode will stay activated.
	///
	/// This is set to `None` if the safe-mode is inactive.
	/// The safe-mode is automatically deactivated when the current block number is greater than
	/// this.
	#[pallet::storage]
	#[pallet::getter(fn active_until)]
	pub type ActiveUntil<T: Config> = StorageValue<_, T::BlockNumber, OptionQuery>;

	/// Holds the reserve that was reserved from a user at a specific block number.
	#[pallet::storage]
	#[pallet::getter(fn reserves)]
	pub type Reservations<T: Config> = StorageDoubleMap<
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
		/// Activate safe-mode permissionlessly for [`Config::ActivationDuration`] blocks.
		///
		/// Reserves [`Config::ActivateReservationAmount`] from the caller's account.
		/// Emits an [`Event::Activated`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is already activated.
		/// Errors with [`Error::NotConfigured`] if the reservation amount is `None` .
		///
		/// ### Safety
		///
		/// This may be called by any signed origin with [`Config::ActivateReservationAmount`] free
		/// currency to reserve. This call can be disabled for all origins by configuring
		/// [`Config::ActivateReservationAmount`] to `None`.
		#[pallet::weight(T::WeightInfo::activate())]
		pub fn activate(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_activate(Some(who), T::ActivationDuration::get())
		}

		/// Activate safe-mode by force for a per-origin configured number of blocks.
		///
		/// Emits an [`Event::Activated`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is already activated.
		///
		/// ### Safety
		///
		/// Can only be called by the [`Config::ForceActivateOrigin`] origin.
		#[pallet::weight(T::WeightInfo::force_activate())]
		pub fn force_activate(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceActivateOrigin::ensure_origin(origin)?;

			Self::do_activate(None, duration)
		}

		/// Extend the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// Reserves [`Config::ExtendReservationAmount`] from the caller's account.
		/// Emits an [`Event::Extended`] event on success.
		/// Errors with [`Error::IsInactive`] if the safe-mode is active.
		/// Errors with [`Error::NotConfigured`] if the reservation amount is `None` .
		///
		/// ### Safety
		///
		/// This may be called by any signed origin with [`Config::ExtendReservationAmount`] free
		/// currency to reserve. This call can be disabled for all origins by configuring
		/// [`Config::ExtendReservationAmount`] to `None`.
		#[pallet::weight(T::WeightInfo::extend())]
		pub fn extend(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_extend(Some(who), T::ExtendDuration::get())
		}

		/// Extend the safe-mode by force a per-origin configured number of blocks.
		///
		/// Emits an [`Event::Extended`] event on success.
		/// Errors with [`Error::IsInactive`] if the safe-mode is inactive.
		///
		/// ### Safety
		///
		/// Can only be called by the [`Config::ForceExtendOrigin`] origin.
		#[pallet::weight(T::WeightInfo::force_extend())]
		pub fn force_extend(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceExtendOrigin::ensure_origin(origin)?;

			Self::do_extend(None, duration)
		}

		/// Deactivate safe-mode by force.
		///
		/// Emits an [`Event::Exited`] with [`ExitReason::Force`] event on success.
		/// Errors with [`Error::IsInactive`] if the safe-mode is inactive.
		///
		/// Note: `safe-mode` will be automatically deactivated by [`Pallet::on_initialize`] hook
		/// after the block height is greater than [`ActiveUntil`] found in storage.
		/// Emits an [`Event::Exited`] with [`ExitReason::Timeout`] event on hook.
		///
		///
		/// ### Safety
		///
		/// Can only be called by the [`Config::ForceDeactivateOrigin`] origin.
		#[pallet::weight(T::WeightInfo::force_deactivate())]
		pub fn force_deactivate(origin: OriginFor<T>) -> DispatchResult {
			T::ForceDeactivateOrigin::ensure_origin(origin)?;

			Self::do_deactivate(ExitReason::Force)
		}

		/// Slash a reservation for an account that activated or extended safe-mode at a specific
		/// block earlier. This cannot be called while safe-mode is active.
		///
		/// Emits a [`Event::ReservationSlashed`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is active.
		///
		/// ### Safety
		///
		/// Can only be called by the [`Config::ForceReservationOrigin`] origin.
		#[pallet::weight(T::WeightInfo::slash_reservation())]
		pub fn slash_reservation(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: T::BlockNumber,
		) -> DispatchResult {
			T::ForceReservationOrigin::ensure_origin(origin)?;

			Self::do_slash(account, block)
		}

		/// Release a currency reservation for an account that activated safe-mode at a specific
		/// block earlier. This cannot be called while safe-mode is active and not until the
		/// [`Config::ReleaseDelay`] block height is passed.
		///
		/// Emits a [`Event::ReservationReleased`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is active.
		/// Errors with [`Error::CannotReleaseYet`] if the [`Config::ReleaseDelay`] .
		/// Errors with [`Error::NoReservation`] if the payee has no reserved currency at the
		/// block specified.
		///
		/// ### Safety
		///
		/// This may be called by any signed origin.
		/// This call can be disabled for all origins by configuring
		/// [`Config::ReleaseDelay`] to `None`.
		#[pallet::weight(T::WeightInfo::release_reservation())]
		pub fn release_reservation(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: T::BlockNumber,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_release(Some(who), account, block)
		}

		/// Release a currency reservation for an account that activated safe-mode at a specific
		/// block earlier. This cannot be called while safe-mode is active.
		///
		/// Emits a [`Event::ReservationReleased`] event on success.
		/// Errors with [`Error::IsActive`] if the safe-mode is active.
		/// Errors with [`Error::NoReservation`] if the payee has no reserved currency at the
		/// block specified.
		///
		/// ### Safety
		///
		/// Can only be called by the [`Config::ForceReservationOrigin`] origin.
		#[pallet::weight(T::WeightInfo::force_release_reservation())]
		pub fn force_release_reservation(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: T::BlockNumber,
		) -> DispatchResult {
			T::ForceReservationOrigin::ensure_origin(origin)?;

			Self::do_release(None, account, block)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Automatically deactivates the safe-mode when the period runs out.
		///
		/// Bypasses any call filters to avoid getting rejected by them.
		fn on_initialize(current: T::BlockNumber) -> Weight {
			match ActiveUntil::<T>::get() {
				Some(limit) if current > limit => {
					let _ = Self::do_deactivate(ExitReason::Timeout)
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
			let reserve = T::ActivateReservationAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, reserve)?;
		}

		ensure!(!ActiveUntil::<T>::exists(), Error::<T>::IsActive);
		let limit = <frame_system::Pallet<T>>::block_number().saturating_add(duration);
		ActiveUntil::<T>::put(limit);
		Self::deposit_event(Event::Activated { block: limit });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::extend`] and [`crate::Pallet::force_extend`] calls.
	fn do_extend(who: Option<T::AccountId>, duration: T::BlockNumber) -> DispatchResult {
		if let Some(who) = who {
			let reserve = T::ExtendReservationAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::reserve(who, reserve)?;
		}

		let limit =
			ActiveUntil::<T>::take().ok_or(Error::<T>::IsInactive)?.saturating_add(duration);
		ActiveUntil::<T>::put(limit);
		Self::deposit_event(Event::<T>::Extended { block: limit });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::force_deactivate`] call.
	///
	/// Errors if the safe-mode is already inactive.
	/// Does not check the origin.
	fn do_deactivate(reason: ExitReason) -> DispatchResult {
		let _limit = ActiveUntil::<T>::take().ok_or(Error::<T>::IsInactive)?;
		Self::deposit_event(Event::Exited { reason });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::release_reservation`] and
	/// [`crate::Pallet::force_release_reservation`] calls.
	///
	/// Errors if the safe-mode is active with [`Error::IsActive`].
	/// Errors if release is called too soon by anyone but [`Config::ForceReservationOrigin`] with
	/// [`Error::CannotReleaseYet`]. Does not check the origin.
	fn do_release(
		who: Option<T::AccountId>,
		account: T::AccountId,
		block: T::BlockNumber,
	) -> DispatchResult {
		ensure!(!Self::is_active(), Error::<T>::IsActive);

		let reserve = Reservations::<T>::get(&account, &block).ok_or(Error::<T>::NoReservation)?;

		if who.is_some() {
			let delay = T::ReleaseDelay::get().ok_or(Error::<T>::NotConfigured)?;
			let now = <frame_system::Pallet<T>>::block_number();
			ensure!(now > (block.saturating_add(delay)), Error::<T>::CannotReleaseYet);
		}

		Reservations::<T>::remove(&account, &block);
		T::Currency::unreserve_named(&block, &account, reserve);
		Self::deposit_event(Event::<T>::ReservationReleased { block, account, amount: reserve });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::slash_reservation`] call.
	///
	/// Errors if the safe-mode is active with [`Error::IsActive`].
	/// Does not check the origin.
	fn do_slash(account: T::AccountId, block: T::BlockNumber) -> DispatchResult {
		ensure!(!Self::is_active(), Error::<T>::IsActive);
		let reserve = Reservations::<T>::take(&account, block).ok_or(Error::<T>::NoReservation)?;

		T::Currency::slash_reserved_named(&block, &account, reserve);
		Self::deposit_event(Event::<T>::ReservationSlashed { block, account, amount: reserve });
		Ok(())
	}

	/// Reserve `reserve` amount from `who` and store it in `Reservations`.
	fn reserve(who: T::AccountId, reserve: BalanceOf<T>) -> DispatchResult {
		let block = <frame_system::Pallet<T>>::block_number();
		T::Currency::reserve_named(&block, &who, reserve)?;
		let current_reservation = Reservations::<T>::get(&who, block).unwrap_or_default();
		// Reservation is mapped to the block that an extrinsic calls activate or extend,
		// therefore we prevent abuse in a block by adding to present value in the same block. TODO:
		// should we? Why not just fail? Calls in other blocks to activate or extend are stored in a
		// new Reservations item.
		Reservations::<T>::insert(&who, block, current_reservation.saturating_add(reserve));
		Ok(())
	}

	/// Return whether the `safe-mode` is active.
	pub fn is_active() -> bool {
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

		if Self::is_active() {
			T::WhitelistCalls::contains(call)
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
