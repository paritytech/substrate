// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
	defensive_assert,
	pallet_prelude::*,
	traits::{
		fungible::{
			hold::{Inspect as FunHoldInspect, Mutate as FunHoldMutate},
			Inspect as FunInspect,
		},
		tokens::{Fortitude, Precision},
		CallMetadata, Contains, Defensive, GetCallMetadata, PalletInfoAccess, SafeModeNotify,
	},
	weights::Weight,
	DefaultNoBound,
};
use frame_system::pallet_prelude::*;
use sp_arithmetic::traits::Zero;
use sp_runtime::traits::Saturating;
use sp_std::{convert::TryInto, prelude::*};

pub use pallet::*;
pub use weights::*;

type BalanceOf<T> =
	<<T as Config>::Currency as FunInspect<<T as frame_system::Config>::AccountId>>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Currency type for this pallet, used for Deposits.
		type Currency: FunHoldInspect<Self::AccountId>
			+ FunHoldMutate<Self::AccountId, Reason = Self::RuntimeHoldReason>;

		/// The hold reason when reserving funds for entering or extending the safe-mode.
		type RuntimeHoldReason: From<HoldReason>;

		/// Contains all runtime calls in any pallet that can be dispatched even while the safe-mode
		/// is entered.
		///
		/// The safe-mode pallet cannot disable it's own calls, and does not need to be explicitly
		/// added here.
		type WhitelistedCalls: Contains<Self::RuntimeCall>;

		/// For how many blocks the safe-mode will be entered by [`Pallet::enter`].
		#[pallet::constant]
		type EnterDuration: Get<BlockNumberFor<Self>>;

		/// For how many blocks the safe-mode can be extended by each [`Pallet::extend`] call.
		///
		/// This does not impose a hard limit as the safe-mode can be extended multiple times.
		#[pallet::constant]
		type ExtendDuration: Get<BlockNumberFor<Self>>;

		/// The amount that will be reserved upon calling [`Pallet::enter`].
		///
		/// `None` disallows permissionlessly enabling the safe-mode and is a sane default.
		#[pallet::constant]
		type EnterDepositAmount: Get<Option<BalanceOf<Self>>>;

		/// The amount that will be reserved upon calling [`Pallet::extend`].
		///
		/// `None` disallows permissionlessly extending the safe-mode and is a sane default.
		#[pallet::constant]
		type ExtendDepositAmount: Get<Option<BalanceOf<Self>>>;

		/// The origin that may call [`Pallet::force_enter`].
		///
		/// The `Success` value is the number of blocks that this origin can enter safe-mode for.
		type ForceEnterOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = BlockNumberFor<Self>>;

		/// The origin that may call [`Pallet::force_extend`].
		///
		/// The `Success` value is the number of blocks that this origin can extend the safe-mode.
		type ForceExtendOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = BlockNumberFor<Self>>;

		/// The origin that may call [`Pallet::force_enter`].
		type ForceExitOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The only origin that can force to release or slash a deposit.
		type ForceDepositOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Notifies external logic when the safe-mode is being entered or exited.
		type Notify: SafeModeNotify;

		/// The minimal duration a deposit will remain reserved after safe-mode is entered or
		/// extended, unless [`Pallet::force_release_deposit`] is successfully called sooner.
		///
		/// Every deposit is tied to a specific activation or extension, thus each deposit can be
		/// released independently after the delay for it has passed.
		///
		/// `None` disallows permissionlessly releasing the safe-mode deposits and is a sane
		/// default.
		#[pallet::constant]
		type ReleaseDelay: Get<Option<BlockNumberFor<Self>>>;

		// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// The safe-mode is (already or still) entered.
		Entered,

		/// The safe-mode is (already or still) exited.
		Exited,

		/// This functionality of the pallet is disabled by the configuration.
		NotConfigured,

		/// There is no balance reserved.
		NoDeposit,

		/// The account already has a deposit reserved and can therefore not enter or extend again.
		AlreadyDeposited,

		/// This deposit cannot be released yet.
		CannotReleaseYet,

		/// An error from the underlying `Currency`.
		CurrencyError,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The safe-mode was entered until inclusively this block.
		Entered { until: BlockNumberFor<T> },

		/// The safe-mode was extended until inclusively this block.
		Extended { until: BlockNumberFor<T> },

		/// Exited the safe-mode for a specific reason.
		Exited { reason: ExitReason },

		/// An account reserved funds for either entering or extending the safe-mode.
		DepositPlaced { account: T::AccountId, amount: BalanceOf<T> },

		/// An account had a reserve released that was reserved.
		DepositReleased { account: T::AccountId, amount: BalanceOf<T> },

		/// An account had reserve slashed that was reserved.
		DepositSlashed { account: T::AccountId, amount: BalanceOf<T> },

		/// Could not hold funds for entering or extending the safe-mode.
		///
		/// This error comes from the underlying `Currency`.
		CannotDeposit,

		/// Could not release funds for entering or extending the safe-mode.
		///
		/// This error comes from the underlying `Currency`.
		CannotRelease,
	}

	/// The reason why the safe-mode was deactivated.
	#[derive(Copy, Clone, PartialEq, Eq, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
	pub enum ExitReason {
		/// The safe-mode was automatically deactivated after it's duration ran out.
		Timeout,

		/// The safe-mode was forcefully deactivated by [`Pallet::force_exit`].
		Force,
	}

	/// Contains the last block number that the safe-mode will remain entered in.
	///
	///  Set to `None` when safe-mode is exited.
	///
	/// Safe-mode is automatically exited when the current block number exceeds this value.
	#[pallet::storage]
	pub type EnteredUntil<T: Config> = StorageValue<_, BlockNumberFor<T>, OptionQuery>;

	/// Holds the reserve that was taken from an account at a specific block number.
	///
	/// This helps governance to have an overview of outstanding deposits that should be returned or
	/// slashed.
	#[pallet::storage]
	pub type Deposits<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		T::AccountId,
		Twox64Concat,
		BlockNumberFor<T>,
		BalanceOf<T>,
		OptionQuery,
	>;

	/// Configure the initial state of this pallet in the genesis block.
	#[pallet::genesis_config]
	#[derive(DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		pub entered_until: Option<BlockNumberFor<T>>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			if let Some(block) = self.entered_until {
				EnteredUntil::<T>::put(block);
			}
		}
	}

	/// A reason for the pallet placing a hold on funds.
	#[pallet::composite_enum]
	pub enum HoldReason {
		/// Funds are held for entering or extending the safe-mode.
		#[codec(index = 0)]
		EnterOrExtend,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Enter safe-mode permissionlessly for [`Config::EnterDuration`] blocks.
		///
		/// Reserves [`Config::EnterDepositAmount`] from the caller's account.
		/// Emits an [`Event::Entered`] event on success.
		/// Errors with [`Error::Entered`] if the safe-mode is already entered.
		/// Errors with [`Error::NotConfigured`] if the deposit amount is `None`.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::enter())]
		pub fn enter(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_enter(Some(who), T::EnterDuration::get()).map_err(Into::into)
		}

		/// Enter safe-mode by force for a per-origin configured number of blocks.
		///
		/// Emits an [`Event::Entered`] event on success.
		/// Errors with [`Error::Entered`] if the safe-mode is already entered.
		///
		/// Can only be called by the [`Config::ForceEnterOrigin`] origin.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::force_enter())]
		pub fn force_enter(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceEnterOrigin::ensure_origin(origin)?;

			Self::do_enter(None, duration).map_err(Into::into)
		}

		/// Extend the safe-mode permissionlessly for [`Config::ExtendDuration`] blocks.
		///
		/// This accumulates on top of the current remaining duration.
		/// Reserves [`Config::ExtendDepositAmount`] from the caller's account.
		/// Emits an [`Event::Extended`] event on success.
		/// Errors with [`Error::Exited`] if the safe-mode is entered.
		/// Errors with [`Error::NotConfigured`] if the deposit amount is `None`.
		///
		/// This may be called by any signed origin with [`Config::ExtendDepositAmount`] free
		/// currency to reserve. This call can be disabled for all origins by configuring
		/// [`Config::ExtendDepositAmount`] to `None`.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::extend())]
		pub fn extend(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			Self::do_extend(Some(who), T::ExtendDuration::get()).map_err(Into::into)
		}

		/// Extend the safe-mode by force for a per-origin configured number of blocks.
		///
		/// Emits an [`Event::Extended`] event on success.
		/// Errors with [`Error::Exited`] if the safe-mode is inactive.
		///
		/// Can only be called by the [`Config::ForceExtendOrigin`] origin.
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::force_extend())]
		pub fn force_extend(origin: OriginFor<T>) -> DispatchResult {
			let duration = T::ForceExtendOrigin::ensure_origin(origin)?;

			Self::do_extend(None, duration).map_err(Into::into)
		}

		/// Exit safe-mode by force.
		///
		/// Emits an [`Event::Exited`] with [`ExitReason::Force`] event on success.
		/// Errors with [`Error::Exited`] if the safe-mode is inactive.
		///
		/// Note: `safe-mode` will be automatically deactivated by [`Pallet::on_initialize`] hook
		/// after the block height is greater than the [`EnteredUntil`] storage item.
		/// Emits an [`Event::Exited`] with [`ExitReason::Timeout`] event when deactivated in the
		/// hook.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::force_exit())]
		pub fn force_exit(origin: OriginFor<T>) -> DispatchResult {
			T::ForceExitOrigin::ensure_origin(origin)?;

			Self::do_exit(ExitReason::Force).map_err(Into::into)
		}

		/// Slash a deposit for an account that entered or extended safe-mode at a given
		/// historical block.
		///
		/// This can only be called while safe-mode is entered.
		///
		/// Emits a [`Event::DepositSlashed`] event on success.
		/// Errors with [`Error::Entered`] if safe-mode is entered.
		///
		/// Can only be called by the [`Config::ForceDepositOrigin`] origin.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::force_slash_deposit())]
		pub fn force_slash_deposit(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: BlockNumberFor<T>,
		) -> DispatchResult {
			T::ForceDepositOrigin::ensure_origin(origin)?;

			Self::do_force_deposit(account, block).map_err(Into::into)
		}

		/// Permissionlessly release a deposit for an account that entered safe-mode at a
		/// given historical block.
		///
		/// The call can be completely disabled by setting [`Config::ReleaseDelay`] to `None`.
		/// This cannot be called while safe-mode is entered and not until
		/// [`Config::ReleaseDelay`] blocks have passed since safe-mode was entered.
		///
		/// Emits a [`Event::DepositReleased`] event on success.
		/// Errors with [`Error::Entered`] if the safe-mode is entered.
		/// Errors with [`Error::CannotReleaseYet`] if [`Config::ReleaseDelay`] block have not
		/// passed since safe-mode was entered. Errors with [`Error::NoDeposit`] if the payee has no
		/// reserved currency at the block specified.
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::release_deposit())]
		pub fn release_deposit(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: BlockNumberFor<T>,
		) -> DispatchResult {
			ensure_signed(origin)?;

			Self::do_release(false, account, block).map_err(Into::into)
		}

		/// Force to release a deposit for an account that entered safe-mode at a given
		/// historical block.
		///
		/// This can be called while safe-mode is still entered.
		///
		/// Emits a [`Event::DepositReleased`] event on success.
		/// Errors with [`Error::Entered`] if safe-mode is entered.
		/// Errors with [`Error::NoDeposit`] if the payee has no reserved currency at the
		/// specified block.
		///
		/// Can only be called by the [`Config::ForceDepositOrigin`] origin.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::force_release_deposit())]
		pub fn force_release_deposit(
			origin: OriginFor<T>,
			account: T::AccountId,
			block: BlockNumberFor<T>,
		) -> DispatchResult {
			T::ForceDepositOrigin::ensure_origin(origin)?;

			Self::do_release(true, account, block).map_err(Into::into)
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Automatically exits safe-mode when the current block number is greater than
		/// [`EnteredUntil`].
		fn on_initialize(current: BlockNumberFor<T>) -> Weight {
			let Some(limit) = EnteredUntil::<T>::get() else {
				return T::WeightInfo::on_initialize_noop()
			};

			if current > limit {
				let _ = Self::do_exit(ExitReason::Timeout).defensive_proof("Only Errors if safe-mode is not entered. Safe-mode has already been checked to be entered; qed");
				T::WeightInfo::on_initialize_exit()
			} else {
				T::WeightInfo::on_initialize_noop()
			}
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Logic for the [`crate::Pallet::enter`] and [`crate::Pallet::force_enter`] calls.
	pub(crate) fn do_enter(
		who: Option<T::AccountId>,
		duration: BlockNumberFor<T>,
	) -> Result<(), Error<T>> {
		ensure!(!Self::is_entered(), Error::<T>::Entered);

		if let Some(who) = who {
			let amount = T::EnterDepositAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::hold(who, amount)?;
		}

		let until = <frame_system::Pallet<T>>::block_number().saturating_add(duration);
		EnteredUntil::<T>::put(until);
		Self::deposit_event(Event::Entered { until });
		T::Notify::entered();
		Ok(())
	}

	/// Logic for the [`crate::Pallet::extend`] and [`crate::Pallet::force_extend`] calls.
	pub(crate) fn do_extend(
		who: Option<T::AccountId>,
		duration: BlockNumberFor<T>,
	) -> Result<(), Error<T>> {
		let mut until = EnteredUntil::<T>::get().ok_or(Error::<T>::Exited)?;

		if let Some(who) = who {
			let amount = T::ExtendDepositAmount::get().ok_or(Error::<T>::NotConfigured)?;
			Self::hold(who, amount)?;
		}

		until.saturating_accrue(duration);
		EnteredUntil::<T>::put(until);
		Self::deposit_event(Event::<T>::Extended { until });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::force_exit`] call.
	///
	/// Errors if safe-mode is already exited.
	pub(crate) fn do_exit(reason: ExitReason) -> Result<(), Error<T>> {
		let _until = EnteredUntil::<T>::take().ok_or(Error::<T>::Exited)?;
		Self::deposit_event(Event::Exited { reason });
		T::Notify::exited();
		Ok(())
	}

	/// Logic for the [`crate::Pallet::release_deposit`] and
	/// [`crate::Pallet::force_release_deposit`] calls.
	pub(crate) fn do_release(
		force: bool,
		account: T::AccountId,
		block: BlockNumberFor<T>,
	) -> Result<(), Error<T>> {
		let amount = Deposits::<T>::take(&account, &block).ok_or(Error::<T>::NoDeposit)?;

		if !force {
			ensure!(!Self::is_entered(), Error::<T>::Entered);

			let delay = T::ReleaseDelay::get().ok_or(Error::<T>::NotConfigured)?;
			let now = <frame_system::Pallet<T>>::block_number();
			ensure!(now > block.saturating_add(delay), Error::<T>::CannotReleaseYet);
		}

		let amount = T::Currency::release(
			&&HoldReason::EnterOrExtend.into(),
			&account,
			amount,
			Precision::BestEffort,
		)
		.map_err(|_| Error::<T>::CurrencyError)?;
		Self::deposit_event(Event::<T>::DepositReleased { account, amount });
		Ok(())
	}

	/// Logic for the [`crate::Pallet::slash_deposit`] call.
	pub(crate) fn do_force_deposit(
		account: T::AccountId,
		block: BlockNumberFor<T>,
	) -> Result<(), Error<T>> {
		let amount = Deposits::<T>::take(&account, block).ok_or(Error::<T>::NoDeposit)?;

		let burned = T::Currency::burn_held(
			&&HoldReason::EnterOrExtend.into(),
			&account,
			amount,
			Precision::BestEffort,
			Fortitude::Force,
		)
		.map_err(|_| Error::<T>::CurrencyError)?;
		defensive_assert!(burned == amount, "Could not burn the full held amount");
		Self::deposit_event(Event::<T>::DepositSlashed { account, amount });
		Ok(())
	}

	/// Place a hold for exactly `amount` and store it in `Deposits`.
	///
	/// Errors if the account already has a hold for the same reason.
	fn hold(who: T::AccountId, amount: BalanceOf<T>) -> Result<(), Error<T>> {
		let block = <frame_system::Pallet<T>>::block_number();
		if !T::Currency::balance_on_hold(&HoldReason::EnterOrExtend.into(), &who).is_zero() {
			return Err(Error::<T>::AlreadyDeposited.into())
		}

		T::Currency::hold(&HoldReason::EnterOrExtend.into(), &who, amount)
			.map_err(|_| Error::<T>::CurrencyError)?;
		Deposits::<T>::insert(&who, block, amount);
		Self::deposit_event(Event::<T>::DepositPlaced { account: who, amount });

		Ok(())
	}

	/// Return whether `safe-mode` is entered.
	pub fn is_entered() -> bool {
		EnteredUntil::<T>::exists()
	}

	/// Return whether the given call is allowed to be dispatched.
	pub fn is_allowed(call: &T::RuntimeCall) -> bool
	where
		T::RuntimeCall: GetCallMetadata,
	{
		let CallMetadata { pallet_name, .. } = call.get_call_metadata();
		// SAFETY: The `SafeMode` pallet is always allowed.
		if pallet_name == <Pallet<T> as PalletInfoAccess>::name() {
			return true
		}

		if Self::is_entered() {
			T::WhitelistedCalls::contains(call)
		} else {
			true
		}
	}
}

impl<T: Config> Contains<T::RuntimeCall> for Pallet<T>
where
	T::RuntimeCall: GetCallMetadata,
{
	/// Return whether the given call is allowed to be dispatched.
	fn contains(call: &T::RuntimeCall) -> bool {
		Pallet::<T>::is_allowed(call)
	}
}

impl<T: Config> frame_support::traits::SafeMode for Pallet<T> {
	type BlockNumber = BlockNumberFor<T>;

	fn is_entered() -> bool {
		Self::is_entered()
	}

	fn remaining() -> Option<BlockNumberFor<T>> {
		EnteredUntil::<T>::get().map(|until| {
			let now = <frame_system::Pallet<T>>::block_number();
			until.saturating_sub(now)
		})
	}

	fn enter(duration: BlockNumberFor<T>) -> Result<(), frame_support::traits::SafeModeError> {
		Self::do_enter(None, duration).map_err(Into::into)
	}

	fn extend(duration: BlockNumberFor<T>) -> Result<(), frame_support::traits::SafeModeError> {
		Self::do_extend(None, duration).map_err(Into::into)
	}

	fn exit() -> Result<(), frame_support::traits::SafeModeError> {
		Self::do_exit(ExitReason::Force).map_err(Into::into)
	}
}

impl<T: Config> From<Error<T>> for frame_support::traits::SafeModeError {
	fn from(err: Error<T>) -> Self {
		match err {
			Error::<T>::Entered => Self::AlreadyEntered,
			Error::<T>::Exited => Self::AlreadyExited,
			_ => Self::Unknown,
		}
	}
}
