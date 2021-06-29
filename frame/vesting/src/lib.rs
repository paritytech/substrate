// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! # Vesting Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! A simple pallet providing a means of placing a linear curve on an account's locked balance. This
//! pallet ensures that there is a lock in place preventing the balance to drop below the *unvested*
//! amount for any reason other than transaction fee payment.
//!
//! As the amount vested increases over time, the amount unvested reduces. However, locks remain in
//! place and explicit action is needed on behalf of the user to ensure that the amount locked is
//! equivalent to the amount remaining to be vested. This is done through a dispatchable function,
//! either `vest` (in typical case where the sender is calling on their own behalf) or `vest_other`
//! in case the sender is calling on another account's behalf.
//!
//! ## Interface
//!
//! This pallet implements the `VestingSchedule` trait.
//!
//! ### Dispatchable Functions
//!
//! - `vest` - Update the lock, reducing it in line with the amount "vested" so far.
//! - `vest_other` - Update the lock of another account, reducing it in line with the amount
//!   "vested" so far.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
pub mod weights;

use sp_std::{prelude::*, fmt::Debug, convert::TryInto};
use codec::{Encode, Decode};
use sp_runtime::{RuntimeDebug, traits::{
	StaticLookup, Zero, AtLeast32BitUnsigned, MaybeSerializeDeserialize, Convert, Saturating, CheckedDiv
}};
use frame_support::{ensure, pallet_prelude::*};
use frame_support::traits::{
	Currency, LockableCurrency, VestingSchedule, WithdrawReasons, LockIdentifier,
	ExistenceRequirement, Get,
};
use frame_system::{ensure_signed, ensure_root, pallet_prelude::*};
pub use weights::WeightInfo;
pub use pallet::*;
pub use vesting_info::*;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type MaxLocksOf<T> = <<T as Config>::Currency as LockableCurrency<<T as frame_system::Config>::AccountId>>::MaxLocks;

const VESTING_ID: LockIdentifier = *b"vesting ";

// Module to enforce private fields on `VestingInfo`
mod vesting_info {
	use super::*;
	/// Struct to encode the vesting schedule of an individual account.
	#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug)]
	pub struct VestingInfo<Balance, BlockNumber> {
		/// Locked amount at genesis.
		locked: Balance,
		/// Amount that gets unlocked every block after `starting_block`.
		per_block: Balance,
		/// Starting block for unlocking(vesting).
		starting_block: BlockNumber,
	}

	impl<Balance: AtLeast32BitUnsigned + Copy, BlockNumber: AtLeast32BitUnsigned + Copy>
		VestingInfo<Balance, BlockNumber>
	{
		/// Instantiate a new `VestingInfo` and validate parameters
		pub fn try_new<T: Config>(
			locked: Balance,
			per_block: Balance,
			starting_block: BlockNumber,
		) -> Result<VestingInfo<Balance, BlockNumber>, Error<T>> {
			Self::validate_params(locked, per_block, starting_block)?;
			let per_block = if per_block > locked { locked } else { per_block };
			Ok(VestingInfo { locked, per_block, starting_block })
		}

		/// Validate parameters for `VestingInfo`.
		pub fn validate_params<T: Config>(
			locked: Balance,
			per_block: Balance,
			_starting_block: BlockNumber,
		) -> Result<(), Error<T>> {
			ensure!(!locked.is_zero() && !per_block.is_zero(), Error::<T>::InvalidScheduleParams);
			let min_transfer: u32 = T::MinVestedTransfer::get().try_into().unwrap_or(u32::MAX);
			let min_transfer = Balance::from(min_transfer);
			ensure!(locked >= min_transfer, Error::<T>::AmountLow);
			Ok(())
		}

		/// Instantiate a new `VestingInfo` without param validation. Useful for
		/// mocking bad inputs in testing.
		#[cfg(test)]
		pub fn unsafe_new(
			locked: Balance,
			per_block: Balance,
			starting_block: BlockNumber,
		) -> VestingInfo<Balance, BlockNumber> {
			VestingInfo { locked, per_block, starting_block }
		}

		/// Locked amount at schedule creation.
		pub fn locked(&self) -> Balance {
			self.locked
		}

		/// Amount that gets unlocked every block after `starting_block`.
		pub fn per_block(&self) -> Balance {
			self.per_block
		}

		/// Starting block for unlocking(vesting).
		pub fn starting_block(&self) -> BlockNumber {
			self.starting_block
		}

		/// Amount locked at block `n`.
		pub fn locked_at<BlockNumberToBalance: Convert<BlockNumber, Balance>>(
			&self,
			n: BlockNumber,
		) -> Balance {
			// Number of blocks that count toward vesting
			// Saturating to 0 when n < starting_block
			let vested_block_count = n.saturating_sub(self.starting_block);
			let vested_block_count = BlockNumberToBalance::convert(vested_block_count);
			// Return amount that is still locked in vesting
			vested_block_count.checked_mul(&self.per_block)
                .map(|balance| self.locked.saturating_sub(balance))
                .unwrap_or(Zero::zero())
		}

		/// Block number at which the schedule ends.
		pub fn ending_block<BlockNumberToBalance: Convert<BlockNumber, Balance>>(&self) -> Balance {
			let starting_block = BlockNumberToBalance::convert(self.starting_block);
			let duration = if self.per_block > self.locked {
				// If `per_block` is bigger than `locked`, the schedule will end
				// the block after starting.
				1u32.into()
			} else if self.per_block.is_zero() {
				// Check for div by 0 errors, which should only be from legacy
				// vesting schedules since new ones are validated for this.
				self.locked
			} else {
				let has_remainder = !(self.locked % self.per_block).is_zero();
				let maybe_duration = self.locked / self.per_block;
				if has_remainder {
					maybe_duration + 1u32.into()
				} else {
					maybe_duration
				}
			};
			starting_block.saturating_add(duration)
		}
	}
}

/// The indexes of vesting schedules to remove from an accounts vesting schedule collection.
enum Filter {
	/// Do not filter out any schedules.
	Zero,
	/// Filter out 1 schedule.
	One(usize),
	/// Filter out 2 schedules.
	Two(usize, usize),
}

impl Filter {
	/// Whether or not the filter says the schedule index should be removed.
	fn should_remove(&self, index: &usize) -> bool {
		match self {
			Self::Zero => false,
			Self::One(index1) => index1 == index,
			Self::Two(index1, index2) => index1 == index || index2 == index,
		}
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The currency trait.
		type Currency: LockableCurrency<Self::AccountId>;

		/// Convert the block number into a balance.
		type BlockNumberToBalance: Convert<Self::BlockNumber, BalanceOf<Self>>;

		/// The minimum amount transferred to call `vested_transfer`.
		#[pallet::constant]
		type MinVestedTransfer: Get<BalanceOf<Self>>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Maximum number of vesting schedules an account may have at a given moment.
		#[pallet::constant]
		type MaxVestingSchedules: Get<u32>;
	}

	/// Information regarding the vesting of a given account.
	#[pallet::storage]
	#[pallet::getter(fn vesting)]
	pub type Vesting<T: Config> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>
	>;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub vesting: Vec<(T::AccountId, T::BlockNumber, T::BlockNumber, BalanceOf<T>)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig {
				vesting: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
        fn build(&self) {
			use sp_runtime::traits::Saturating;

			// Generate initial vesting configuration
			// * who - Account which we are generating vesting configuration for
			// * begin - Block when the account will start to vest
			// * length - Number of blocks from `begin` until fully vested
			// * liquid - Number of units which can be spent before vesting begins
			for &(ref who, begin, length, liquid) in self.vesting.iter() {
				let balance = T::Currency::free_balance(who);
				assert!(!balance.is_zero(), "Currencies must be init'd before vesting");
				// Total genesis `balance` minus `liquid` equals funds locked for vesting
				let locked = balance.saturating_sub(liquid);
				let length_as_balance = T::BlockNumberToBalance::convert(length);
				let per_block = locked / length_as_balance.max(sp_runtime::traits::One::one());
				let vesting_info = VestingInfo::try_new::<T>(locked, per_block, begin)
					.expect("Invalid VestingInfo params at genesis");

				Vesting::<T>::try_append(who, vesting_info)
					.expect("Too many vesting schedules at genesis.");
				let reasons = WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE;
				T::Currency::set_lock(VESTING_ID, who, locked, reasons);
			}
		}
    }

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	#[pallet::metadata(
		T::AccountId = "AccountId", BalanceOf<T> = "Balance", T::BlockNumber = "BlockNumber"
	)]
	pub enum Event<T: Config> {
		/// The amount vested has been updated. This could indicate more funds are available. The
		/// balance given is the amount which is left unvested (and thus locked).
		/// \[account, unvested\]
		VestingUpdated(T::AccountId, BalanceOf<T>),
		/// An \[account\] has become fully vested. No further vesting can happen.
		VestingCompleted(T::AccountId),
		/// 2 vesting schedules where successfully merged together.
		///\[locked, per_block, starting_block\]
		VestingMergeSuccess(BalanceOf<T>, BalanceOf<T>, T::BlockNumber),
	}

	/// Error for the vesting pallet.
	#[pallet::error]
	pub enum Error<T> {
		/// The account given is not vesting.
		NotVesting,
		/// The account already has `MaxVestingSchedules` number of schedules and thus
		/// cannot add another one. Consider merging existing schedules in order to add another.
		AtMaxVestingSchedules,
		/// Amount being transferred is too low to create a vesting schedule.
		AmountLow,
		/// At least one of the indexes is out of bounds of the vesting schedules.
		ScheduleIndexOutOfBounds,
		/// Failed to create a new schedule because the parameters where invalid. i.e. `per_block` or
		/// `locked` was 0.
		InvalidScheduleParams,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Unlock any vested funds of the sender account.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must have funds still
		/// locked under this pallet.
		///
		/// Emits either `VestingCompleted` or `VestingUpdated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: 2 Reads, 2 Writes
		///     - Reads: Vesting Storage, Balances Locks, [Sender Account]
		///     - Writes: Vesting Storage, Balances Locks, [Sender Account]
		/// # </weight>
		#[pallet::weight(T::WeightInfo::vest_locked(MaxLocksOf::<T>::get())
			.max(T::WeightInfo::vest_unlocked(MaxLocksOf::<T>::get()))
		)]
		pub fn vest(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_vest(who)
		}

		/// Unlock any vested funds of a `target` account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `target`: The account whose vested funds should be unlocked. Must have funds still
		/// locked under this pallet.
		///
		/// Emits either `VestingCompleted` or `VestingUpdated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: 3 Reads, 3 Writes
		///     - Reads: Vesting Storage, Balances Locks, Target Account
		///     - Writes: Vesting Storage, Balances Locks, Target Account
		/// # </weight>
		#[pallet::weight(T::WeightInfo::vest_other_locked(MaxLocksOf::<T>::get())
			.max(T::WeightInfo::vest_other_unlocked(MaxLocksOf::<T>::get()))
		)]
		pub fn vest_other(
			origin: OriginFor<T>,
			target: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let who = T::Lookup::lookup(target)?;
			Self::do_vest(who)
		}

		/// Create a vested transfer.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `target`: The account that should be transferred the vested funds.
		/// - `schedule`: The vesting schedule attached to the transfer.
		///
		/// Emits `VestingCreated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: 3 Reads, 3 Writes
		///     - Reads: Vesting Storage, Balances Locks, Target Account, [Sender Account]
		///     - Writes: Vesting Storage, Balances Locks, Target Account, [Sender Account]
		/// # </weight>
		#[pallet::weight(
			T::WeightInfo::last_vested_transfer(MaxLocksOf::<T>::get())
			.max(T::WeightInfo::first_vested_transfer(MaxLocksOf::<T>::get()))
		)]
		pub fn vested_transfer(
			origin: OriginFor<T>,
			target: <T::Lookup as StaticLookup>::Source,
			schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		) -> DispatchResult {
			let transactor = ensure_signed(origin)?;
			let transactor = <T::Lookup as StaticLookup>::unlookup(transactor);
			Self::do_vested_transfer(transactor, target, schedule)
		}

		/// Force a vested transfer.
		///
		/// The dispatch origin for this call must be _Root_.
		///
		/// - `source`: The account whose funds should be transferred.
		/// - `target`: The account that should be transferred the vested funds.
		/// - `schedule`: The vesting schedule attached to the transfer.
		///
		/// Emits `VestingCreated`.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: 4 Reads, 4 Writes
		///     - Reads: Vesting Storage, Balances Locks, Target Account, Source Account
		///     - Writes: Vesting Storage, Balances Locks, Target Account, Source Account
		/// # </weight>
		#[pallet::weight(
			T::WeightInfo::first_force_vested_transfer(MaxLocksOf::<T>::get())
			.max(T::WeightInfo::last_force_vested_transfer(MaxLocksOf::<T>::get()))
		)]
		pub fn force_vested_transfer(
			origin: OriginFor<T>,
			source: <T::Lookup as StaticLookup>::Source,
			target: <T::Lookup as StaticLookup>::Source,
			schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_vested_transfer(source, target, schedule)
		}

		/// Merge two vesting schedules together, creating a new vesting schedule that unlocks over
		/// highest possible start and end blocks. If both schedules have already started the current 
		/// block will be used as the schedule start; with the caveat that if one schedule is finishes by 
		/// the current block, the other will be treated as the new merged schedule, unmodified.
		///
		/// NOTE: If `schedule1_index == schedule2_index` this is a no-op.
		/// NOTE: This will unlock all schedules through the current block prior to merging.
		/// NOTE: If both schedules have ended by the current block, no new schedule will be created.
		///
		/// Merged schedule attributes:
		/// starting_block: `MAX(schedule1.starting_block, scheduled2.starting_block, current_block)`.
		/// ending_block: `MAX(schedule1.ending_block, schedule2.ending_block)`.
		/// locked: `schedule1.locked_at(current_block) + schedule2.locked_at(current_block)`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `schedule1_index`: index of the first schedule to merge.
		/// - `schedule2_index`: index of the second schedule to merge.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: TODO Reads, TODO Writes
		///     - Reads: TODO
		///     - Writes: TODO
		/// # </weight>
		#[pallet::weight(
			T::WeightInfo::not_unlocking_merge_schedules(MaxLocksOf::<T>::get())
			.max(T::WeightInfo::unlocking_merge_schedules(MaxLocksOf::<T>::get()))
		)]
		pub fn merge_schedules(
			origin: OriginFor<T>,
			schedule1_index: u32,
			schedule2_index: u32,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if schedule1_index == schedule2_index {
				return Ok(());
			};
			let schedule1_index = schedule1_index as usize;
			let schedule2_index = schedule2_index as usize;
			let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;

			// The schedule index is based off of the schedule ordering prior to filtering out any
			// schedules that may be ending at this block.
			let schedule1 = *vesting.get(schedule1_index).ok_or(Error::<T>::ScheduleIndexOutOfBounds)?;
			let schedule2 = *vesting.get(schedule2_index).ok_or(Error::<T>::ScheduleIndexOutOfBounds)?;
			let filter = Filter::Two(schedule1_index, schedule2_index);

			// The length of vesting decreases by 2 here since we filter out 2 schedules. Thus we know
			// below that we can safely insert the new merged schedule.
			let maybe_vesting = Self::update_lock_and_schedules(who.clone(), vesting, filter);

			// We can't fail from here on because we have potentially removed two schedules.

			let now = <frame_system::Pallet<T>>::block_number();
			if let Some(s) = Self::merge_vesting_info(now, schedule1, schedule2) {
				let mut vesting = maybe_vesting.unwrap_or_default();
				// It shouldn't be possible for this to fail because we removed 2 schedules above.
				ensure!(vesting.try_push(s).is_ok(), Error::<T>::AtMaxVestingSchedules);
				Self::deposit_event(Event::<T>::VestingMergeSuccess(
					s.locked(),
					s.per_block(),
					s.starting_block(),
				));
				Vesting::<T>::insert(&who, vesting);
			} else if maybe_vesting.is_some() {
				Vesting::<T>::insert(&who, maybe_vesting.expect("checked above; qed"));
			} else {
				Vesting::<T>::remove(&who);
			}

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	// Create a new `VestingInfo`, based off of two other `VestingInfo`s.
	// NOTE: We assume both schedules have been vested up through the current block.
	fn merge_vesting_info(
		now: T::BlockNumber,
		schedule1: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		schedule2: VestingInfo<BalanceOf<T>, T::BlockNumber>,
	) -> Option<VestingInfo<BalanceOf<T>, T::BlockNumber>> {
		let schedule1_ending_block = schedule1.ending_block::<T::BlockNumberToBalance>();
		let schedule2_ending_block = schedule2.ending_block::<T::BlockNumberToBalance>();
		let now_as_balance = T::BlockNumberToBalance::convert(now);

		if schedule1_ending_block <= now_as_balance && schedule2_ending_block <= now_as_balance {
			// If both schedules hav ended, we don't merge and exit early.
			return None;
		} else if schedule1_ending_block <= now_as_balance {
			// If one schedule has ended, we treat the one that has not ended as the new
			// merged schedule.
			return Some(schedule2);
		} else if schedule2_ending_block <= now_as_balance {
			return Some(schedule1);
		}

		let locked = schedule1
			.locked_at::<T::BlockNumberToBalance>(now)
			.saturating_add(schedule2.locked_at::<T::BlockNumberToBalance>(now));
		// This shouldn't happen because we know at least one ending block is greater than now.
		if locked.is_zero() {
			return None;
		}

		let ending_block = schedule1_ending_block.max(schedule2_ending_block);
		let starting_block = now.max(schedule1.starting_block()).max(schedule2.starting_block());
		let duration =
			ending_block.saturating_sub(T::BlockNumberToBalance::convert(starting_block));
		let per_block = if duration.is_zero() {
			// The logic of `ending_block` guarantees that each schedule ends at least a block
			// after it starts and since we take the max starting and ending_block we should never
			// get here
			locked
		} else if duration > locked {
			// This would mean we have a per_block of less than 1, which should not be not possible
			// because when we create the new schedule is at most the same duration as the longest,
			// but never greater.
			1u32.into()
		} else {
			locked.checked_div(&duration)?
		};

		// At this point inputs have been validated, so this should always be `Some`.
		VestingInfo::try_new::<T>(locked, per_block, starting_block).ok()
	}

	// Execute a vested transfer from `source` to `target` with the given `schedule`.
	fn do_vested_transfer(
		source: <T::Lookup as StaticLookup>::Source,
		target: <T::Lookup as StaticLookup>::Source,
		schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
	) -> DispatchResult {
		VestingInfo::validate_params::<T>(
			schedule.locked(),
			schedule.per_block(),
			schedule.starting_block(),
		)?;

		let target = T::Lookup::lookup(target)?;
		let source = T::Lookup::lookup(source)?;
		if let Some(len) = Vesting::<T>::decode_len(&target) {
			ensure!(
				len < T::MaxVestingSchedules::get() as usize,
				Error::<T>::AtMaxVestingSchedules
			);
		}

		T::Currency::transfer(
			&source,
			&target,
			schedule.locked(),
			ExistenceRequirement::AllowDeath,
		)?;

		// We can't let this fail because the currency transfer has already happened
		Self::add_vesting_schedule(
			&target,
			schedule.locked(),
			schedule.per_block(),
			schedule.starting_block(),
		)
		.expect("schedule inputs and vec bounds have been validated. q.e.d.");

		Ok(())
	}

	/// (Re)set or remove the pallet's currency lock on `who`'s account in accordance with their
	/// current unvested amount and prune any vesting schedules that have completed.
	///
	/// NOTE: This will update the users lock, but will not read/write the `Vesting` storage item.
	fn update_lock_and_schedules(
		who: T::AccountId,
		vesting: BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>,
		filter: Filter,
	) -> Option<BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>> {
		let now = <frame_system::Pallet<T>>::block_number();

		let mut total_locked_now: BalanceOf<T> = Zero::zero();
		let still_vesting = vesting
			.into_iter()
			.enumerate()
			.filter_map(|(index, schedule)| {
				let locked_now = schedule.locked_at::<T::BlockNumberToBalance>(now);
				total_locked_now = total_locked_now.saturating_add(locked_now);
				if locked_now.is_zero() || filter.should_remove(&index) {
					None
				} else {
					Some(schedule)
				}
			})
			.collect::<Vec<_>>()
			.try_into()
			.expect("`BoundedVec` is created from another `BoundedVec` with same bound; q.e.d.");

		if total_locked_now.is_zero() {
			T::Currency::remove_lock(VESTING_ID, &who);
			Vesting::<T>::remove(&who);
			Self::deposit_event(Event::<T>::VestingCompleted(who));
			None
		} else {
			let reasons = WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE;
			T::Currency::set_lock(VESTING_ID, &who, total_locked_now, reasons);
			Self::deposit_event(Event::<T>::VestingUpdated(who, total_locked_now));
			Some(still_vesting)
		}
	}

	/// Unlock any vested funds of `who`.
	fn do_vest(who: T::AccountId) -> DispatchResult {
		let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;
		let maybe_vesting = Self::update_lock_and_schedules(who.clone(), vesting, Filter::Zero);
		if let Some(vesting) = maybe_vesting {
			Vesting::<T>::insert(&who, vesting);
		} else {
			Vesting::<T>::remove(&who);
		}

		Ok(())
	}
}

impl<T: Config> VestingSchedule<T::AccountId> for Pallet<T>
where
	BalanceOf<T>: MaybeSerializeDeserialize + Debug,
{
	type Currency = T::Currency;
	type Moment = T::BlockNumber;

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	fn vesting_balance(who: &T::AccountId) -> Option<BalanceOf<T>> {
		if let Some(v) = Self::vesting(who) {
			let now = <frame_system::Pallet<T>>::block_number();
			let total_locked_now = v.iter().fold(Zero::zero(), |total, schedule| {
				schedule.locked_at::<T::BlockNumberToBalance>(now).saturating_add(total)
			});
			Some(T::Currency::free_balance(who).min(total_locked_now))
		} else {
			None
		}
	}

	/// Adds a vesting schedule to a given account.
	///
	/// If there are already `MaxVestingSchedules`, an Error is returned and nothing
	/// is updated.
	///
	/// On success, a linearly reducing amount of funds will be locked. In order to realise any
	/// reduction of the lock over time as it diminishes, the account owner must use `vest` or
	/// `vest_other`.
	///
	/// Is a no-op if the amount to be vested is zero.
	fn add_vesting_schedule(
		who: &T::AccountId,
		locked: BalanceOf<T>,
		per_block: BalanceOf<T>,
		starting_block: T::BlockNumber,
	) -> DispatchResult {
		if locked.is_zero() {
			return Ok(());
		}

		let vesting_schedule = VestingInfo::try_new::<T>(locked, per_block, starting_block)?;
		let mut vesting = Self::vesting(who).unwrap_or_default();
		ensure!(vesting.try_push(vesting_schedule).is_ok(), Error::<T>::AtMaxVestingSchedules);

		if let Some(v) = Self::update_lock_and_schedules(who.clone(), vesting, Filter::Zero) {
			Vesting::<T>::insert(&who, v);
		} else {
			Vesting::<T>::remove(&who);
		}
		Ok(())
	}

	/// Remove a vesting schedule for a given account. Will error if `schedule_index` is `None`.
	fn remove_vesting_schedule(who: &T::AccountId, schedule_index: Option<u32>) -> DispatchResult {
		let schedule_index = schedule_index.ok_or(Error::<T>::ScheduleIndexOutOfBounds)?;
		let filter = Filter::One(schedule_index as usize);

		let vesting = Self::vesting(who).ok_or(Error::<T>::NotVesting)?;
		if let Some(v) = Self::update_lock_and_schedules(who.clone(), vesting, filter) {
			Vesting::<T>::insert(&who, v);
		} else {
			Vesting::<T>::remove(&who);
		};
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use frame_support::{assert_noop, assert_ok, assert_storage_noop, parameter_types};
	use frame_system::RawOrigin;
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BadOrigin, BlakeTwo256, Identity, IdentityLookup},
	};

	use super::*;
	use crate as pallet_vesting;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
			Vesting: pallet_vesting::{Pallet, Call, Storage, Event<T>, Config<T>},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
	impl frame_system::Config for Test {
		type BaseCallFilter = ();
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
	}
	parameter_types! {
		pub const MaxLocks: u32 = 10;
	}
	impl pallet_balances::Config for Test {
		type Balance = u64;
		type DustRemoval = ();
		type Event = Event;
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type MaxLocks = MaxLocks;
		type MaxReserves = ();
		type ReserveIdentifier = [u8; 8];
		type WeightInfo = ();
	}
	parameter_types! {
		pub const MinVestedTransfer: u64 = 10;
		pub static ExistentialDeposit: u64 = 0;
		pub const MaxVestingSchedules: u32 = 3;
	}
	impl Config for Test {
		type Event = Event;
		type Currency = Balances;
		type BlockNumberToBalance = Identity;
		type MinVestedTransfer = MinVestedTransfer;
		type WeightInfo = ();
		type MaxVestingSchedules = MaxVestingSchedules;
	}

	pub struct ExtBuilder {
		existential_deposit: u64,
		vesting_genesis_config: Option<Vec<(u64, u64, u64, u64)>>,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				existential_deposit: 1,
				vesting_genesis_config: None,
			}
		}
	}
	impl ExtBuilder {
		pub fn existential_deposit(mut self, existential_deposit: u64) -> Self {
			self.existential_deposit = existential_deposit;
			self
		}

		pub fn vesting_genesis_config(mut self, config: Vec<(u64, u64, u64, u64)>) -> Self {
			self.vesting_genesis_config = Some(config);
			self
		}

		pub fn build(self) -> sp_io::TestExternalities {
			EXISTENTIAL_DEPOSIT.with(|v| *v.borrow_mut() = self.existential_deposit);
			let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
			pallet_balances::GenesisConfig::<Test> {
				balances: vec![
					(1, 10 * self.existential_deposit),
					(2, 20 * self.existential_deposit),
					(3, 30 * self.existential_deposit),
					(4, 40 * self.existential_deposit),
					(12, 10 * self.existential_deposit)
				],
			}.assimilate_storage(&mut t).unwrap();

			let vesting = if let Some(vesting_config) = self.vesting_genesis_config {
				vesting_config
			} else {
				vec![
					(1, 0, 10, 5 * self.existential_deposit),
					(2, 10, 20, 0),
					(12, 10, 20, 5 * self.existential_deposit)
				]
			};

			pallet_vesting::GenesisConfig::<Test> {
				vesting
			}.assimilate_storage(&mut t).unwrap();
			let mut ext = sp_io::TestExternalities::new(t);
			ext.execute_with(|| System::set_block_number(1));
			ext
		}
	}

	/// A default existential deposit.
	const ED: u64 = 256;

	#[test]
	fn check_vesting_status() {
		ExtBuilder::default()
			.existential_deposit(256)
			.build()
			.execute_with(|| {
				let user1_free_balance = Balances::free_balance(&1);
				let user2_free_balance = Balances::free_balance(&2);
				let user12_free_balance = Balances::free_balance(&12);
				assert_eq!(user1_free_balance, 256 * 10); // Account 1 has free balance
				assert_eq!(user2_free_balance, 256 * 20); // Account 2 has free balance
				assert_eq!(user12_free_balance, 256 * 10); // Account 12 has free balance
				let user1_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 5,
					128, // Vesting over 10 blocks
					0,
				)
				.unwrap();
				let user2_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 20,
					256, // Vesting over 20 blocks
					10,
				)
				.unwrap();
				let user12_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 5,
					64, // Vesting over 20 blocks
					10,
				)
				.unwrap();
				assert_eq!(Vesting::vesting(&1).unwrap(), vec![user1_vesting_schedule]); // Account 1 has a vesting schedule
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![user2_vesting_schedule]); // Account 2 has a vesting schedule
				assert_eq!(Vesting::vesting(&12).unwrap(), vec![user12_vesting_schedule]); // Account 12 has a vesting schedule

				// Account 1 has only 128 units vested from their illiquid 256 * 5 units at block 1
				assert_eq!(Vesting::vesting_balance(&1), Some(128 * 9));
				// Account 2 has their full balance locked
				assert_eq!(Vesting::vesting_balance(&2), Some(user2_free_balance));
				// Account 12 has only their illiquid funds locked
				assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

				System::set_block_number(10);
				assert_eq!(System::block_number(), 10);

				// Account 1 has fully vested by block 10
				assert_eq!(Vesting::vesting_balance(&1), Some(0));
				// Account 2 has started vesting by block 10
				assert_eq!(Vesting::vesting_balance(&2), Some(user2_free_balance));
				// Account 12 has started vesting by block 10
				assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

				System::set_block_number(30);
				assert_eq!(System::block_number(), 30);

				assert_eq!(Vesting::vesting_balance(&1), Some(0)); // Account 1 is still fully vested, and not negative
				assert_eq!(Vesting::vesting_balance(&2), Some(0)); // Account 2 has fully vested by block 30
				assert_eq!(Vesting::vesting_balance(&12), Some(0)); // Account 2 has fully vested by block 30
			});
	}

	#[test]
	fn check_vesting_status_for_multi_schedule_account() {
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			assert_eq!(System::block_number(), 1);
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // Vesting over 20 blocks
				10,
			)
			.unwrap();

			// Use 2 already has a vesting schedule.
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			// User 2's free balance is from sched0
			let free_balance = Balances::free_balance(&2);
			assert_eq!(free_balance, ED * (20));
			assert_eq!(Vesting::vesting_balance(&2), Some(free_balance));

			// Add a 2nd schedule that is already unlocking by block #1
			let sched1 = VestingInfo::try_new::<Test>(
				ED * 10,
				ED, // Vesting over 10 blocks
				0,
			)
			.unwrap();
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, sched1));
			// Free balance is equal to the two existing schedules total amount.
			let free_balance = Balances::free_balance(&2);
			assert_eq!(free_balance, ED * (10 + 20));
			// The most recently added schedule exists.
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);
			// sched1 has free funds at block #1, but nothing else.
			assert_eq!(Vesting::vesting_balance(&2), Some(free_balance - sched1.per_block()));

			// Add a 3rd schedule
			let sched2 = VestingInfo::try_new::<Test>(
				ED * 30,
				ED, // Vesting over 30 blocks
				5,
			)
			.unwrap();
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, sched2));

			System::set_block_number(9);
			// Free balance is equal to the 3 existing schedules total amount.
			let free_balance = Balances::free_balance(&2);
			assert_eq!(free_balance, ED * (10 + 20 + 30));
			// sched1 and sched2 are freeing funds at block #9.
			assert_eq!(
				Vesting::vesting_balance(&2),
				Some(free_balance - sched1.per_block() * 9 - sched2.per_block() * 4)
			);

			System::set_block_number(20);
			// At block #20 sched1 is fully unlocked while sched2 and sched0 are partially unlocked.
			assert_eq!(
					Vesting::vesting_balance(&2),
					Some(
						free_balance -
							sched1.locked() - sched2.per_block() * 15 -
							sched0.per_block() * 10
					)
				);

				System::set_block_number(30);
				// At block #30 sched0 and sched1 are fully unlocked while sched2 is partially unlocked.
				assert_eq!(
					Vesting::vesting_balance(&2),
					Some(
						free_balance - sched1.locked() - sched2.per_block() * 25 - sched0.locked()
					)
				);

				// At block #35 sched2 fully unlocks and thus all schedules funds are unlocked.
				System::set_block_number(35);
				assert_eq!(System::block_number(), 35);
				assert_eq!(Vesting::vesting_balance(&2), Some(0));
			});
	}

	#[test]
	fn unvested_balance_should_not_transfer() {
		ExtBuilder::default()
			.existential_deposit(10)
			.build()
			.execute_with(|| {
				let user1_free_balance = Balances::free_balance(&1);
				assert_eq!(user1_free_balance, 100); // Account 1 has free balance
				// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
				assert_eq!(Vesting::vesting_balance(&1), Some(45));
				assert_noop!(
					Balances::transfer(Some(1).into(), 2, 56),
					pallet_balances::Error::<Test, _>::LiquidityRestrictions,
				); // Account 1 cannot send more than vested amount
			});
	}

	#[test]
	fn vested_balance_should_transfer() {
		ExtBuilder::default()
			.existential_deposit(10)
			.build()
			.execute_with(|| {
				let user1_free_balance = Balances::free_balance(&1);
				assert_eq!(user1_free_balance, 100); // Account 1 has free balance
				// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
				assert_eq!(Vesting::vesting_balance(&1), Some(45));
				assert_ok!(Vesting::vest(Some(1).into()));
				assert_ok!(Balances::transfer(Some(1).into(), 2, 55));
			});
	}

	#[test]
	fn vested_balance_should_transfer_using_vest_other() {
		ExtBuilder::default()
			.existential_deposit(10)
			.build()
			.execute_with(|| {
				let user1_free_balance = Balances::free_balance(&1);
				assert_eq!(user1_free_balance, 100); // Account 1 has free balance
				// Account 1 has only 5 units vested at block 1 (plus 50 unvested)
				assert_eq!(Vesting::vesting_balance(&1), Some(45));
				assert_ok!(Vesting::vest_other(Some(2).into(), 1));
				assert_ok!(Balances::transfer(Some(1).into(), 2, 55));
			});
	}

	#[test]
	fn extra_balance_should_transfer() {
		ExtBuilder::default()
			.existential_deposit(10)
			.build()
			.execute_with(|| {
				assert_ok!(Balances::transfer(Some(3).into(), 1, 100));
				assert_ok!(Balances::transfer(Some(3).into(), 2, 100));

				let user1_free_balance = Balances::free_balance(&1);
				assert_eq!(user1_free_balance, 200); // Account 1 has 100 more free balance than normal

				let user2_free_balance = Balances::free_balance(&2);
				assert_eq!(user2_free_balance, 300); // Account 2 has 100 more free balance than normal

				// Account 1 has only 5 units vested at block 1 (plus 150 unvested)
				assert_eq!(Vesting::vesting_balance(&1), Some(45));
				assert_ok!(Vesting::vest(Some(1).into()));
				assert_ok!(Balances::transfer(Some(1).into(), 3, 155)); // Account 1 can send extra units gained

				// Account 2 has no units vested at block 1, but gained 100
				assert_eq!(Vesting::vesting_balance(&2), Some(200));
				assert_ok!(Vesting::vest(Some(2).into()));
				assert_ok!(Balances::transfer(Some(2).into(), 3, 100)); // Account 2 can send extra units gained
			});
	}

	#[test]
	fn liquid_funds_should_transfer_with_delayed_vesting() {
		ExtBuilder::default()
			.existential_deposit(256)
			.build()
			.execute_with(|| {
				let user12_free_balance = Balances::free_balance(&12);

				assert_eq!(user12_free_balance, 2560); // Account 12 has free balance
				// Account 12 has liquid funds
				assert_eq!(Vesting::vesting_balance(&12), Some(user12_free_balance - 256 * 5));

				// Account 12 has delayed vesting
				let user12_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 5,
					64, // Vesting over 20 blocks
					10,
				).unwrap();
				assert_eq!(Vesting::vesting(&12).unwrap(), vec![user12_vesting_schedule]);

				// Account 12 can still send liquid funds
				assert_ok!(Balances::transfer(Some(12).into(), 3, 256 * 5));
			});
	}

	#[test]
	fn vested_transfer_works() {
		ExtBuilder::default()
			.existential_deposit(256)
			.build()
			.execute_with(|| {
				let user3_free_balance = Balances::free_balance(&3);
				let user4_free_balance = Balances::free_balance(&4);
				assert_eq!(user3_free_balance, 256 * 30);
				assert_eq!(user4_free_balance, 256 * 40);
				// Account 4 should not have any vesting yet.
				assert_eq!(Vesting::vesting(&4), None);
				// Make the schedule for the new transfer.
				let new_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 5,
					64, // Vesting over 20 blocks
					10,
				).unwrap();
				assert_ok!(Vesting::vested_transfer(Some(3).into(), 4, new_vesting_schedule));
				// Now account 4 should have vesting.
				assert_eq!(Vesting::vesting(&4).unwrap(), vec![new_vesting_schedule]);
				// Ensure the transfer happened correctly.
				let user3_free_balance_updated = Balances::free_balance(&3);
				assert_eq!(user3_free_balance_updated, 256 * 25);
				let user4_free_balance_updated = Balances::free_balance(&4);
				assert_eq!(user4_free_balance_updated, 256 * 45);
				// Account 4 has 5 * 256 locked.
				assert_eq!(Vesting::vesting_balance(&4), Some(256 * 5));

				System::set_block_number(20);
				assert_eq!(System::block_number(), 20);

				// Account 4 has 5 * 64 units vested by block 20.
				assert_eq!(Vesting::vesting_balance(&4), Some(10 * 64));

				System::set_block_number(30);
				assert_eq!(System::block_number(), 30);

				// Account 4 has fully vested.
				assert_eq!(Vesting::vesting_balance(&4), Some(0));
			});
	}

	#[test]
	fn vested_transfer_correctly_fails() {
		ExtBuilder::default()
			.existential_deposit(256)
			.build()
			.execute_with(|| {
				let user2_free_balance = Balances::free_balance(&2);
				let user4_free_balance = Balances::free_balance(&4);
				assert_eq!(user2_free_balance, 256 * 20);
				assert_eq!(user4_free_balance, 256 * 40);

				// Account 2 should already have a vesting schedule.
				let user2_vesting_schedule = VestingInfo::try_new::<Test>(
					256 * 20,
					256, // Vesting over 20 blocks
					10,
				).unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![user2_vesting_schedule]);

				// Fails due to too low transfer amount.
				let new_vesting_schedule_too_low = VestingInfo::unsafe_new(
					<Test as Config>::MinVestedTransfer::get() - 1,
					64,
					10,
				);
				assert_noop!(
					Vesting::vested_transfer(Some(3).into(), 4, new_vesting_schedule_too_low),
					Error::<Test>::AmountLow,
				);

				// `per_block` is 0, which would result in a schedule with infinite duration.
				let schedule_per_block_0 = VestingInfo::unsafe_new(
					256,
					0,
					10,
				);
				assert_noop!(
					Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, schedule_per_block_0),
					Error::<Test>::InvalidScheduleParams,
				);

				// `locked` is 0.
				let schedule_locked_0 = VestingInfo::unsafe_new(
					0,
					1,
					10,
				);
				assert_noop!(
					Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, schedule_locked_0),
					Error::<Test>::InvalidScheduleParams,
				);

				// Free balance has not changed.
				assert_eq!(user2_free_balance, Balances::free_balance(&2));
				assert_eq!(user4_free_balance, Balances::free_balance(&4));


			});
	}

	#[test]
	fn vested_transfer_allows_max_schedules() {
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			let mut user_4_free_balance = Balances::free_balance(&4);
			let max_schedules = <Test as Config>::MaxVestingSchedules::get();
			let sched = VestingInfo::try_new::<Test>(
				ED, 1, // Vest over 256 blocks.
				10,
			)
			.unwrap();
			// Add max amount schedules to user 4.
			for _ in 0 .. max_schedules {
				assert_ok!(Vesting::vested_transfer(Some(3).into(), 4, sched));
			}
			// The schedules count towards vesting balance
			let transferred_amount = ED * max_schedules as u64;
			assert_eq!(Vesting::vesting_balance(&4), Some(transferred_amount));
			// and free balance.
			user_4_free_balance += transferred_amount;
			assert_eq!(Balances::free_balance(&4), user_4_free_balance);

			// Cannot insert a 4th vesting schedule when `MaxVestingSchedules` === 3
			assert_noop!(
				Vesting::vested_transfer(Some(3).into(), 4, sched),
				Error::<Test>::AtMaxVestingSchedules,
			);
			// so the free balance does not change.
			assert_eq!(Balances::free_balance(&4), user_4_free_balance);

			// Account 4 has fully vested when all the schedules end
			System::set_block_number(ED + 10);
			assert_eq!(Vesting::vesting_balance(&4), Some(0));
		});
	}

	#[test]
	fn force_vested_transfer_works() {
		ExtBuilder::default().existential_deposit(256).build().execute_with(|| {
			let user3_free_balance = Balances::free_balance(&3);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user3_free_balance, 256 * 30);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 4 should not have any vesting yet.
			assert_eq!(Vesting::vesting(&4), None);
			// Make the schedule for the new transfer.
			let new_vesting_schedule = VestingInfo::try_new::<Test>(
				256 * 5,
				64, // Vesting over 20 blocks
				10,
			)
			.unwrap();

			assert_noop!(
				Vesting::force_vested_transfer(Some(4).into(), 3, 4, new_vesting_schedule),
				BadOrigin
			);
			assert_ok!(Vesting::force_vested_transfer(
				RawOrigin::Root.into(),
				3,
				4,
				new_vesting_schedule
			));
			// Now account 4 should have vesting.
			assert_eq!(Vesting::vesting(&4).unwrap()[0], new_vesting_schedule);
			assert_eq!(Vesting::vesting(&4).unwrap().len(), 1);
			// Ensure the transfer happened correctly.
			let user3_free_balance_updated = Balances::free_balance(&3);
			assert_eq!(user3_free_balance_updated, 256 * 25);
			let user4_free_balance_updated = Balances::free_balance(&4);
			assert_eq!(user4_free_balance_updated, 256 * 45);
			// Account 4 has 5 * 256 locked.
			assert_eq!(Vesting::vesting_balance(&4), Some(256 * 5));

			System::set_block_number(20);
			assert_eq!(System::block_number(), 20);

			// Account 4 has 5 * 64 units vested by block 20.
			assert_eq!(Vesting::vesting_balance(&4), Some(10 * 64));

			System::set_block_number(30);
			assert_eq!(System::block_number(), 30);

			// Account 4 has fully vested.
			assert_eq!(Vesting::vesting_balance(&4), Some(0));
		});
	}

	#[test]
	fn force_vested_transfer_correctly_fails() {
		ExtBuilder::default().existential_deposit(256).build().execute_with(|| {
			let user2_free_balance = Balances::free_balance(&2);
			let user4_free_balance = Balances::free_balance(&4);
			assert_eq!(user2_free_balance, 256 * 20);
			assert_eq!(user4_free_balance, 256 * 40);
			// Account 2 should already have a vesting schedule.
			let user2_vesting_schedule = VestingInfo::try_new::<Test>(
				256 * 20,
				256, // Vesting over 20 blocks
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![user2_vesting_schedule]);

			// Too low transfer amount.
			let new_vesting_schedule_too_low =
				VestingInfo::unsafe_new(<Test as Config>::MinVestedTransfer::get() - 1, 64, 10);
			assert_noop!(
				Vesting::force_vested_transfer(
					RawOrigin::Root.into(),
					3,
					4,
					new_vesting_schedule_too_low
				),
				Error::<Test>::AmountLow,
			);

			// `per_block` is 0
			let schedule_per_block_0 = VestingInfo::unsafe_new(256, 0, 10);
			assert_noop!(
				Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, schedule_per_block_0),
				Error::<Test>::InvalidScheduleParams,
			);

			// `locked` is 0
			let schedule_locked_0 = VestingInfo::unsafe_new(0, 1, 10);
			assert_noop!(
				Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, schedule_locked_0),
				Error::<Test>::InvalidScheduleParams,
			);

			// Verify no currency transfer happened.
			assert_eq!(user2_free_balance, Balances::free_balance(&2));
			assert_eq!(user4_free_balance, Balances::free_balance(&4));
		});
	}

	#[test]
	fn force_vested_transfer_allows_max_schedules() {
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			let mut user_4_free_balance = Balances::free_balance(&4);
			let max_schedules = <Test as Config>::MaxVestingSchedules::get();
			let sched = VestingInfo::try_new::<Test>(
				ED, 1, // Vest over 256 blocks.
				10,
			)
			.unwrap();
			// Add max amount schedules to user 4.
			for _ in 0 .. max_schedules {
				assert_ok!(Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, sched));
			}
			// The schedules count towards vesting balance.
			let transferred_amount = ED * max_schedules as u64;
			assert_eq!(Vesting::vesting_balance(&4), Some(transferred_amount));
			// and free balance.
			user_4_free_balance += transferred_amount;
			assert_eq!(Balances::free_balance(&4), user_4_free_balance);

			// Cannot insert a 4th vesting schedule when `MaxVestingSchedules` === 3.
			assert_noop!(
				Vesting::force_vested_transfer(RawOrigin::Root.into(), 3, 4, sched),
				Error::<Test>::AtMaxVestingSchedules,
			);
			// so the free balance does not change.
			assert_eq!(Balances::free_balance(&4), user_4_free_balance);

			// Account 4 has fully vested when all the schedules end.
			System::set_block_number(ED + 10);
			assert_eq!(Vesting::vesting_balance(&4), Some(0));
		});
	}

	#[test]
	fn merge_schedules_that_have_not_started() {
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // Vest over 20 blocks.
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);
			assert_eq!(Balances::usable_balance(&2), 0);

			// Add a schedule that is identical to the one that already exists
			Vesting::vested_transfer(Some(3).into(), 2, sched0).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched0]);
			assert_eq!(Balances::usable_balance(&2), 0);
			Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();

			// Since we merged identical schedules, the new schedule finishes at the same
			// time as the original, just with double the amount
			let sched1 = VestingInfo::try_new::<Test>(
				sched0.locked() * 2,
				sched0.per_block() * 2,
				10, // starts at the block the schedules are merged
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched1]);

			assert_eq!(Balances::usable_balance(&2), 0);
		});
	}

	#[test]
	fn merge_ongoing_schedules() {
		// Merging two schedules that have started will vest both before merging
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // Vest over 20 blocks
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			let sched1 = VestingInfo::try_new::<Test>(
				256 * 10,
				256,                         // Vest over 10 blocks
				sched0.starting_block() + 5, // Start at block 15
			)
			.unwrap();
			Vesting::vested_transfer(Some(4).into(), 2, sched1).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);

			// Got to half way through the second schedule where both schedules are actively vesting
			let cur_block = 20;
			System::set_block_number(cur_block);

			// user2 has no usable balances prior to the merge because they have not unlocked
			// with `vest` yet.
			assert_eq!(Balances::usable_balance(&2), 0);
			Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();

			// Merging schedules vests all pre-existing schedules prior to merging, which is reflected
			// in user2's updated usable balance
			let sched0_vested_now = sched0.per_block() * (cur_block - sched0.starting_block());
			let sched1_vested_now = sched1.per_block() * (cur_block - sched1.starting_block());
			assert_eq!(Balances::usable_balance(&2), sched0_vested_now + sched1_vested_now);

			// The locked amount is the sum of what both schedules have locked at the current block.
			let sched2_locked = sched1
				.locked_at::<Identity>(cur_block)
				.saturating_add(sched0.locked_at::<Identity>(cur_block));
			// End block of the new schedule is the greater of either merged schedule
			let sched2_end =
				sched1.ending_block::<Identity>().max(sched0.ending_block::<Identity>());
			let sched2_duration = sched2_end - cur_block;
			// Based off the new schedules total locked and its duration, we can calculate the
			// amount to unlock per block.
			let sched2_per_block = sched2_locked / sched2_duration;

			let sched2 =
				VestingInfo::try_new::<Test>(sched2_locked, sched2_per_block, cur_block).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2]);
		});
	}

	#[test]
	fn merging_shifts_other_schedules_index() {
		// Schedules being merged are filtered out, schedules to the right of any merged
		// schedule shift left and the new, merged schedule is always last.
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 10,
				ED, // Vesting over 10 blocks
				10,
			)
			.unwrap();
			let sched1 = VestingInfo::try_new::<Test>(
				ED * 11,
				ED, // Vesting over 11 blocks
				11,
			)
			.unwrap();
			let sched2 = VestingInfo::try_new::<Test>(
				ED * 12,
				ED, // Vesting over 12 blocks
				12,
			)
			.unwrap();

			// Account 3 start out with no schedules
			assert_eq!(Vesting::vesting(&3), None);
			// and some usable balance.
			let usable_balance = Balances::usable_balance(&3);
			assert_eq!(usable_balance, 30 * ED);

			let cur_block = 1;
			assert_eq!(System::block_number(), cur_block);

			// Transfer the above 3 schedules to account 3
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 3, sched0));
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 3, sched1));
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 3, sched2));

			// With no schedules vested or merged they are in the order they are created
			assert_eq!(Vesting::vesting(&3).unwrap(), vec![sched0, sched1, sched2]);
			// and the usable balance has not changed.
			assert_eq!(usable_balance, Balances::usable_balance(&3));

			Vesting::merge_schedules(Some(3).into(), 0, 2).unwrap();

			// Create the merged schedule of sched0 & sched2.
			// The merged schedule will have the max possible starting block,
			let sched3_start = sched1.starting_block().max(sched2.starting_block());
			// have locked equal to the sum of the two schedules locked through the current block,
			let sched3_locked =
				sched2.locked_at::<Identity>(cur_block) + sched0.locked_at::<Identity>(cur_block);
			// and will end at the max possible block.
			let sched3_end =
				sched2.ending_block::<Identity>().max(sched0.ending_block::<Identity>());
			let sched3_duration = sched3_end - sched3_start;
			let sched3_per_block = sched3_locked / sched3_duration;
			let sched3 =
				VestingInfo::try_new::<Test>(sched3_locked, sched3_per_block, sched3_start)
					.unwrap();

			// The not touched schedule moves left and the new merged schedule is appended.
			assert_eq!(Vesting::vesting(&3).unwrap(), vec![sched1, sched3]);
			// The usable balance hasn't changed since none of the schedules have started.
			assert_eq!(Balances::usable_balance(&3), usable_balance);
		});
	}

	#[test]
	fn merge_ongoing_and_yet_to_be_started_schedule() {
		// Merge an ongoing schedule that has had `vest` called and a schedule that has not already
		// started.
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // Vesting over 20 blocks
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			// Fast forward to half way through the life of sched_1
			let mut cur_block = (sched0.starting_block() + sched0.ending_block::<Identity>()) / 2;
			assert_eq!(cur_block, 20);
			System::set_block_number(cur_block);

			// Prior to vesting there is no usable balance.
			let mut usable_balance = 0;
			assert_eq!(Balances::usable_balance(&2), usable_balance);
			// Vest the current schedules (which is just sched0 now).
			Vesting::vest(Some(2).into()).unwrap();

			// After vesting the usable balance increases by the amount the unlocked amount.
			let sched0_vested_now = sched0.locked() - sched0.locked_at::<Identity>(cur_block);
			usable_balance += sched0_vested_now;
			assert_eq!(Balances::usable_balance(&2), usable_balance);

			// Go forward a block.
			cur_block += 1;
			System::set_block_number(cur_block);

			// And add a schedule that starts after this block, but before sched0 finishes.
			let sched1 = VestingInfo::try_new::<Test>(
				ED * 10,
				1, // Vesting over 256 * 10 (2560) blocks
				cur_block + 1,
			)
			.unwrap();
			Vesting::vested_transfer(Some(4).into(), 2, sched1).unwrap();

			// Merge the schedules before sched1 starts.
			Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();
			// After merging, the usable balance only changes by the amount sched0 vested since we
			// last called `vest` (which is just 1 block). The usable balance is not affected by
			// sched1 because it has not started yet.
			usable_balance += sched0.per_block();
			assert_eq!(Balances::usable_balance(&2), usable_balance);

			// The resulting schedule will have the later starting block of the two,
			let sched2_start = sched1.starting_block();
			// have locked equal to the sum of the two schedules locked through the current block,
			let sched2_locked =
				sched0.locked_at::<Identity>(cur_block) + sched1.locked_at::<Identity>(cur_block);
			// and will end at the max possible block.
			let sched2_end =
				sched0.ending_block::<Identity>().max(sched1.ending_block::<Identity>());
			let sched2_duration = sched2_end - sched2_start;
			let sched2_per_block = sched2_locked / sched2_duration;

			let sched2 =
				VestingInfo::try_new::<Test>(sched2_locked, sched2_per_block, sched2_start)
					.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2]);
		});
	}

	#[test]
	fn merge_finishing_and_ongoing_schedule() {
		// If a schedule finishes by the current block we treat the ongoing schedule,
		// without any alterations, as the merged one.
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // Duration of 20.
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			let sched1 = VestingInfo::try_new::<Test>(
				ED * 40,
				ED, // Duration of 40.
				10,
			)
			.unwrap();
			assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, sched1));

			// Transfer a 3rd schedule, so we can demonstrate how schedule indices change.
			// (We are not merging this schedule.)
			let sched2 = VestingInfo::try_new::<Test>(
				ED * 30,
				ED, // Duration of 30.
				10,
			)
			.unwrap();
			assert_ok!(Vesting::vested_transfer(Some(3).into(), 2, sched2));

			// The schedules are in expected order prior to merging.
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1, sched2]);

			// Fast forward to sched0's end block.
			let cur_block = sched0.ending_block::<Identity>();
			System::set_block_number(cur_block);
			assert_eq!(System::block_number(), 30);

			// Prior to merge_schedules and with no vest/vest_other called the user has no usable
			// balance.
			assert_eq!(Balances::usable_balance(&2), 0);
			Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();

			// sched2 is now the first, since sched0 & sched1 get filtered out while "merging".
			// sched1 gets treated like the new merged schedule by getting pushed onto back
			// of the vesting schedules vec. Note: sched0 finished at the current block.
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2, sched1]);

			// sched0 has finished, so its funds are fully unlocked.
			let sched0_unlocked_now = sched0.locked();
			// The remaining schedules are ongoing, so their funds are partially unlocked.
			let sched1_unlocked_now = sched1.locked() - sched1.locked_at::<Identity>(cur_block);
			let sched2_unlocked_now = sched2.locked() - sched2.locked_at::<Identity>(cur_block);

			// Since merging also vests all the schedules, the users usable balance after merging
			// includes all pre-existing schedules unlocked through the current block, including
			// schedules not merged.
			assert_eq!(
				Balances::usable_balance(&2),
				sched0_unlocked_now + sched1_unlocked_now + sched2_unlocked_now
			);
		});
	}

	#[test]
	fn merge_finishing_schedules_does_not_create_a_new_one() {
		// If both schedules finish by the current block we don't create new one
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // 20 block duration.
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			// Create sched1 and transfer it to account 2.
			let sched1 = VestingInfo::try_new::<Test>(
				ED * 30,
				ED, // 30 block duration.
				10,
			)
			.unwrap();
			assert_ok!(Vesting::vested_transfer(Some(3).into(), 2, sched1));
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);

			let all_scheds_end =
				sched0.ending_block::<Identity>().max(sched1.ending_block::<Identity>());
			assert_eq!(all_scheds_end, 40);
			System::set_block_number(all_scheds_end);

			// Prior to merge_schedules and with no vest/vest_other called the user has no usable
			// balance.
			assert_eq!(Balances::usable_balance(&2), 0);

			// Merge schedule 0 and 1.
			Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();
			// The user no longer has any more vesting schedules because they both ended at the
			// block they where merged.
			assert_eq!(Vesting::vesting(&2), None);
			// And their usable balance has increased by the total amount locked in the merged
			// schedules.
			assert_eq!(Balances::usable_balance(&2), sched0.locked() + sched1.locked());
		});
	}

	#[test]
	fn merge_schedules_throws_proper_errors() {
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			// Account 2 should already have a vesting schedule.
			let sched0 = VestingInfo::try_new::<Test>(
				ED * 20,
				ED, // 20 block duration.
				10,
			)
			.unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

			// There is only 1 vesting schedule.
			assert_noop!(
				Vesting::merge_schedules(Some(2).into(), 0, 1),
				Error::<Test>::ScheduleIndexOutOfBounds
			);

			// There are 0 vesting schedules.
			assert_eq!(Vesting::vesting(&4), None);
			assert_noop!(Vesting::merge_schedules(Some(4).into(), 0, 1), Error::<Test>::NotVesting);

			// There are enough schedules to merge but an index is non-existent.
			Vesting::vested_transfer(Some(3).into(), 2, sched0).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched0]);
			assert_noop!(
				Vesting::merge_schedules(Some(2).into(), 0, 2),
				Error::<Test>::ScheduleIndexOutOfBounds
			);

			// It is a storage noop with no errors if the indexes are the same.
			assert_storage_noop!(Vesting::merge_schedules(Some(2).into(), 0, 0).unwrap());
		});
	}

	#[test]
	fn generates_multiple_schedules_from_genesis_config() {
		let vesting_config = vec![
			// 5 * existential deposit locked
			(1, 0, 10, 5 * ED),
			// 1 * existential deposit locked
			(2, 10, 20, 19 * ED),
			// 2 * existential deposit locked
			(2, 10, 20, 18 * ED),
			// 1 * existential deposit locked
			(12, 10, 20, 9 * ED),
			// 2 * existential deposit locked
			(12, 10, 20, 8 * ED),
			// 3 * existential deposit locked
			(12, 10, 20, 7 * ED),
		];
		ExtBuilder::default()
			.existential_deposit(ED)
			.vesting_genesis_config(vesting_config)
			.build()
			.execute_with(|| {
				let user1_sched1 = VestingInfo::try_new::<Test>(5 * ED, 128, 0u64).unwrap();
				assert_eq!(Vesting::vesting(&1).unwrap(), vec![user1_sched1]);

				let user2_sched1 = VestingInfo::try_new::<Test>(1 * ED, 12, 10u64).unwrap();
				let user2_sched2 = VestingInfo::try_new::<Test>(2 * ED, 25, 10u64).unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![user2_sched1, user2_sched2]);

				let user12_sched1 = VestingInfo::try_new::<Test>(1 * ED, 12, 10u64).unwrap();
				let user12_sched2 = VestingInfo::try_new::<Test>(2 * ED, 25, 10u64).unwrap();
				let user12_sched3 = VestingInfo::try_new::<Test>(3 * ED, 38, 10u64).unwrap();
				assert_eq!(
					Vesting::vesting(&12).unwrap(),
					vec![user12_sched1, user12_sched2, user12_sched3]
				);
			});
	}

	#[test]
	#[should_panic]
	fn multiple_schedules_from_genesis_config_errors() {
		// MaxVestingSchedules is 3, but this config has 4 for account 12 so we panic when building
		// from genesis.
		let vesting_config =
			vec![(12, 10, 20, ED), (12, 10, 20, ED), (12, 10, 20, ED), (12, 10, 20, ED)];
		ExtBuilder::default()
			.existential_deposit(ED)
			.vesting_genesis_config(vesting_config)
			.build();
	}

	#[test]
	fn merge_vesting_info_handles_per_block_0() {
		// Faulty schedules with an infinite duration (per_block == 0) can be merged to create
		// a schedule that vest 1 per_block, (helpful for faulty, legacy schedules).
		ExtBuilder::default().existential_deposit(ED).build().execute_with(|| {
			let sched0 = VestingInfo::unsafe_new(ED, 0, 1);
			let sched1 = VestingInfo::unsafe_new(ED * 2, 0, 10);

			let cur_block = 5;
			let expected_locked =
				sched0.locked_at::<Identity>(cur_block) + sched1.locked_at::<Identity>(cur_block);
			let expected_sched = VestingInfo::try_new::<Test>(
				expected_locked,
				1, // per_block of 1, which corrects existing schedules.
				10,
			)
			.unwrap();
			assert_eq!(
				Vesting::merge_vesting_info(cur_block, sched0, sched1),
				Some(expected_sched),
			);
		});
	}

	#[test]
	fn vesting_info_validation_works() {
		let min_transfer = <Test as Config>::MinVestedTransfer::get();
		// `locked` cannot be less than min_transfer (non 0 case).
		match VestingInfo::try_new::<Test>(min_transfer - 1, 1u64, 10u64) {
			Err(Error::<Test>::AmountLow) => (),
			_ => panic!(),
		}

		// `locked` cannot be 0.
		match VestingInfo::try_new::<Test>(0, 1u64, 10u64) {
			Err(Error::<Test>::InvalidScheduleParams) => (),
			_ => panic!(),
		}

		// `per_block` cannot be 0.
		match VestingInfo::try_new::<Test>(min_transfer + 1, 0u64, 10u64) {
			Err(Error::<Test>::InvalidScheduleParams) => (),
			_ => panic!(),
		}

		// With valid inputs it does not error and does not modify the inputs.
		assert_eq!(
			VestingInfo::try_new::<Test>(min_transfer, 1u64, 10u64).unwrap(),
			VestingInfo::unsafe_new(min_transfer, 1u64, 10u64)
		);

		// `per_block` is never bigger than `locked`.
		assert_eq!(
			VestingInfo::try_new::<Test>(256u64, 256 * 2u64, 10u64).unwrap(),
			VestingInfo::try_new::<Test>(256u64, 256u64, 10u64).unwrap()
		);
	}

	#[test]
	fn vesting_info_ending_block_works() {
		// Treats `per_block` 0 as a `per_block` of 1 to accommodate faulty, legacy schedules.
		let per_block_0 = VestingInfo::unsafe_new(256u32, 0u32, 10u32);
		assert_eq!(
			per_block_0.ending_block::<Identity>(),
			per_block_0.locked() + per_block_0.starting_block()
		);
		let per_block_1 = VestingInfo::try_new::<Test>(256u32, 1u32, 10u32).unwrap();
		assert_eq!(per_block_0.ending_block::<Identity>(), per_block_1.ending_block::<Identity>());

		// `per_block >= locked` always results in a schedule ending the block after it starts
		let per_block_gt_locked = VestingInfo::unsafe_new(256u32, 256 * 2u32, 10u32);
		assert_eq!(
			per_block_gt_locked.ending_block::<Identity>(),
			1 + per_block_gt_locked.starting_block()
		);
		let per_block_eq_locked = VestingInfo::try_new::<Test>(256u32, 256u32, 10u32).unwrap();
		assert_eq!(
			per_block_gt_locked.ending_block::<Identity>(),
			per_block_eq_locked.ending_block::<Identity>()
		);

		// Correctly calcs end if `locked % per_block != 0`. (We need a block to unlock the remainder).
		let imperfect_per_block = VestingInfo::try_new::<Test>(256u32, 250u32, 10u32).unwrap();
		assert_eq!(
			imperfect_per_block.ending_block::<Identity>(),
			imperfect_per_block.starting_block() + 2u32,
		);
		assert_eq!(
			imperfect_per_block
				.locked_at::<Identity>(imperfect_per_block.ending_block::<Identity>()),
			0
		);
	}
}
