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
			// TODO - Do we want to enforce this here? This would keep from merging where sum of
			// schedules is below MinVestedTransfer
			ensure!(locked >= min_transfer, Error::<T>::AmountLow);
			Ok(())
		}

		/// Instantiate a new `VestingInfo` without param validation. Useful for
		/// mocking bad inputs in testing.
		pub fn unsafe_new(
			locked: Balance,
			per_block: Balance,
			starting_block: BlockNumber,
		) -> VestingInfo<Balance, BlockNumber> {
			VestingInfo { locked, per_block, starting_block }
		}

		/// Locked amount at genesis.
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
			let maybe_balance = vested_block_count.checked_mul(&self.per_block);
			if let Some(balance) = maybe_balance {
				self.locked.saturating_sub(balance)
			} else {
				Zero::zero()
			}
		}

		/// Block number at which the schedule ends
		pub fn ending_block<BlockNumberToBalance: Convert<BlockNumber, Balance>>(&self) -> Balance {
			let starting_block = BlockNumberToBalance::convert(self.starting_block);
			let duration = if self.per_block > self.locked {
				// If `per_block` is bigger than `locked`, the schedule will end
				// the block after starting
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
		/// `locked` was a 0.
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
			let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;
			let maybe_vesting = Self::update_lock_and_schedules(who.clone(), vesting, vec![]);
			if let Some(vesting) = maybe_vesting {
				Vesting::<T>::insert(&who, vesting);
			} else {
				Vesting::<T>::remove(&who);
			}
			Ok(())
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
		pub fn vest_other(origin: OriginFor<T>, target: <T::Lookup as StaticLookup>::Source) -> DispatchResult {
			ensure_signed(origin)?;
			let who = T::Lookup::lookup(target)?;
			let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;
			let maybe_vesting = Self::update_lock_and_schedules(who.clone(), vesting, vec![]);
			if let Some(vesting) = maybe_vesting {
				Vesting::<T>::insert(&who, vesting);
			} else {
				Vesting::<T>::remove(&who);
			}
			Ok(())
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
		#[pallet::weight(T::WeightInfo::vested_transfer(MaxLocksOf::<T>::get()))]
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
		#[pallet::weight(T::WeightInfo::force_vested_transfer(MaxLocksOf::<T>::get()))]
		pub fn force_vested_transfer(
			origin: OriginFor<T>,
			source: <T::Lookup as StaticLookup>::Source,
			target: <T::Lookup as StaticLookup>::Source,
			schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_vested_transfer(source, target, schedule)
		}

		/// Merge two vesting schedules together, creating a new vesting schedule that vests over
		/// the maximum of the original two schedules duration.
		///
		/// NOTE: this will vest all schedules through the current block prior to merging. However,
		/// the schedule indexes are based off of the ordering prior to schedules being vested/filtered.
		///
		/// NOTE: If `schedule1_index == schedule2_index` this is a no-op.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `schedule1_index`: TODO
		/// - `schedule2_index`: TODO
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: TODO Reads, TODO Writes
		///     - Reads: TODO
		///     - Writes: TODO
		/// # </weight>
		#[pallet::weight(123)] // TODO
		pub fn merge_schedules(
			origin: OriginFor<T>,
			schedule1_index: u32,
			schedule2_index: u32,
		) -> DispatchResult {
			if schedule1_index == schedule2_index {
				return Ok(());
			};
			let who = ensure_signed(origin)?;
			let schedule1_index = schedule1_index as usize;
			let schedule2_index = schedule2_index as usize;
			let vesting = Self::vesting(&who).ok_or(Error::<T>::NotVesting)?;
			let len = vesting.len();
			ensure!(schedule1_index < len && schedule2_index < len, Error::<T>::ScheduleIndexOutOfBounds);

			// The schedule index is based off of the schedule ordering prior to filtering out any
			// schedules that may be ending at this block.
			let schedule1 = vesting[schedule1_index];
			let schedule2 = vesting[schedule2_index];
			let filter = vec![schedule1_index, schedule2_index];
			// The length of vesting decreases by 2 here since we filter out 2 schedules. So we know
			// below we have the space to insert the merged schedule.
			let maybe_vesting = Self::update_lock_and_schedules(who.clone(), vesting, filter);

			let now = <frame_system::Pallet<T>>::block_number();
			if let Some(s) = Self::merge_vesting_info(now, schedule1, schedule2) {
				let mut vesting = maybe_vesting.unwrap_or_default();
				// It shouldn't be possible for this to fail because we removed 2 schedules above.
				ensure!(vesting.try_push(s).is_ok(), Error::<T>::AtMaxVestingSchedules);
				Self::deposit_event(
					Event::<T>::VestingMergeSuccess(s.locked(), s.per_block(), s.starting_block())
				);
				Vesting::<T>::insert(&who, vesting);
			} else if maybe_vesting.is_some() {
				Vesting::<T>::insert(&who, maybe_vesting.unwrap());
			} else {
				Vesting::<T>::remove(&who);
			}

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	// Create a new `VestingInfo`, based off of two other `VestingInfo`s.
	// Note: We assume both schedules have been vested up through the current block.
	fn merge_vesting_info(
		now: T::BlockNumber,
		schedule1: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		schedule2: VestingInfo<BalanceOf<T>, T::BlockNumber>,
	) -> Option<VestingInfo<BalanceOf<T>, T::BlockNumber>> {
		let schedule1_ending_block = schedule1.ending_block::<T::BlockNumberToBalance>();
		let schedule2_ending_block = schedule2.ending_block::<T::BlockNumberToBalance>();
		let now_as_balance = T::BlockNumberToBalance::convert(now);
		if schedule1_ending_block <= now_as_balance && schedule2_ending_block <= now_as_balance {
			// If both schedule has ended, we don't merge
			return None;
		} else if schedule1_ending_block <= now_as_balance {
			// If one schedule has ended, we treat the one that has not ended as the new "merged schedule"
			return Some(schedule2)
		} else if schedule2_ending_block <= now_as_balance {
			return Some(schedule1)
		}
		let locked = schedule1.locked_at::<T::BlockNumberToBalance>(now)
			.saturating_add(schedule2.locked_at::<T::BlockNumberToBalance>(now));
		// This shouldn't happen because we know at least one ending block is greater than now.
		if locked.is_zero() { return None; }

		let ending_block = schedule1_ending_block.max(schedule2_ending_block);
		let starting_block = now
			.max(schedule1.starting_block())
			.max(schedule2.starting_block());
		let duration =
			ending_block.saturating_sub(T::BlockNumberToBalance::convert(starting_block));
		let per_block = if duration.is_zero() {
			// The logic of `ending_block` guarantees that each schedule ends at least a block
			// after it starts and since we take the max starting and ending_block we should never get here
			locked
		} else if duration > locked {
			// This would mean we have a per_block of less than 1, which should not be not possible
			// because when we merge the new schedule is at most the same duration as the longest, but
			// never greater
			1u32.into()
		} else {
			locked.checked_div(&duration)?
		};

		// At this point inputs have been validated, so this should always be `Some`
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
		.expect("schedule inputs and vec bounds validated. q.e.");

		Ok(())
	}

	/// (Re)set or remove the pallet's currency lock on `who`'s account in accordance with their
	/// current unvested amount and prune any vesting schedules that have completed.
	///
	/// NOTE: This will update the users lock, but will not read/write the `Vesting` storage item.
	fn update_lock_and_schedules(
		who: T::AccountId,
		vesting: BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>,
		filter: Vec<usize>,
	) -> Option<BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>> {
		let now = <frame_system::Pallet<T>>::block_number();

		let mut total_locked_now: BalanceOf<T> = Zero::zero();
		let still_vesting  = vesting
			.into_iter()
			.enumerate()
			.filter_map(| (i, schedule) | {
				let locked_now = schedule.locked_at::<T::BlockNumberToBalance>(now);
				total_locked_now = total_locked_now.saturating_add(locked_now);
				if locked_now.is_zero() || filter.contains(&i) {
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
}

impl<T: Config> VestingSchedule<T::AccountId> for Pallet<T> where
	BalanceOf<T>: MaybeSerializeDeserialize + Debug
{
	type Moment = T::BlockNumber;
	type Currency = T::Currency;

	// TODO should we expose merge vesting schedules here? Its a bit dangerous because schedules
	// need to be vested before being merged

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
	/// If there already `MaxVestingSchedules`, an `Err` is returned and nothing
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
		starting_block: T::BlockNumber
	) -> DispatchResult {
		if locked.is_zero() { return Ok(()) }
		let vesting_schedule = VestingInfo::try_new::<T>(
			locked, per_block, starting_block
		)?;
		let mut vesting = if let Some(v) = Self::vesting(who) {
			v
		} else {
			BoundedVec::default()
		};
		ensure!(vesting.try_push(vesting_schedule).is_ok(), Error::<T>::AtMaxVestingSchedules);
		if let Some(v) = Self::update_lock_and_schedules(who.clone(), vesting, vec![]) {
			Vesting::<T>::insert(&who, v);
		} else {
			Vesting::<T>::remove(&who);
		}
		Ok(())
	}

	/// Remove a vesting schedule for a given account.
	fn remove_vesting_schedule(who: &T::AccountId, schedule_index: Option<u32>) -> DispatchResult {
		let filter = if let Some(schedule_index) = schedule_index {
			ensure!(schedule_index < T::MaxVestingSchedules::get(), Error::<T>::ScheduleIndexOutOfBounds);
			vec![schedule_index as usize]
		} else {
			vec![]
		};
		let vesting= Self::vesting(who).ok_or(Error::<T>::NotVesting)?;
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
	use super::*;
	use crate as pallet_vesting;

	use frame_support::{assert_ok, assert_noop, parameter_types};
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup, Identity, BadOrigin},
	};
	use frame_system::RawOrigin;

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

	#[test]
	fn check_vesting_status() {
		ExtBuilder::default().existential_deposit(256).build().execute_with(|| {
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
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				assert_eq!(System::block_number(), 1);
				let sched0 = VestingInfo::try_new::<Test>(
					existential_deposit * 20,
					existential_deposit, // Vesting over 20 blocks
					10,
				)
				.unwrap();

				// Use 2 already has a vesting schedule.
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

				// User 2's free balance is from sched0
				let free_balance = Balances::free_balance(&2);
				assert_eq!(free_balance, existential_deposit * (20));
				assert_eq!(Vesting::vesting_balance(&2), Some(free_balance));

				let sched1 = VestingInfo::try_new::<Test>(
					existential_deposit * 10,
					existential_deposit, // Vesting over 10 blocks
					0,
				)
				.unwrap();
				assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, sched1));
				// Free balance is equal to the two existing schedules total amount
				let free_balance = Balances::free_balance(&2);
				assert_eq!(free_balance, existential_deposit * (10 + 20));
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);
				// sched1 has free funds at block #1, but nothing else
				assert_eq!(Vesting::vesting_balance(&2), Some(free_balance - sched1.per_block()));

				System::set_block_number(4);
				assert_eq!(System::block_number(), 4);
				// sched1 has freeing funds at block #4, but nothing else
				assert_eq!(
					Vesting::vesting_balance(&2),
					Some(free_balance - sched1.per_block() * 4),
				);

				let sched2 = VestingInfo::try_new::<Test>(
					existential_deposit * 30,
					existential_deposit, // Vesting over 30 blocks
					5,
				)
				.unwrap();
				// Add a 3rd schedule for user t2
				assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, sched2));

				System::set_block_number(9);
				assert_eq!(System::block_number(), 9);
				// Free balance is equal to the two existing schedules total amount
				let free_balance = Balances::free_balance(&2);
				assert_eq!(free_balance, existential_deposit * (10 + 20 + 30));
				// sched1 and sched2 are freeing funds at block #9
				assert_eq!(
					Vesting::vesting_balance(&2),
					Some(free_balance - sched1.per_block() * 9 - sched2.per_block() * 4)
				);

				System::set_block_number(20);
				assert_eq!(System::block_number(), 20);
				assert_eq!(
					Vesting::vesting_balance(&2),
					Some(
						free_balance -
							sched1.locked() - sched2.per_block() * 15 -
							sched0.per_block() * 10
					)
				);

				System::set_block_number(30);
				assert_eq!(System::block_number(), 30);
				assert_eq!(
					Vesting::vesting_balance(&2),
					Some(
						free_balance - sched1.locked() - sched2.per_block() * 25 - sched0.locked()
					)
				);

				// Fully vested now that sched2 has finished
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

				// `per_block` is 0.
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

				// Add max amount schedules to user 4, (additionally asserting that vested_transfer
				// works with multiple schedules).
				for _ in 0..<Test as Config>::MaxVestingSchedules::get() - 1 {
					assert_ok!(Vesting::vested_transfer(Some(4).into(), 2, user2_vesting_schedule));
				}
				// Try to insert a 4th vesting schedule when `MaxVestingSchedules` === 3.
				assert_noop!(
					Vesting::vested_transfer(Some(4).into(), 2, user2_vesting_schedule),
					Error::<Test>::AtMaxVestingSchedules,
				);
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

			let new_vesting_schedule = VestingInfo::try_new::<Test>(
				256 * 5,
				64, // Vesting over 20 blocks
				10,
			)
			.unwrap();

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

			// Add max amount schedules to user 4, (additionally asserting that force_vested_transfer
			// works with multiple schedules).
			for _ in 0 .. <Test as Config>::MaxVestingSchedules::get() - 1 {
				assert_ok!(Vesting::force_vested_transfer(
					RawOrigin::Root.into(),
					4,
					2,
					new_vesting_schedule
				));
			}
			// Try to insert a 4th vesting schedule when `MaxVestingSchedules` === 3.
			assert_noop!(
				Vesting::vested_transfer(Some(4).into(), 2, user2_vesting_schedule),
				Error::<Test>::AtMaxVestingSchedules,
			);
		});
	}

	#[test]
	fn max_vesting_schedules_bounds_vesting_schedules() {
		let existential_deposit = 256;
		// Test `vested_transfer`
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				let new_vesting_schedule =
					VestingInfo::try_new::<Test>(existential_deposit * 5, existential_deposit, 10)
						.unwrap();

				assert_eq!(Vesting::vesting(&3), None);
				for _ in 0 .. <Test as Config>::MaxVestingSchedules::get() {
					assert_ok!(Vesting::vested_transfer(Some(4).into(), 3, new_vesting_schedule));
				}
				assert_noop!(
					Vesting::vested_transfer(Some(4).into(), 3, new_vesting_schedule),
					Error::<Test>::AtMaxVestingSchedules,
				);
			});

		// Test `force_vested_transfer`
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				let new_vesting_schedule =
					VestingInfo::try_new::<Test>(existential_deposit * 5, existential_deposit, 10)
						.unwrap();

				assert_eq!(Vesting::vesting(&3), None);
				for _ in 0 .. <Test as Config>::MaxVestingSchedules::get() {
					assert_ok!(
						Vesting::force_vested_transfer(
							RawOrigin::Root.into(),
							4,
							3,
							new_vesting_schedule
						)
					);
				}
				assert_noop!(
					Vesting::force_vested_transfer(
						RawOrigin::Root.into(),
						4,
						3,
						new_vesting_schedule
					),
					Error::<Test>::AtMaxVestingSchedules,
				);
			});
	}

	#[test]
	fn merge_schedules_that_have_not_started() {
		// Merging schedules that have not started works
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 =
					VestingInfo::try_new::<Test>(existential_deposit * 20, existential_deposit, 10)
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
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 = VestingInfo::try_new::<Test>(
					existential_deposit * 20,
					existential_deposit, // Vest over 20 blocks
					10,
				)
				.unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

				let sched1 = VestingInfo::try_new::<Test>(
					300 * 10,
					300, // Vest over 10 blocks
					sched0.starting_block() + 5,
				)
				.unwrap();
				Vesting::vested_transfer(Some(4).into(), 2, sched1).unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap().len(), 2);
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);

				// Got to half way through the second schedule where both schedules are actively vesting
				let cur_block = (sched1.ending_block::<Identity>() - sched1.starting_block()) / 2 +
					sched1.starting_block();
				assert_eq!(cur_block, 20);

				System::set_block_number(cur_block);

				// user2 has no usable balances prior to the merge because they have not vested yet
				assert_eq!(Balances::usable_balance(&2), 0);
				Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();

				// Merging schedules vests all pre-existing schedules prior to merging, which is reflected
				// in user2's updated usable balance
				let sched0_vested_now = sched0.per_block() * (cur_block - sched0.starting_block());
				let sched1_vested_now = sched1.per_block() * (cur_block - sched1.starting_block());
				assert_eq!(Balances::usable_balance(&2), sched0_vested_now + sched1_vested_now);

				// The locked amount is the sum of schedules locked minus the amount that each schedule
				// has vested up until the current block.
				let sched2_locked = sched1
					.locked_at::<Identity>(cur_block)
					.saturating_add(sched0.locked_at::<Identity>(cur_block));
				// End block of the new schedule is the greater of either merged schedule
				let sched2_end =
					sched1.ending_block::<Identity>().max(sched0.ending_block::<Identity>());
				let sched2_remaining_blocks = sched2_end - cur_block;
				let sched2_per_block = sched2_locked / sched2_remaining_blocks;
				let sched2 =
					VestingInfo::try_new::<Test>(sched2_locked, sched2_per_block, cur_block)
						.unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2]);
			});
	}

	#[test]
	fn merging_shifts_other_schedules_index() {
		// Schedules being merged are filtered out, schedules to the right of any merged
		// schedule shift left and the new schedule is last
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				let sched0 = VestingInfo::try_new::<Test>(
					existential_deposit * 10,
					existential_deposit, // Vesting over 10 blocks
					10,
				)
				.unwrap();
				let sched1 = VestingInfo::try_new::<Test>(
					existential_deposit * 11,
					existential_deposit, // Vesting over 11 blocks
					11,
				)
				.unwrap();
				let sched2 = VestingInfo::try_new::<Test>(
					existential_deposit * 12,
					existential_deposit, // Vesting over 12 blocks
					12,
				)
				.unwrap();

				// Account 3 start out with no schedules
				assert_eq!(Vesting::vesting(&3), None);
				// and some usable balance.
				let usable_balance = Balances::usable_balance(&3);
				assert_eq!(usable_balance, 30 * existential_deposit);

				let cur_block = 1;
				assert_eq!(System::block_number(), cur_block);

				// Transfer the above 3 schedules to account 3
				Vesting::vested_transfer(Some(4).into(), 3, sched0).unwrap();
				Vesting::vested_transfer(Some(4).into(), 3, sched1).unwrap();
				Vesting::vested_transfer(Some(4).into(), 3, sched2).unwrap();

				// With no schedules vested or merged they are in the order they are created
				assert_eq!(Vesting::vesting(&3).unwrap(), vec![sched0, sched1, sched2]);
				// and the usable balance has not changed
				assert_eq!(usable_balance, Balances::usable_balance(&3));

				Vesting::merge_schedules(Some(3).into(), 0, 2).unwrap();

				// Create the merged schedule of sched0 & sched2.
				let sched3_start =
					sched1.starting_block().max(sched2.starting_block()).max(cur_block);
				let sched3_locked = sched2
					.locked_at::<Identity>(cur_block)
					.saturating_add(sched0.locked_at::<Identity>(cur_block));
				// End block of the new schedule is the greater of either schedule.
				let sched3_end =
					sched2.ending_block::<Identity>().max(sched0.ending_block::<Identity>());
				let sched3_remaining_blocks = sched3_end - sched3_start;
				let sched3_per_block = sched3_locked / sched3_remaining_blocks;
				let sched3 =
					VestingInfo::try_new::<Test>(sched3_locked, sched3_per_block, sched3_start)
						.unwrap();

				let sched0_vested_now = sched0.per_block() *
					(cur_block.max(sched0.starting_block()) - sched0.starting_block());
				let sched1_vested_now = sched1.per_block() *
					(cur_block.max(sched1.starting_block()) - sched1.starting_block());
				let sched2_vested_now = sched2.per_block() *
					(cur_block.max(sched2.starting_block()) - sched2.starting_block());
				// The not touched schedule moves left and the new merged schedule is appended.
				assert_eq!(Vesting::vesting(&3).unwrap(), vec![sched1, sched3]);
				// and the usable balance increases by how much the original schedules vested through
				// the current block
				assert_eq!(
					Balances::usable_balance(&3),
					usable_balance + sched1_vested_now + sched0_vested_now + sched2_vested_now
				);
			});
	}

	#[test]
	fn merge_ongoing_schedule_and_yet_to_be_started_schedule() {
		// Merging an ongoing schedule and one that has not started yet works
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 = VestingInfo::try_new::<Test>(
					existential_deposit * 20,
					existential_deposit, // Vesting over 20 blocks
					10,
				)
				.unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap()[0], sched0);
				assert_eq!(Vesting::vesting(&2).unwrap().len(), 1);

				// Fast forward to half way through the life of sched_1
				let mut cur_block = sched0.starting_block() + sched0.ending_block::<Identity>() / 2;
				System::set_block_number(cur_block);
				assert_eq!(Balances::usable_balance(&2), 0);

				// Prior to vesting there is no usable balance
				let mut usable_balance = 0;
				assert_eq!(Balances::usable_balance(&2), usable_balance);
				// We are also testing the behavior of when vest has been called on one of the
				// schedules prior to merging.
				Vesting::vest(Some(2).into()).unwrap();

				// After vesting the usable balance increases by the amount the vested amount
				let sched0_vested_now =
					(cur_block - sched0.starting_block()) * sched0.per_block();
				usable_balance += sched0_vested_now;
				assert_eq!(Balances::usable_balance(&2), usable_balance);

				// Go forward a block
				cur_block += 1;

				System::set_block_number(cur_block);

				// And add a schedule that starts after this block, but before sched0 finishes.
				let sched1 = VestingInfo::try_new::<Test>(
					existential_deposit * 10,
					1, // Vesting over 256 * 10 (2560) blocks
					cur_block + 1,
				)
				.unwrap();
				Vesting::vested_transfer(Some(4).into(), 2, sched1).unwrap();

				// Merge the schedules before sched1 starts.
				Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();
				// The usable balance only changes by the amount sched0 vested since we last called `vest`
				// and is not affected by sched1 which has not started yet.
				usable_balance += sched0.per_block();
				assert_eq!(Balances::usable_balance(&2), usable_balance);

				// The resulting schedule will have the later starting block of the two.
				let sched2_start = sched1.starting_block();
				let sched2_locked = sched0
					.locked_at::<Identity>(cur_block)
					.saturating_add(sched1.locked_at::<Identity>(cur_block));
				// End block of the new schedule is the greater of either schedule.
				let sched2_end =
					sched0.ending_block::<Identity>().max(sched1.ending_block::<Identity>());
				let sched2_remaining_blocks = sched2_end - sched2_start;
				let sched2_per_block = sched2_locked / sched2_remaining_blocks;
				let sched2 =
					VestingInfo::try_new::<Test>(sched2_locked, sched2_per_block, sched2_start)
						.unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2]);

			});
	}

	#[test]
	fn merge_schedules_with_zero_values_does_not_create_new_schedules() {
		ExtBuilder::default().existential_deposit(256).build().execute_with(|| {});
	}

	#[test]
	fn merge_vesting_info_handles_per_block_0() {
		// Faulty schedules with an infinite duration (per_block == 0) can be merged to create
		// a schedule that vest 1 per_block (helpful for faulty legacy schedules)
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Merge a two schedules both with a duration greater than there
				// locked amount
				let sched0 = VestingInfo::unsafe_new(existential_deposit, 0, 1);
				let sched1 = VestingInfo::unsafe_new(existential_deposit * 2, 0, 10);

				let cur_block = 5;
				let merged_locked = sched0.locked_at::<Identity>(cur_block) +
					sched1.locked_at::<Identity>(cur_block);
				let merged_sched = VestingInfo::try_new::<Test>(
					merged_locked,
					1, // Merged schedule will have a per_block of 1
					10,
				)
				.unwrap();
				assert_eq!(
					merged_sched,
					Vesting::merge_vesting_info(cur_block, sched0, sched1).unwrap()
				);
			});
	}

	#[test]
	fn merge_finishing_and_ongoing_schedule() {
		// If a schedule finishes by the block we treat the ongoing schedule as the merged one
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 =
					VestingInfo::try_new::<Test>(existential_deposit * 20, existential_deposit, 10)
						.unwrap();
				assert_eq!(sched0.ending_block::<Identity>(), 30);
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

				let sched1 =
					VestingInfo::try_new::<Test>(existential_deposit * 40, existential_deposit, 10)
						.unwrap();
				assert_eq!(sched1.ending_block::<Identity>(), 50);
				Vesting::vested_transfer(Some(4).into(), 2, sched1).unwrap();

				// Transfer a 3rd schedule, so we can demonstrate how schedule indices change
				// (We are not merging this schedule)
				let sched2 =
					VestingInfo::try_new::<Test>(existential_deposit * 30, existential_deposit, 10)
						.unwrap();
				Vesting::vested_transfer(Some(3).into(), 2, sched2).unwrap();

				// Current schedule order, prior to any merging
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1, sched2]);

				// Fast forward to sched0's end block
				let current_block = sched0.ending_block::<Identity>();
				System::set_block_number(current_block);

				assert_eq!(System::block_number(), 30);
				// Prior to merge_schedules and with no vest/vest_other called the user has no usable
				// balance.
				assert_eq!(Balances::usable_balance(&2), 0);
				Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();

				// sched2 is now the first, since sched0 & sched1 get filtered out while "merging".
				// sched1 gets treated like the new merged schedule by getting pushed onto back
				// of the vesting schedules vec. Note: sched0 finished at the current block.
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched2, sched1]);

				let sched0_vested_now = sched0.per_block() *
					(sched0.ending_block::<Identity>() - sched0.starting_block());
				let sched1_vested_now =
					sched1.per_block() * (current_block - sched1.starting_block());
				let sched2_vested_now =
					sched2.per_block() * (current_block - sched2.starting_block());
				// The users usable balance after merging includes all pre-existing
				// schedules vested through the current block, including schedules not merged
				assert_eq!(
					Balances::usable_balance(&2),
					sched0_vested_now + sched1_vested_now + sched2_vested_now
				);
			});
	}

	#[test]
	fn merge_finishing_schedules_does_not_create_a_new_one() {
		// If both schedules finish by the current block we don't create new one
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 =
					VestingInfo::try_new::<Test>(existential_deposit * 20, existential_deposit, 10)
						.unwrap();
				assert_eq!(sched0.ending_block::<Identity>(), 30);
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0]);

				let sched1 =
					VestingInfo::try_new::<Test>(existential_deposit * 30, existential_deposit, 10)
						.unwrap();
				assert_eq!(sched1.ending_block::<Identity>(), 40);
				Vesting::vested_transfer(Some(3).into(), 2, sched1).unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched1]);

				let all_scheds_end =
					sched0.ending_block::<Identity>().max(sched1.ending_block::<Identity>());
				assert_eq!(all_scheds_end, 40);
				System::set_block_number(all_scheds_end);
				// Prior to merge_schedules and with no vest/vest_other called the user has no usable
				// balance.
				assert_eq!(Balances::usable_balance(&2), 0);
				Vesting::merge_schedules(Some(2).into(), 0, 1).unwrap();
				// The user no longer has any more vesting schedules because they both ended at the
				// block they where merged
				assert_eq!(Vesting::vesting(&2), None);

				let sched0_vested_now = sched0.per_block() *
					(sched0.ending_block::<Identity>() - sched0.starting_block());
				let sched1_vested_now = sched1.per_block() *
					(sched1.ending_block::<Identity>() - sched1.starting_block());
				assert_eq!(Balances::usable_balance(&2), sched0_vested_now + sched1_vested_now);
			});
	}

	#[test]
	fn merge_schedules_throws_proper_errors() {
		let existential_deposit = 256;
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.build()
			.execute_with(|| {
				// Account 2 should already have a vesting schedule.
				let sched0 =
					VestingInfo::try_new::<Test>(existential_deposit * 20, existential_deposit, 10)
						.unwrap();

				// Not enough vesting schedules
				assert_eq!(Vesting::vesting(&2).unwrap().len(), 1);
				assert_noop!(
					Vesting::merge_schedules(Some(2).into(), 0, 1),
					Error::<Test>::ScheduleIndexOutOfBounds
				);

			// Enough schedules to merge but an index is non-existent
			Vesting::vested_transfer(Some(3).into(), 2, sched0).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap(), vec![sched0, sched0]);
			assert_noop!(
				Vesting::merge_schedules(Some(2).into(), 0, 2),
				Error::<Test>::ScheduleIndexOutOfBounds
			);

			// Index >= max allowed schedules
			let max_schedules = <Test as Config>::MaxVestingSchedules::get();
			Vesting::vested_transfer(Some(4).into(), 2, sched0).unwrap();
			assert_eq!(Vesting::vesting(&2).unwrap().len(), max_schedules as usize);
			assert_noop!(
				Vesting::merge_schedules(Some(2).into(), 0, max_schedules),
				Error::<Test>::ScheduleIndexOutOfBounds
			);

				// Essentially a noop with no errors if indexes are the same.
				let cur_scheds = Vesting::vesting(&2);
				let usable_balance = Balances::usable_balance(&2);
				assert_ok!(Vesting::merge_schedules(Some(2).into(), 0, 0));
				// The relevant storage is invariant.
				assert_eq!(Vesting::vesting(&2), cur_scheds);
				assert_eq!(usable_balance, Balances::usable_balance(&2));
			});
	}

	#[test]
	fn generates_multiple_schedules_from_genesis_config() {
		let existential_deposit = 256;
		let vesting_config = vec![
			// 5 * existential_deposit locked
			(1, 0, 10, 5 * existential_deposit),
			// 1 * existential_deposit locked
			(2, 10, 20, 19 * existential_deposit),
			// 2 * existential_deposit locked
			(2, 10, 20, 18 * existential_deposit),
			// 1 * existential_deposit locked
			(12, 10, 20, 9 * existential_deposit),
			// 2 * existential_deposit locked
			(12, 10, 20, 8 * existential_deposit),
			// 3 * existential_deposit locked
			(12, 10, 20, 7 * existential_deposit),
		];
		ExtBuilder::default()
			.existential_deposit(existential_deposit)
			.vesting_genesis_config(vesting_config)
			.build()
			.execute_with(|| {
				let user1_sched1 =
					VestingInfo::try_new::<Test>(5 * existential_deposit, 128, 0u64).unwrap();
				assert_eq!(Vesting::vesting(&1).unwrap(), vec![user1_sched1]);

				let user2_sched1 =
					VestingInfo::try_new::<Test>(1 * existential_deposit, 12, 10u64).unwrap();
				let user2_sched2 =
					VestingInfo::try_new::<Test>(2 * existential_deposit, 25, 10u64).unwrap();
				assert_eq!(Vesting::vesting(&2).unwrap(), vec![user2_sched1, user2_sched2]);

				let user12_sched1 =
					VestingInfo::try_new::<Test>(1 * existential_deposit, 12, 10u64).unwrap();
				let user12_sched2 =
					VestingInfo::try_new::<Test>(2 * existential_deposit, 25, 10u64).unwrap();
				let user12_sched3 =
					VestingInfo::try_new::<Test>(3 * existential_deposit, 38, 10u64).unwrap();
				assert_eq!(
					Vesting::vesting(&12).unwrap(),
					vec![user12_sched1, user12_sched2, user12_sched3]
				);
			});
	}

	#[test]
	fn vesting_info_validation_works() {
		let min_transfer = <Test as Config>::MinVestedTransfer::get();
		// `locked` cannot be less than min_transfer (non 0 case)
		match VestingInfo::try_new::<Test>(min_transfer - 1, 1u64, 10u64) {
			Err(Error::<Test>::AmountLow) => (),
			_ => panic!(),
		}
		// `locked` cannot be 0
		match VestingInfo::try_new::<Test>(0, 1u64, 10u64) {
			Err(Error::<Test>::InvalidScheduleParams) => (),
			_ => panic!(),
		}
		// `per_block` cannot be 0
		match VestingInfo::try_new::<Test>(min_transfer + 1, 0u64, 10u64) {
			Err(Error::<Test>::InvalidScheduleParams) => (),
			_ => panic!(),
		}
		// Valid inputs
		let ok_sched = VestingInfo::try_new::<Test>(min_transfer, 1u64, 10u64);
		assert!(ok_sched.is_ok());
		assert_eq!(ok_sched.unwrap(), VestingInfo::unsafe_new(min_transfer, 1u64, 10u64));
		// `per_block` is never bigger than `locked`
		assert_eq!(
			VestingInfo::try_new::<Test>(256u64, 256 * 2u64, 10u64).unwrap(),
			VestingInfo::try_new::<Test>(256u64, 256u64, 10u64).unwrap()
		);
	}

	#[test]
	fn vesting_info_ending_block_works() {
		// Treats `per_block` 0 as a `per_block` of 1
		let per_block_0 = VestingInfo::unsafe_new(256u32, 0u32, 10u32);
		let per_block_1 = VestingInfo::try_new::<Test>(256u32, 1u32, 10u32).unwrap();
		assert_eq!(
			per_block_0.ending_block::<Identity>(),
			per_block_0.locked() + per_block_0.starting_block()
		);
		assert_eq!(per_block_0.ending_block::<Identity>(), per_block_1.ending_block::<Identity>());

		// `per_block >= locked` always results in a schedule ending the block after it starts
		let per_block_gt_locked = VestingInfo::unsafe_new(256u32, 256 * 2u32, 10u32);
		let per_block_eq_locked = VestingInfo::try_new::<Test>(256u32, 256u32, 10u32).unwrap();
		assert_eq!(
			per_block_gt_locked.ending_block::<Identity>(),
			1 + per_block_gt_locked.starting_block()
		);
		assert_eq!(
			per_block_gt_locked.ending_block::<Identity>(),
			per_block_eq_locked.ending_block::<Identity>()
		);

		// Correctly calcs end if `locked % per_block != 0`
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
