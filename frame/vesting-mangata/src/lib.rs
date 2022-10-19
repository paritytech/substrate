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
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
mod vesting_info;

pub mod weights;

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	ensure,
	pallet_prelude::*,
	traits::{
		tokens::currency::{MultiTokenCurrency, MultiTokenLockableCurrency},
		ExistenceRequirement, Get, LockIdentifier, WithdrawReasons,
	},
};
use frame_system::{ensure_root, ensure_signed, pallet_prelude::*};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{
		AtLeast32BitUnsigned, Bounded, CheckedSub, Convert, MaybeSerializeDeserialize, One,
		Saturating, StaticLookup, Zero,
	},
	RuntimeDebug,
};
use sp_std::{convert::TryInto, fmt::Debug, prelude::*};
pub use vesting_info::*;
pub use weights::WeightInfo;

type BalanceOf<T> =
	<<T as Config>::Tokens as MultiTokenCurrency<<T as frame_system::Config>::AccountId>>::Balance;
type TokenIdOf<T> = <<T as Config>::Tokens as MultiTokenCurrency<
	<T as frame_system::Config>::AccountId,
>>::CurrencyId;
type MaxLocksOf<T> = <<T as Config>::Tokens as MultiTokenLockableCurrency<
	<T as frame_system::Config>::AccountId,
>>::MaxLocks;

const VESTING_ID: LockIdentifier = *b"vesting ";

// A value placed in storage that represents the current version of the Vesting storage.
// This value is used by `on_runtime_upgrade` to determine whether we run storage migration logic.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug, MaxEncodedLen, TypeInfo)]
enum Releases {
	V0,
	V1,
}

impl Default for Releases {
	fn default() -> Self {
		Releases::V0
	}
}

/// Actions to take against a user's `Vesting` storage entry.
#[derive(Clone, Copy)]
enum VestingAction {
	/// Do not actively remove any schedules.
	Passive,
	/// Remove the schedule specified by the index.
	Remove(usize),
	/// Remove the two schedules, specified by index, so they can be merged.
	Merge(usize, usize),
}

impl VestingAction {
	/// Whether or not the filter says the schedule index should be removed.
	fn should_remove(&self, index: usize) -> bool {
		match self {
			Self::Passive => false,
			Self::Remove(index1) => *index1 == index,
			Self::Merge(index1, index2) => *index1 == index || *index2 == index,
		}
	}

	/// Pick the schedules that this action dictates should continue vesting undisturbed.
	fn pick_schedules<'a, T: Config>(
		&'a self,
		schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>,
	) -> impl Iterator<Item = VestingInfo<BalanceOf<T>, T::BlockNumber>> + 'a {
		schedules.into_iter().enumerate().filter_map(move |(index, schedule)| {
			if self.should_remove(index) {
				None
			} else {
				Some(schedule)
			}
		})
	}
}

// Wrapper for `T::MAX_VESTING_SCHEDULES` to satisfy `trait Get`.
pub struct MaxVestingSchedulesGet<T>(PhantomData<T>);
impl<T: Config> Get<u32> for MaxVestingSchedulesGet<T> {
	fn get() -> u32 {
		T::MAX_VESTING_SCHEDULES
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The tokens trait.
		type Tokens: MultiTokenLockableCurrency<Self::AccountId>;

		/// Convert the block number into a balance.
		type BlockNumberToBalance: Convert<Self::BlockNumber, BalanceOf<Self>>;

		/// The minimum amount transferred to call `vested_transfer`.
		#[pallet::constant]
		type MinVestedTransfer: Get<BalanceOf<Self>>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Maximum number of vesting schedules an account may have at a given moment.
		const MAX_VESTING_SCHEDULES: u32;
	}

	#[pallet::extra_constants]
	impl<T: Config> Pallet<T> {
		// TODO: rename to snake case after https://github.com/paritytech/substrate/issues/8826 fixed.
		#[allow(non_snake_case)]
		fn MaxVestingSchedules() -> u32 {
			T::MAX_VESTING_SCHEDULES
		}
	}

	/// Information regarding the vesting of a given account.
	#[pallet::storage]
	#[pallet::getter(fn vesting)]
	pub type Vesting<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Blake2_128Concat,
		TokenIdOf<T>,
		BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, MaxVestingSchedulesGet<T>>,
	>;

	/// Storage version of the pallet.
	///
	/// New networks start with latest version, as determined by the genesis build.
	#[pallet::storage]
	pub(crate) type StorageVersion<T: Config> = StorageValue<_, Releases, ValueQuery>;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub vesting:
			Vec<(T::AccountId, TokenIdOf<T>, T::BlockNumber, T::BlockNumber, BalanceOf<T>)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig { vesting: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			// Genesis uses the latest storage version.
			StorageVersion::<T>::put(Releases::V1);

			// Generate initial vesting configuration
			// * who - Account which we are generating vesting configuration for
			// * begin - Block when the account will start to vest
			// * length - Number of blocks from `begin` until fully vested
			// * locked - Number of units which are locked for vesting
			for &(ref who, token_id, begin, length, locked) in self.vesting.iter() {
				let length_as_balance = T::BlockNumberToBalance::convert(length);
				let per_block = locked / length_as_balance.max(sp_runtime::traits::One::one());
				let vesting_info = VestingInfo::new(locked, per_block, begin);
				if !vesting_info.is_valid() {
					panic!("Invalid VestingInfo params at genesis")
				};

				Vesting::<T>::try_append(who, token_id, vesting_info)
					.expect("Too many vesting schedules at genesis.");

				let reasons = WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE;
				T::Tokens::set_lock(token_id, VESTING_ID, who, locked, reasons);
			}
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// The amount vested has been updated. This could indicate a change in funds available.
		/// The balance given is the amount which is left unvested (and thus locked).
		/// \[account, unvested\]
		VestingUpdated(T::AccountId, TokenIdOf<T>, BalanceOf<T>),
		/// An \[account\] has become fully vested.
		VestingCompleted(T::AccountId, TokenIdOf<T>),
	}

	/// Error for the vesting pallet.
	#[pallet::error]
	pub enum Error<T> {
		/// The account given is not vesting.
		NotVesting,
		/// The account already has `MaxVestingSchedules` count of schedules and thus
		/// cannot add another one. Consider merging existing schedules in order to add another.
		AtMaxVestingSchedules,
		/// Amount being transferred is too low to create a vesting schedule.
		AmountLow,
		/// An index was out of bounds of the vesting schedules.
		ScheduleIndexOutOfBounds,
		/// Failed to create a new schedule because some parameter was invalid.
		InvalidScheduleParams,
		/// No suitable schedule found
		/// Perhaps the user could merge vesting schedules and try again
		NoSuitableScheduleFound,
		/// Sudo is not allowed to unlock tokens
		SudoUnlockIsDisallowed,
		/// The provided vesting index exceeds the current number of vesting schedules
		InvalidVestingIndex,
		/// An overflow or underflow has occured
		MathError,
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
		#[pallet::weight(T::WeightInfo::vest_locked(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES)
			.max(T::WeightInfo::vest_unlocked(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES))
		)]
		pub fn vest(origin: OriginFor<T>, token_id: TokenIdOf<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_vest(who, token_id)
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
		#[pallet::weight(T::WeightInfo::vest_other_locked(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES)
			.max(T::WeightInfo::vest_other_unlocked(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES))
		)]
		pub fn vest_other(
			origin: OriginFor<T>,
			token_id: TokenIdOf<T>,
			target: <T::Lookup as StaticLookup>::Source,
		) -> DispatchResult {
			ensure_signed(origin)?;
			let who = T::Lookup::lookup(target)?;
			Self::do_vest(who, token_id)
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
		/// NOTE: This will unlock all schedules through the current block.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - DbWeight: 4 Reads, 4 Writes
		///     - Reads: Vesting Storage, Balances Locks, Target Account, Source Account
		///     - Writes: Vesting Storage, Balances Locks, Target Account, Source Account
		/// # </weight>
		#[pallet::weight(
			T::WeightInfo::force_vested_transfer(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES)
		)]
		pub fn force_vested_transfer(
			origin: OriginFor<T>,
			token_id: TokenIdOf<T>,
			source: <T::Lookup as StaticLookup>::Source,
			target: <T::Lookup as StaticLookup>::Source,
			schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::do_vested_transfer(source, target, schedule, token_id)
		}

		/// Merge two vesting schedules together, creating a new vesting schedule that unlocks over
		/// the highest possible start and end blocks. If both schedules have already started the
		/// current block will be used as the schedule start; with the caveat that if one schedule
		/// is finished by the current block, the other will be treated as the new merged schedule,
		/// unmodified.
		///
		/// NOTE: If `schedule1_index == schedule2_index` this is a no-op.
		/// NOTE: This will unlock all schedules through the current block prior to merging.
		/// NOTE: If both schedules have ended by the current block, no new schedule will be created
		/// and both will be removed.
		///
		/// Merged schedule attributes:
		/// - `starting_block`: `MAX(schedule1.starting_block, scheduled2.starting_block,
		///   current_block)`.
		/// - `ending_block`: `MAX(schedule1.ending_block, schedule2.ending_block)`.
		/// - `locked`: `schedule1.locked_at(current_block) + schedule2.locked_at(current_block)`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `schedule1_index`: index of the first schedule to merge.
		/// - `schedule2_index`: index of the second schedule to merge.
		#[pallet::weight(
			T::WeightInfo::not_unlocking_merge_schedules(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES)
			.max(T::WeightInfo::unlocking_merge_schedules(MaxLocksOf::<T>::get(), T::MAX_VESTING_SCHEDULES))
		)]
		pub fn merge_schedules(
			origin: OriginFor<T>,
			token_id: TokenIdOf<T>,
			schedule1_index: u32,
			schedule2_index: u32,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if schedule1_index == schedule2_index {
				return Ok(())
			};
			let schedule1_index = schedule1_index as usize;
			let schedule2_index = schedule2_index as usize;

			let schedules = Self::vesting(&who, token_id).ok_or(Error::<T>::NotVesting)?;
			let merge_action = VestingAction::Merge(schedule1_index, schedule2_index);

			let (schedules, locked_now) = Self::exec_action(schedules.to_vec(), merge_action)?;

			Self::write_vesting(&who, schedules, token_id)?;
			Self::write_lock(&who, locked_now, token_id);

			Ok(())
		}

		// TODO
		// Needs to be benchmarked
		#[pallet::weight(400_000_000u64)]
		pub fn sudo_unlock_all_vesting_tokens(
			origin: OriginFor<T>,
			target: <T::Lookup as StaticLookup>::Source,
			token_id: TokenIdOf<T>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let who = T::Lookup::lookup(target)?;

			Self::do_unlock_all(who, token_id)?;

			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	pub fn get_vesting_locked_at(
		who: &T::AccountId,
		token_id: TokenIdOf<T>,
		at_block_number: Option<T::BlockNumber>,
	) -> Result<Vec<(VestingInfo<BalanceOf<T>, T::BlockNumber>, BalanceOf<T>)>, DispatchError> {
		let at_block_number = at_block_number.unwrap_or(<frame_system::Pallet<T>>::block_number());
		Ok(Self::vesting(&who, token_id)
			.ok_or(Error::<T>::NotVesting)?
			.to_vec()
			.into_iter()
			.map(|x| {
				(
					x.into(),
					BalanceOf::<T>::from(x.locked_at::<T::BlockNumberToBalance>(at_block_number)),
				)
			})
			.collect::<Vec<(VestingInfo<BalanceOf<T>, T::BlockNumber>, BalanceOf<T>)>>())
	}

	// Create a new `VestingInfo`, based off of two other `VestingInfo`s.
	// NOTE: We assume both schedules have had funds unlocked up through the current block.
	fn merge_vesting_info(
		now: T::BlockNumber,
		schedule1: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		schedule2: VestingInfo<BalanceOf<T>, T::BlockNumber>,
	) -> Option<VestingInfo<BalanceOf<T>, T::BlockNumber>> {
		let schedule1_ending_block = schedule1.ending_block_as_balance::<T::BlockNumberToBalance>();
		let schedule2_ending_block = schedule2.ending_block_as_balance::<T::BlockNumberToBalance>();
		let now_as_balance = T::BlockNumberToBalance::convert(now);

		// Check if one or both schedules have ended.
		match (schedule1_ending_block <= now_as_balance, schedule2_ending_block <= now_as_balance) {
			// If both schedules have ended, we don't merge and exit early.
			(true, true) => return None,
			// If one schedule has ended, we treat the one that has not ended as the new
			// merged schedule.
			(true, false) => return Some(schedule2),
			(false, true) => return Some(schedule1),
			// If neither schedule has ended don't exit early.
			_ => {},
		}

		let locked = schedule1
			.locked_at::<T::BlockNumberToBalance>(now)
			.saturating_add(schedule2.locked_at::<T::BlockNumberToBalance>(now));
		// This shouldn't happen because we know at least one ending block is greater than now,
		// thus at least a schedule a some locked balance.
		debug_assert!(
			!locked.is_zero(),
			"merge_vesting_info validation checks failed to catch a locked of 0"
		);

		let ending_block = schedule1_ending_block.max(schedule2_ending_block);
		let starting_block = now.max(schedule1.starting_block()).max(schedule2.starting_block());

		let per_block = {
			let duration = ending_block
				.saturating_sub(T::BlockNumberToBalance::convert(starting_block))
				.max(One::one());
			(locked / duration).max(One::one())
		};

		let schedule = VestingInfo::new(locked, per_block, starting_block);
		debug_assert!(schedule.is_valid(), "merge_vesting_info schedule validation check failed");

		Some(schedule)
	}

	// Execute a vested transfer from `source` to `target` with the given `schedule`.
	fn do_vested_transfer(
		source: <T::Lookup as StaticLookup>::Source,
		target: <T::Lookup as StaticLookup>::Source,
		schedule: VestingInfo<BalanceOf<T>, T::BlockNumber>,
		token_id: TokenIdOf<T>,
	) -> DispatchResult {
		// Validate user inputs.
		ensure!(schedule.locked() >= T::MinVestedTransfer::get(), Error::<T>::AmountLow);
		if !schedule.is_valid() {
			return Err(Error::<T>::InvalidScheduleParams.into())
		};
		let target = T::Lookup::lookup(target)?;
		let source = T::Lookup::lookup(source)?;

		// Check we can add to this account prior to any storage writes.
		Self::can_add_vesting_schedule(
			&target,
			schedule.locked(),
			schedule.per_block(),
			schedule.starting_block(),
			token_id,
		)?;

		T::Tokens::ensure_can_withdraw(
			token_id,
			&source,
			schedule.locked(),
			WithdrawReasons::all(),
			Default::default(),
		)?;

		T::Tokens::transfer(
			token_id,
			&source,
			&target,
			schedule.locked(),
			ExistenceRequirement::AllowDeath,
		)?;

		// We can't let this fail because the currency transfer has already happened.
		let res = Self::add_vesting_schedule(
			&target,
			schedule.locked(),
			schedule.per_block(),
			schedule.starting_block(),
			token_id,
		);
		debug_assert!(res.is_ok(), "Failed to add a schedule when we had to succeed.");

		Ok(())
	}

	/// Iterate through the schedules to track the current locked amount and
	/// filter out completed and specified schedules.
	///
	/// Returns a tuple that consists of:
	/// - Vec of vesting schedules, where completed schedules and those specified
	/// 	by filter are removed. (Note the vec is not checked for respecting
	/// 	bounded length.)
	/// - The amount locked at the current block number based on the given schedules.
	///
	/// NOTE: the amount locked does not include any schedules that are filtered out via `action`.
	fn report_schedule_updates(
		schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>,
		action: VestingAction,
	) -> (Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>, BalanceOf<T>) {
		let now = <frame_system::Pallet<T>>::block_number();

		let mut total_locked_now: BalanceOf<T> = Zero::zero();
		let filtered_schedules = action
			.pick_schedules::<T>(schedules)
			.filter_map(|schedule| {
				let locked_now = schedule.locked_at::<T::BlockNumberToBalance>(now);
				if locked_now.is_zero() {
					None
				} else {
					total_locked_now = total_locked_now.saturating_add(locked_now);
					Some(schedule)
				}
			})
			.collect::<Vec<_>>();

		(filtered_schedules, total_locked_now)
	}

	/// Write an accounts updated vesting lock to storage.
	fn write_lock(who: &T::AccountId, total_locked_now: BalanceOf<T>, token_id: TokenIdOf<T>) {
		if total_locked_now.is_zero() {
			T::Tokens::remove_lock(token_id, VESTING_ID, who);
			Self::deposit_event(Event::<T>::VestingCompleted(who.clone(), token_id));
		} else {
			let reasons = WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE;
			T::Tokens::set_lock(token_id, VESTING_ID, who, total_locked_now, reasons);
			Self::deposit_event(Event::<T>::VestingUpdated(
				who.clone(),
				token_id,
				total_locked_now,
			));
		};
	}

	/// Write an accounts updated vesting schedules to storage.
	fn write_vesting(
		who: &T::AccountId,
		schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>,
		token_id: TokenIdOf<T>,
	) -> Result<(), DispatchError> {
		let schedules: BoundedVec<
			VestingInfo<BalanceOf<T>, T::BlockNumber>,
			MaxVestingSchedulesGet<T>,
		> = schedules.try_into().map_err(|_| Error::<T>::AtMaxVestingSchedules)?;

		if schedules.len() == 0 {
			Vesting::<T>::remove(&who, token_id);
		} else {
			Vesting::<T>::insert(who, token_id, schedules)
		}

		Ok(())
	}

	/// Unlock any vested funds of `who`.
	fn do_vest(who: T::AccountId, token_id: TokenIdOf<T>) -> DispatchResult {
		let schedules = Self::vesting(&who, token_id).ok_or(Error::<T>::NotVesting)?;

		let (schedules, locked_now) =
			Self::exec_action(schedules.to_vec(), VestingAction::Passive)?;

		Self::write_vesting(&who, schedules, token_id)?;
		Self::write_lock(&who, locked_now, token_id);

		Ok(())
	}

	/// Unlock all token_id tokens of `who`.
	fn do_unlock_all(who: T::AccountId, token_id: TokenIdOf<T>) -> DispatchResult {
		Self::write_vesting(&who, Default::default(), token_id)?;
		Self::write_lock(&who, Default::default(), token_id);

		Ok(())
	}

	/// Execute a `VestingAction` against the given `schedules`. Returns the updated schedules
	/// and locked amount.
	fn exec_action(
		schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>,
		action: VestingAction,
	) -> Result<(Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>>, BalanceOf<T>), DispatchError> {
		let (schedules, locked_now) = match action {
			VestingAction::Merge(idx1, idx2) => {
				// The schedule index is based off of the schedule ordering prior to filtering out
				// any schedules that may be ending at this block.
				let schedule1 = *schedules.get(idx1).ok_or(Error::<T>::ScheduleIndexOutOfBounds)?;
				let schedule2 = *schedules.get(idx2).ok_or(Error::<T>::ScheduleIndexOutOfBounds)?;

				// The length of `schedules` decreases by 2 here since we filter out 2 schedules.
				// Thus we know below that we can push the new merged schedule without error
				// (assuming initial state was valid).
				let (mut schedules, mut locked_now) =
					Self::report_schedule_updates(schedules.to_vec(), action);

				let now = <frame_system::Pallet<T>>::block_number();
				if let Some(new_schedule) = Self::merge_vesting_info(now, schedule1, schedule2) {
					// Merging created a new schedule so we:
					// 1) need to add it to the accounts vesting schedule collection,
					schedules.push(new_schedule);
					// (we use `locked_at` in case this is a schedule that started in the past)
					let new_schedule_locked =
						new_schedule.locked_at::<T::BlockNumberToBalance>(now);
					// and 2) update the locked amount to reflect the schedule we just added.
					locked_now = locked_now.saturating_add(new_schedule_locked);
				} // In the None case there was no new schedule to account for.

				(schedules, locked_now)
			},
			_ => Self::report_schedule_updates(schedules.to_vec(), action),
		};

		debug_assert!(
			locked_now > Zero::zero() && schedules.len() > 0 ||
				locked_now == Zero::zero() && schedules.len() == 0
		);

		Ok((schedules, locked_now))
	}
}

pub trait MultiTokenVestingLocks<AccountId, BlockNumber> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// The currency that this schedule applies to.
	type Currency: MultiTokenCurrency<AccountId>;

	/// Finds a vesting schedule with locked_at value greater than unlock_amount
	/// Removes that old vesting schedule, adds a new one with new_locked and new_per_block
	/// reflecting old locked_at - unlock_amount, to be unlocked by old ending block.
	/// This does not transfer funds
	fn unlock_tokens(
		who: &AccountId,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
		unlock_amount: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
	) -> Result<
		(BlockNumber, <Self::Currency as MultiTokenCurrency<AccountId>>::Balance),
		DispatchError,
	>;

	/// Finds the vesting schedule with the provided index
	/// Removes that old vesting schedule, adds a new one with new_locked and new_per_block
	/// reflecting old locked_at - unlock_amount, to be unlocked by old ending block.
	/// This does not transfer funds
	fn unlock_tokens_by_vesting_index(
		who: &AccountId,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
		vesting_index: u32,
		unlock_some_amount_or_all: Option<
			<Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		>,
	) -> Result<
		(
			<Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
			BlockNumber,
			<Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		),
		DispatchError,
	>;

	/// Constructs a vesting schedule based on the given data starting from now
	/// And places it into the appropriate (who, token_id) storage
	/// This does not transfer funds
	fn lock_tokens(
		who: &AccountId,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
		lock_amount: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		starting_block_as_balance: Option<BlockNumber>,
		ending_block_as_balance: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
	) -> DispatchResult;
}

impl<T: Config> MultiTokenVestingLocks<T::AccountId, T::BlockNumber> for Pallet<T>
where
	BalanceOf<T>: MaybeSerializeDeserialize + Debug,
	TokenIdOf<T>: MaybeSerializeDeserialize + Debug,
{
	type Currency = T::Tokens;
	type Moment = T::BlockNumber;

	fn unlock_tokens(
		who: &T::AccountId,
		token_id: TokenIdOf<T>,
		unlock_amount: BalanceOf<T>,
	) -> Result<(T::BlockNumber, BalanceOf<T>), DispatchError> {
		let now = <frame_system::Pallet<T>>::block_number();
		// First we get the schedules of who
		let schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>> =
			Self::vesting(who, token_id).ok_or(Error::<T>::NotVesting)?.into();
		// Then we enumerate and iterate through them
		// and select the one which has atleast the `unlock_amount` as `locked_at` in the schedule
		// Amongst the ones that satisfy the above condition we pick the one with least ending_block
		// number index of the schedule to be removed, the schedule, locked_at of the schedule,
		// ending_block_as_balance of the schedule
		let mut selected_schedule: Option<(
			usize,
			VestingInfo<BalanceOf<T>, T::BlockNumber>,
			BalanceOf<T>,
			BalanceOf<T>,
		)> = None;
		for (i, schedule) in schedules.clone().into_iter().enumerate() {
			let schedule_locked_at = schedule.locked_at::<T::BlockNumberToBalance>(now);
			match (schedule_locked_at >= unlock_amount, selected_schedule) {
				(true, None) =>
					selected_schedule = Some((
						i,
						schedule,
						schedule_locked_at,
						schedule.ending_block_as_balance::<T::BlockNumberToBalance>(),
					)),
				(true, Some(currently_selected_schedule)) => {
					let schedule_ending_block_as_balance =
						schedule.ending_block_as_balance::<T::BlockNumberToBalance>();
					if currently_selected_schedule
						.1
						.ending_block_as_balance::<T::BlockNumberToBalance>() >
						schedule_ending_block_as_balance
					{
						selected_schedule = Some((
							i,
							schedule,
							schedule_locked_at,
							schedule_ending_block_as_balance,
						))
					}
				},
				_ => (),
			}
		}

		// Attempt to unwrap selected_schedule
		// If it is still none that means no suitable vesting schedule was found
		// Perhaps the user could merge vesting schedules and try again
		let selected_schedule = selected_schedule.ok_or(Error::<T>::NoSuitableScheduleFound)?;

		// Remove selected_schedule
		let mut updated_schedules = schedules
			.into_iter()
			.enumerate()
			.filter_map(
				move |(index, schedule)| {
					if index == selected_schedule.0 {
						None
					} else {
						Some(schedule)
					}
				},
			)
			.collect::<Vec<_>>();

		let new_locked =
			selected_schedule.2.checked_sub(&unlock_amount).ok_or(Error::<T>::MathError)?;

		let start_block = now.max(selected_schedule.1.starting_block());

		if !new_locked.is_zero() {
			let length_as_balance = selected_schedule
				.3
				.saturating_sub(T::BlockNumberToBalance::convert(start_block))
				.max(One::one());

			// .max in length_as_balance computation protects against unsafe div
			let new_per_block = (new_locked / length_as_balance).max(One::one());

			let vesting_schedule = VestingInfo::new(new_locked, new_per_block, start_block);

			ensure!(vesting_schedule.is_valid(), Error::<T>::InvalidScheduleParams);

			// We just removed an element so this raw push shouldn't fail
			updated_schedules.push(vesting_schedule);
		}

		// This is mostly to calculate locked_now
		// It also removes schedules that represent 0 value locked
		let (updated_schedules, locked_now) =
			Self::exec_action(updated_schedules.to_vec(), VestingAction::Passive)?;

		Self::write_vesting(&who, updated_schedules, token_id)?;
		Self::write_lock(who, locked_now, token_id);

		// Start block, end block
		Ok((start_block, selected_schedule.3))
	}

	fn unlock_tokens_by_vesting_index(
		who: &T::AccountId,
		token_id: TokenIdOf<T>,
		vesting_index: u32,
		unlock_some_amount_or_all: Option<BalanceOf<T>>,
	) -> Result<(BalanceOf<T>, T::BlockNumber, BalanceOf<T>), DispatchError> {
		let now = <frame_system::Pallet<T>>::block_number();

		// First we get the schedules of who
		let schedules: Vec<VestingInfo<BalanceOf<T>, T::BlockNumber>> =
			Self::vesting(who, token_id).ok_or(Error::<T>::NotVesting)?.into();

		// Then we enumerate and iterate through them
		// and select the one which has atleast the `unlock_amount` as `locked_at` in the schedule
		// Amongst the ones that satisfy the above condition we pick the one with least ending_block
		// number index of the schedule to be removed, the schedule, locked_at of the schedule,
		// ending_block_as_balance of the schedule
		let mut selected_schedule: Option<(
			usize,
			VestingInfo<BalanceOf<T>, T::BlockNumber>,
			BalanceOf<T>,
			BalanceOf<T>,
		)> = None;

		for (i, schedule) in schedules.clone().into_iter().enumerate() {
			let schedule_locked_at = schedule.locked_at::<T::BlockNumberToBalance>(now);
			let schedule_locked_at_satisfied: bool =
				if let Some(unlock_amount) = unlock_some_amount_or_all {
					schedule_locked_at >= unlock_amount
				} else {
					true
				};

			match (i == vesting_index as usize && schedule_locked_at_satisfied, selected_schedule) {
				(true, None) =>
					selected_schedule = Some((
						i,
						schedule,
						schedule_locked_at,
						schedule.ending_block_as_balance::<T::BlockNumberToBalance>(),
					)),
				_ => (),
			}
		}

		// Attempt to unwrap selected_schedule
		// If it is still none that means the suitable vesting schedule was not found
		let selected_schedule = selected_schedule.ok_or(Error::<T>::NoSuitableScheduleFound)?;

		// Remove selected_schedule
		let mut updated_schedules = schedules
			.into_iter()
			.enumerate()
			.filter_map(
				move |(index, schedule)| {
					if index == selected_schedule.0 {
						None
					} else {
						Some(schedule)
					}
				},
			)
			.collect::<Vec<_>>();

		let start_block = now.max(selected_schedule.1.starting_block());

		let new_locked = if let Some(unlock_amount) = unlock_some_amount_or_all {
			selected_schedule.2.checked_sub(&unlock_amount).ok_or(Error::<T>::MathError)?
		} else {
			BalanceOf::<T>::zero()
		};

		let unlocked_amount = unlock_some_amount_or_all.unwrap_or(selected_schedule.2);

		if !new_locked.is_zero() {
			let length_as_balance = selected_schedule
				.3
				.saturating_sub(T::BlockNumberToBalance::convert(start_block))
				.max(One::one());

			// .max in length_as_balance computation protects against unsafe div
			let new_per_block = (new_locked / length_as_balance).max(One::one());

			let vesting_schedule = VestingInfo::new(new_locked, new_per_block, start_block);

			ensure!(vesting_schedule.is_valid(), Error::<T>::InvalidScheduleParams);

			// We just removed an element so this raw push shouldn't fail
			updated_schedules.push(vesting_schedule);
		}

		// This is mostly to calculate locked_now
		// It also removes schedules that represent 0 value locked
		let (updated_schedules, locked_now) =
			Self::exec_action(updated_schedules.to_vec(), VestingAction::Passive)?;

		Self::write_vesting(&who, updated_schedules, token_id)?;
		Self::write_lock(who, locked_now, token_id);

		// Unlocked amount, start block, end block
		Ok((unlocked_amount, start_block, selected_schedule.3))
	}

	fn lock_tokens(
		who: &T::AccountId,
		token_id: TokenIdOf<T>,
		lock_amount: BalanceOf<T>,
		starting_block: Option<T::BlockNumber>,
		ending_block_as_balance: BalanceOf<T>,
	) -> DispatchResult {
		let starting_block: T::BlockNumber =
			starting_block.unwrap_or(<frame_system::Pallet<T>>::block_number());

		T::Tokens::ensure_can_withdraw(
			token_id,
			who,
			lock_amount,
			WithdrawReasons::all(),
			Default::default(),
		)?;

		let length_as_balance = ending_block_as_balance
			.saturating_sub(T::BlockNumberToBalance::convert(starting_block))
			.max(One::one());
		let per_block = (lock_amount / length_as_balance).max(One::one());

		let vesting_schedule = VestingInfo::new(lock_amount, per_block, starting_block);
		ensure!(vesting_schedule.is_valid(), Error::<T>::InvalidScheduleParams);

		let mut schedules = Self::vesting(who, token_id).unwrap_or_default();
		ensure!(schedules.try_push(vesting_schedule).is_ok(), Error::<T>::AtMaxVestingSchedules);

		let (schedules, locked_now) =
			Self::exec_action(schedules.to_vec(), VestingAction::Passive)?;

		Self::write_vesting(&who, schedules, token_id)?;
		Self::write_lock(who, locked_now, token_id);

		Ok(())
	}
}

/// A vesting schedule over a currency. This allows a particular currency to have vesting limits
/// applied to it.
pub trait MultiTokenVestingSchedule<AccountId> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// The currency that this schedule applies to.
	type Currency: MultiTokenCurrency<AccountId>;

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	/// Returns `None` if the account has no vesting schedule.
	fn vesting_balance(
		who: &AccountId,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
	) -> Option<<Self::Currency as MultiTokenCurrency<AccountId>>::Balance>;

	/// Adds a vesting schedule to a given account.
	///
	/// If the account has `MaxVestingSchedules`, an Error is returned and nothing
	/// is updated.
	///
	/// Is a no-op if the amount to be vested is zero.
	///
	/// NOTE: This doesn't alter the free balance of the account.
	fn add_vesting_schedule(
		who: &AccountId,
		locked: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		per_block: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		starting_block: Self::Moment,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
	) -> DispatchResult;

	/// Checks if `add_vesting_schedule` would work against `who`.
	fn can_add_vesting_schedule(
		who: &AccountId,
		locked: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		per_block: <Self::Currency as MultiTokenCurrency<AccountId>>::Balance,
		starting_block: Self::Moment,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
	) -> DispatchResult;

	/// Remove a vesting schedule for a given account.
	///
	/// NOTE: This doesn't alter the free balance of the account.
	fn remove_vesting_schedule(
		who: &AccountId,
		token_id: <Self::Currency as MultiTokenCurrency<AccountId>>::CurrencyId,
		schedule_index: u32,
	) -> DispatchResult;
}

impl<T: Config> MultiTokenVestingSchedule<T::AccountId> for Pallet<T>
where
	BalanceOf<T>: MaybeSerializeDeserialize + Debug,
	TokenIdOf<T>: MaybeSerializeDeserialize + Debug,
{
	type Currency = T::Tokens;
	type Moment = T::BlockNumber;

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	fn vesting_balance(who: &T::AccountId, token_id: TokenIdOf<T>) -> Option<BalanceOf<T>> {
		if let Some(v) = Self::vesting(who, token_id) {
			let now = <frame_system::Pallet<T>>::block_number();
			let total_locked_now = v.iter().fold(Zero::zero(), |total, schedule| {
				schedule.locked_at::<T::BlockNumberToBalance>(now).saturating_add(total)
			});
			Some(T::Tokens::free_balance(token_id, who).min(total_locked_now))
		} else {
			None
		}
	}

	/// Adds a vesting schedule to a given account.
	///
	/// If the account has `MaxVestingSchedules`, an Error is returned and nothing
	/// is updated.
	///
	/// On success, a linearly reducing amount of funds will be locked. In order to realise any
	/// reduction of the lock over time as it diminishes, the account owner must use `vest` or
	/// `vest_other`.
	///
	/// Is a no-op if the amount to be vested is zero.
	///
	/// NOTE: This doesn't alter the free balance of the account.
	fn add_vesting_schedule(
		who: &T::AccountId,
		locked: BalanceOf<T>,
		per_block: BalanceOf<T>,
		starting_block: T::BlockNumber,
		token_id: TokenIdOf<T>,
	) -> DispatchResult {
		if locked.is_zero() {
			return Ok(())
		}

		let vesting_schedule = VestingInfo::new(locked, per_block, starting_block);
		// Check for `per_block` or `locked` of 0.
		if !vesting_schedule.is_valid() {
			return Err(Error::<T>::InvalidScheduleParams.into())
		};

		let mut schedules = Self::vesting(who, token_id).unwrap_or_default();

		// NOTE: we must push the new schedule so that `exec_action`
		// will give the correct new locked amount.
		ensure!(schedules.try_push(vesting_schedule).is_ok(), Error::<T>::AtMaxVestingSchedules);

		let (schedules, locked_now) =
			Self::exec_action(schedules.to_vec(), VestingAction::Passive)?;

		Self::write_vesting(&who, schedules, token_id)?;
		Self::write_lock(who, locked_now, token_id);

		Ok(())
	}

	// Ensure we can call `add_vesting_schedule` without error. This should always
	// be called prior to `add_vesting_schedule`.
	fn can_add_vesting_schedule(
		who: &T::AccountId,
		locked: BalanceOf<T>,
		per_block: BalanceOf<T>,
		starting_block: T::BlockNumber,
		token_id: TokenIdOf<T>,
	) -> DispatchResult {
		// Check for `per_block` or `locked` of 0.
		if !VestingInfo::new(locked, per_block, starting_block).is_valid() {
			return Err(Error::<T>::InvalidScheduleParams.into())
		}

		ensure!(
			(Vesting::<T>::decode_len(who, token_id).unwrap_or_default() as u32) <
				T::MAX_VESTING_SCHEDULES,
			Error::<T>::AtMaxVestingSchedules
		);

		Ok(())
	}

	/// Remove a vesting schedule for a given account.
	fn remove_vesting_schedule(
		who: &T::AccountId,
		token_id: TokenIdOf<T>,
		schedule_index: u32,
	) -> DispatchResult {
		let schedules = Self::vesting(who, token_id).ok_or(Error::<T>::NotVesting)?;
		let remove_action = VestingAction::Remove(schedule_index as usize);

		let (schedules, locked_now) = Self::exec_action(schedules.to_vec(), remove_action)?;

		Self::write_vesting(&who, schedules, token_id)?;
		Self::write_lock(who, locked_now, token_id);
		Ok(())
	}
}
