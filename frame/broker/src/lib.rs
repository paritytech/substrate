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
#![doc = include_str!("../README.md")]

pub use pallet::*;

mod mock;
mod tests;
mod benchmarking;
mod test_fungibles;
mod types;

pub mod weights;
pub use weights::WeightInfo;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, traits::fungible::{self, Inspect, Mutate, MutateHold}};
	use frame_system::pallet_prelude::*;
	use sp_runtime::{AccountId32, traits::{ConvertBack, Convert}, DispatchError};
	use sp_arithmetic::traits::{AtLeast32BitUnsigned, SaturatedConversion, Saturating};
	use types::CorePart;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	pub type PartsOf57600 = u16;
	pub enum CoreAssignment {
		InstantaneousPool,
		Task(ParaId),
	}
	pub trait CoretimeInterface {
		type AccountId: Parameter;
		type Balance;
		type BlockNumber: AtLeast32BitUnsigned + TypeInfo + Encode;
		fn latest() -> Self::BlockNumber;
		fn request_core_count(count: CoreIndex);
		fn request_revenue_at(when: Self::BlockNumber);
		fn credit_account(who: Self::AccountId, amount: Balance);
		fn assign_core(
			core: CoreIndex,
			begin: Self::BlockNumber,
			assignment: Vec<(CoreAssignment, PartsOf57600)>,
			end_hint: Option<Self::BlockNumber>,
		);
		fn check_notify_core_count() -> Option<u16>;
		fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)>;
	}
	impl CoretimeInterface for () {
		type AccountId = ();
		type Balance = u64;
		type BlockNumber = u32;
		fn latest() -> Self::BlockNumber { 0 }
		fn request_core_count(_count: CoreIndex) {}
		fn request_revenue_at(_when: Self::BlockNumber) {}
		fn credit_account(_who: Self::AccountId, _amount: Balance) {}
		fn assign_core(
			_core: CoreIndex,
			_begin: Self::BlockNumber,
			_assignment: Vec<(CoreAssignment, PartsOf57600)>,
			_end_hint: Option<Self::BlockNumber>,
		) {}
		fn check_notify_core_count() -> Option<u16> { None }
		fn check_notify_revenue_info() -> Option<(Self::BlockNumber, Self::Balance)> { None }
	}

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Currency: Inspect<Self::AccountId>;//Mutate<Self::AccountId> + MutateHold<Self::AccountId>;

		/// Number of Relay-chain blocks ahead of time which we fix and notify of core assignments.
		#[pallet::constant]
		type AdvanceNotice: Get<RelayBlockNumberOf<Self>>;

		/// Number of Relay-chain blocks per timeslice.
		#[pallet::constant]
		type TimeslicePeriod: Get<RelayBlockNumberOf<Self>>;

		/// Reversible conversion from local balance to Relay-chain balance.
		type ConvertBalance: Convert<BalanceOf<Self>, RelayBalanceOf<Self>> + ConvertBack<BalanceOf<Self>, RelayBalanceOf<Self>>;

		/// Relay chain's Coretime API
		type Coretime: CoretimeInterface;

		/// Weight information for all calls of this pallet.
		type WeightInfo: WeightInfo;
	}

	pub type BalanceOf<T> = <<T as Config>::Currency as Inspect<<T as frame_system::Config>::AccountId>>::Balance;
	pub type RelayBalanceOf<T> = <<T as Config>::Coretime as CoretimeInterface>::Balance;
	pub type RelayBlockNumberOf<T> = <<T as Config>::Coretime as CoretimeInterface>::BlockNumber;

	// Relay-chain block number divided by 80.
	pub type Timeslice = u32;
	pub type CoreIndex = u16;
	pub type RelayAccountId = AccountId32;
	pub type Balance = u128;
	pub type ParaId = u32;
	/// Counter for the total CoreParts which could be dedicated to a pool. `u32` so we don't ever
	/// get an overflow.
	pub type PartCount = u32;
	pub type SignedPartCount = i32;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionId {
		begin: Timeslice,
		core: CoreIndex,
		part: CorePart,
	}

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionRecord<AccountId> {
		end: Timeslice,
		owner: AccountId,
	}
	pub type RegionRecordOf<T> = RegionRecord<<T as frame_system::Config>::AccountId>;

	// TODO: Use a more specialised 32-bit type which puts Off and InstaPool into unused 32-bit values.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum CoreTask {
		Off,
		Assigned(ParaId),
		InstaPool,
	}

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ScheduleItem {
		part: CorePart,
		task: CoreTask,
	}
	pub type Schedule = BoundedVec<ScheduleItem, ConstU32<80>>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum Contributor<AccountId> {
		System,
		Private(AccountId),
	}
	pub type ContributorOf<T> = Contributor<<T as frame_system::Config>::AccountId>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ContributionRecord<AccountId> {
		begin: Timeslice,
		end: Timeslice,
		core: CoreIndex,
		part: CorePart,
		payee: Contributor<AccountId>,
	}
	pub type ContributionRecordOf<T> = ContributionRecord<<T as frame_system::Config>::AccountId>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct InstaPoolHistoryRecord<Balance> {
		total_contributions: PartCount,
		maybe_payout: Option<Balance>,
	}
	pub type InstaPoolHistoryRecordOf<T> = InstaPoolHistoryRecord<BalanceOf<T>>;

	#[pallet::storage]
	pub type Regions<T> = StorageMap<_, Blake2_128Concat, RegionId, RegionRecordOf<T>, OptionQuery>;

	/// The work we plan on having each core do at a particular time in the future.
	#[pallet::storage]
	pub type Workplan<T> = StorageMap<_, Twox64Concat, (Timeslice, CoreIndex), Schedule, OptionQuery>;

	/// The current workload of each core. This gets updated with workplan as timeslices pass.
	#[pallet::storage]
	pub type Workload<T> = StorageMap<_, Twox64Concat, CoreIndex, Schedule, OptionQuery>;

	#[pallet::storage]
	pub type InstaPoolSize<T> = StorageValue<_, PartCount, ValueQuery>;

	#[pallet::storage]
	pub type InstaPoolContribution<T> = StorageMap<_, Blake2_128Concat, ContributionRecordOf<T>, (), OptionQuery>;

	#[pallet::storage]
	pub type InstaPoolIo<T> = StorageMap<_, Blake2_128Concat, Timeslice, SignedPartCount, ValueQuery>;

	/// Total InstaPool rewards for each Timeslice and the number of core parts which contributed.
	#[pallet::storage]
	pub type InstaPoolHistory<T> = StorageMap<_, Blake2_128Concat, Timeslice, InstaPoolHistoryRecordOf<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		Transferred {
			region_id: RegionId,
			old_owner: T::AccountId,
			owner: T::AccountId,
		},
		Partitioned {
			region_id: RegionId,
			pivot: Timeslice,
			new_region_id: RegionId,
		},
		Interlaced {
			region_id: RegionId,
			pivot: CorePart,
		},
		Assigned {
			region_id: RegionId,
			task: ParaId,
		},
		Dropped {
			region_id: RegionId,
		},
		Pooled {
			region_id: RegionId,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		UnknownRegion,
		NotOwner,
		PivotTooEarly,
		PivotTooLate,
		ExteriorPivot,
		NullPivot,
		CompletePivot,
		CorruptWorkplan,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			Weight::zero()
		}
	}

	#[pallet::call(weight(<T as Config>::WeightInfo))]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn transfer(origin: OriginFor<T>, region_id: RegionId, new_owner: T::AccountId) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_transfer(region_id, Some(who), new_owner)?;
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		pub(crate) fn next_timeslice() -> Timeslice {
			let latest = T::Coretime::latest();
			let advance = T::AdvanceNotice::get();
			let timeslice_period = T::TimeslicePeriod::get();
			let last_scheduled = (latest + advance) / timeslice_period;
			let mut next_scheduled: Timeslice = last_scheduled.saturated_into();
			next_scheduled.saturating_add(1)
		}

		pub(crate) fn do_transfer(region_id: RegionId, maybe_check_owner: Option<T::AccountId>, new_owner: T::AccountId) -> Result<(), Error<T>> {
			let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

			if let Some(check_owner) = maybe_check_owner {
				ensure!(check_owner == region.owner, Error::<T>::NotOwner);
			}

			let old_owner = region.owner;
			region.owner = new_owner;
			Regions::<T>::insert(&region_id, &region);
			Self::deposit_event(Event::Transferred { region_id, old_owner, owner: region.owner });

			Ok(())
		}

		pub(crate) fn do_partition(
			region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
			pivot: Timeslice,
		) -> Result<(), Error<T>> {
			let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

			if let Some(check_owner) = maybe_check_owner {
				ensure!(check_owner == region.owner, Error::<T>::NotOwner);
			}

			ensure!(pivot > region_id.begin, Error::<T>::PivotTooEarly);
			ensure!(pivot < region.end, Error::<T>::PivotTooLate);

			let new_region_id = RegionId { begin: pivot, ..region_id.clone() };
			let new_region = RegionRecord { end: pivot, ..region.clone() };

			Regions::<T>::insert(&region_id, &new_region);
			Regions::<T>::insert(&new_region_id, &region);
			Self::deposit_event(Event::Partitioned { region_id, pivot, new_region_id });

			Ok(())
		}

		pub(crate) fn do_interlace(
			mut region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
			pivot: CorePart,
		) -> Result<(), Error<T>> {
			let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

			if let Some(check_owner) = maybe_check_owner {
				ensure!(check_owner == region.owner, Error::<T>::NotOwner);
			}

			ensure!((pivot & !region_id.part).is_void(), Error::<T>::ExteriorPivot);
			ensure!(!pivot.is_void(), Error::<T>::NullPivot);
			ensure!(pivot != region_id.part, Error::<T>::CompletePivot);

			let antipivot = region_id.part ^ pivot;
			region_id.part = pivot;
			Regions::<T>::insert(&region_id, &region);
			region_id.part = antipivot;
			Regions::<T>::insert(&region_id, &region);

			Self::deposit_event(Event::Interlaced { region_id, pivot });

			Ok(())
		}

		pub(crate) fn utilize(
			mut region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
		) -> Result<Option<(RegionId, RegionRecordOf<T>)>, Error<T>> {
			let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

			if let Some(check_owner) = maybe_check_owner {
				ensure!(check_owner == region.owner, Error::<T>::NotOwner);
			}

			let next_timeslice = Self::next_timeslice();
			if region_id.begin > next_timeslice {
				region_id.begin = next_timeslice;
			}
			Regions::<T>::remove(&region_id);

			if region_id.begin < region.end {
				Ok(Some((region_id, region)))
			} else {
				Self::deposit_event(Event::Dropped { region_id });
				Ok(None)
			}
		}

		pub(crate) fn do_assign(
			region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
			target: ParaId,
		) -> Result<(), Error<T>> {
			if let Some((region_id, region)) = Self::utilize(region_id, maybe_check_owner)? {
				let workplan_key = (region_id.begin, region_id.core);
				let mut workplan = Workplan::<T>::get(&workplan_key)
					.unwrap_or_default();
				if workplan.try_push(ScheduleItem {
					part: region_id.part,
					task: CoreTask::Assigned(target),
				}).is_ok() {
					Workplan::<T>::insert(&workplan_key, &workplan);
				}
				Self::deposit_event(Event::Assigned { region_id, task: target });
			}
			Ok(())
		}

		pub(crate) fn do_pool(
			region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
			payee: T::AccountId,
		) -> Result<(), Error<T>> {
			if let Some((region_id, region)) = Self::utilize(region_id, maybe_check_owner)? {
				let workplan_key = (region_id.begin, region_id.core);
				let mut workplan = Workplan::<T>::get(&workplan_key)
					.unwrap_or_default();
				if workplan.try_push(ScheduleItem {
					part: region_id.part,
					task: CoreTask::InstaPool,
				}).is_ok() {
					Workplan::<T>::insert(&workplan_key, &workplan);
					InstaPoolIo::<T>::mutate(region_id.begin, |a| *a += region_id.part.count_ones() as i32);
					InstaPoolIo::<T>::mutate(region.end, |a| *a -= region_id.part.count_ones() as i32);
					let contrib = ContributionRecord {
						begin: region_id.begin,
						end: region.end,
						core: region_id.core,
						part: region_id.part,
						payee: Contributor::Private(payee),
					};
					InstaPoolContribution::<T>::insert(&contrib, ());
				}
				Self::deposit_event(Event::Pooled { region_id });
			}
			Ok(())
		}

		pub(crate) fn issue(
			core: CoreIndex,
			begin: Timeslice,
			length: Timeslice,
			owner: T::AccountId,
		) -> Result<(), Error<T>> {
			let id = RegionId { begin, core, part: CorePart::complete() };
			let record = RegionRecord { end: begin + length, owner };
			Regions::<T>::insert(id, record);
			Ok(())
		}
	}
}
