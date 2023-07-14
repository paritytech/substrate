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
mod core_part;
mod types;
mod coretime_interface;
mod utils;
mod implementation;
mod dispatchable_impls;
mod nonfungible_impl;
mod adapt_price;

pub mod weights;
pub use weights::WeightInfo;

pub use adapt_price::*;
pub use core_part::*;
pub use coretime_interface::*;
pub use nonfungible_impl::*;
pub use types::*;
pub use utils::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		pallet_prelude::{*, DispatchResult, DispatchResultWithPostInfo},
		traits::{fungible::{Credit, Mutate, Balanced}, OnUnbalanced, EnsureOrigin},
		PalletId,
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::{ConvertBack, Convert};

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for all calls of this pallet.
		type WeightInfo: WeightInfo;

		/// Currency used to pay for Coretime.
		type Currency: Mutate<Self::AccountId> + Balanced<Self::AccountId>;

		/// The origin test needed for administrating this pallet.
		type AdminOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// What to do with any revenues collected from the sale of Coretime.
		type OnRevenue: OnUnbalanced<Credit<Self::AccountId, Self::Currency>>;

		/// Relay chain's Coretime API used to interact with and instruct the low-level scheduling
		/// system.
		type Coretime: CoretimeInterface;

		/// The algorithm to determine the next price on the basis of market performance.
		type PriceAdapter: AdaptPrice;

		/// Reversible conversion from local balance to Relay-chain balance. This will typically be
		/// the `Identity`, but provided just in case the chains use different representations.
		type ConvertBalance: Convert<BalanceOf<Self>, RelayBalanceOf<Self>> + ConvertBack<BalanceOf<Self>, RelayBalanceOf<Self>>;

		/// Identifier from which the internal Pot is generated.
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// Number of Relay-chain blocks per timeslice.
		#[pallet::constant]
		type TimeslicePeriod: Get<RelayBlockNumberOf<Self>>;

		/// Maximum number of legacy leases.
		#[pallet::constant]
		type MaxLeasedCores: Get<u32>;

		/// Maximum number of system cores.
		#[pallet::constant]
		type MaxReservedCores: Get<u32>;
	}

	/// The current configuration of this pallet.
	#[pallet::storage]
	pub type Configuration<T> = StorageValue<_, ConfigRecordOf<T>, OptionQuery>;

	/// The Polkadot Core reservations (generally tasked with the maintenance of System Chains).
	#[pallet::storage]
	pub type Reservations<T> = StorageValue<_, ReservationsRecordOf<T>, ValueQuery>;

	/// The Polkadot Core legacy leases.
	#[pallet::storage]
	pub type Leases<T> = StorageValue<_, LeasesRecordOf<T>, ValueQuery>;

	/// The current status of miscellaneous subsystems of this pallet.
	#[pallet::storage]
	pub type Status<T> = StorageValue<_, StatusRecord, OptionQuery>;

	/// The details of the current sale, including its properties and status.
	#[pallet::storage]
	pub type SaleInfo<T> = StorageValue<_, SaleInfoRecordOf<T>, OptionQuery>;

	/// Records of allowed renewals.
	#[pallet::storage]
	pub type AllowedRenewals<T> = StorageMap<_, Twox64Concat, CoreIndex, AllowedRenewalRecordOf<T>, OptionQuery>;

	/// The current (unassigned) Regions.
	#[pallet::storage]
	pub type Regions<T> = StorageMap<_, Blake2_128Concat, RegionId, RegionRecordOf<T>, OptionQuery>;

	/// The work we plan on having each core do at a particular time in the future.
	#[pallet::storage]
	pub type Workplan<T> = StorageMap<_, Twox64Concat, (Timeslice, CoreIndex), Schedule, OptionQuery>;

	/// The current workload of each core. This gets updated with workplan as timeslices pass.
	#[pallet::storage]
	pub type Workload<T> = StorageMap<_, Twox64Concat, CoreIndex, Schedule, ValueQuery>;

	/// Record of a single contribution to the Instantaneous Coretime Pool.
	#[pallet::storage]
	pub type InstaPoolContribution<T> = StorageMap<_, Blake2_128Concat, RegionId, ContributionRecordOf<T>, OptionQuery>;

	/// Record of Coretime entering or leaving the Instantaneous Coretime Pool.
	#[pallet::storage]
	pub type InstaPoolIo<T> = StorageMap<_, Blake2_128Concat, Timeslice, PoolIoRecord, ValueQuery>;

	/// Total InstaPool rewards for each Timeslice and the number of core parts which contributed.
	#[pallet::storage]
	pub type InstaPoolHistory<T> = StorageMap<_, Blake2_128Concat, Timeslice, InstaPoolHistoryRecordOf<T>>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A Region of Bulk Coretime has been purchased.
		Purchased {
			/// The identity of the purchaser.
			who: T::AccountId,
			/// The identity of the Region.
			region_id: RegionId,
			/// The price paid for this Region.
			price: BalanceOf<T>,
			/// The duration of the Region.
			duration: Timeslice,
		},
		/// The workload of a core has become renewable.
		Renewable {
			/// The core whose workload can be renewed.
			core: CoreIndex,
			/// The price at which the workload can be renewed.
			price: BalanceOf<T>,
			/// The time at which the workload would recommence of this renewal. The call to renew
			/// cannot happen before the beginning of the interlude prior to the sale for regions
			/// which begin at this time.
			begin: Timeslice,
			/// The actual workload which can be renewed.
			workload: Schedule,
		},
		/// A workload has been renewed.
		Renewed {
			/// The identity of the renewer.
			who: T::AccountId,
			/// The price paid for this renewal.
			price: BalanceOf<T>,
			/// The index of the core on which the `workload` was previously scheduled.
			old_core: CoreIndex,
			/// The index of the core on which the renewed `workload` has been scheduled.
			core: CoreIndex,
			/// The time at which the `workload` will begin on the `core`.
			begin: Timeslice,
			/// The number of timeslices for which this `workload` is newly scheduled.
			duration: Timeslice,
			/// The workload which was renewed.
			workload: Schedule,
		},
		/// Ownership of a Region has been transferred.
		Transferred {
			/// The Region which has been transferred.
			region_id: RegionId,
			/// The duration of the Region.
			duration: Timeslice,
			/// The old owner of the Region.
			old_owner: T::AccountId,
			/// The new owner of the Region.
			owner: T::AccountId,
		},
		/// A Region has been split into two non-overlapping Regions.
		Partitioned {
			/// The Region which was split.
			old_region_id: RegionId,
			/// The new Regions into which it became.
			new_region_ids: (RegionId, RegionId),
		},
		/// A Region has been converted into two overlapping Regions each of lesser regularity.
		Interlaced {
			/// The Region which was interlaced.
			old_region_id: RegionId,
			/// The new Regions into which it became.
			new_region_ids: (RegionId, RegionId),
		},
		/// A Region has been assigned to a particular task.
		Assigned {
			/// The Region which was assigned.
			region_id: RegionId,
			/// The duration of the assignment.
			duration: Timeslice,
			/// The task to which the Region was assigned.
			task: TaskId,
		},
		/// A Region has been added to the Instantaneous Coretime Pool.
		Pooled {
			/// The Region which was added to the Instantaneous Coretime Pool.
			region_id: RegionId,
			/// The duration of the Region.
			duration: Timeslice,
		},
		/// A Region has been dropped due to being out of date.
		Dropped {
			/// The Region which no longer exists.
			region_id: RegionId,
			/// The duration of the Region.
			duration: Timeslice,
		},
	}

	#[pallet::error]
	#[derive(PartialEq)]
	pub enum Error<T> {
		/// The given region identity is not known.
		UnknownRegion,
		/// The owner of the region is not the origin.
		NotOwner,
		/// The pivot point of the partition at or after the end of the region.
		PivotTooLate,
		/// The pivot mask for the interlacing is not contained within the region's interlace mask.
		ExteriorPivot,
		/// The pivot mask for the interlacing is void (and therefore unschedulable).
		VoidPivot,
		/// The pivot mask for the interlacing is complete (and therefore not a strict subset).
		CompletePivot,
		/// The workplan of the pallet's state is invalid. This indicates a state corruption.
		CorruptWorkplan,
		/// There is no sale happening currently.
		NoSales,
		/// The price for the sale could not be determined. This indicates a logic error.
		IndeterminablePrice,
		/// The price limit is exceeded.
		Overpriced,
		/// There are no cores available.
		Unavailable,
		/// The sale limit has been reached.
		SoldOut,
		/// The renewal operation is not valid at the current time (it may become valid in the next
		/// sale).
		WrongTime,
		/// Invalid attempt to renew.
		NotAllowed,
		/// This pallet has not yet been initialized.
		Uninitialized,
		/// The purchase cannot happen yet as the sale period is yet to begin.
		TooEarly,
		/// There is no work to be done.
		NothingToDo,
		/// The maximum amount of reservations has already been reached.
		TooManyReservations,
		/// The maximum amount of leases has already been reached.
		TooManyLeases,
		/// The revenue for the Instantaneous Core Sales of this period is already known. This
		/// is unexpected and indicates a logic error.
		RevenueAlreadyKnown,
		/// The revenue for the Instantaneous Core Sales of this period is not (yet) known and thus
		/// this operation cannot proceed.
		UnknownRevenue,
		/// The identified contribution to the Instantaneous Core Pool is unknown.
		UnknownContribution,
		/// The recorded contributions to the Instantaneous Core Pool are invalid. This is
		/// unexpected and indicates a logic error.
		InvalidContributions,
		/// The workload assigned for renewal is incomplete. This is unexpected and indicates a
		/// logic error.
		IncompleteAssignment,
		/// An item cannot be dropped because it is still valid.
		StillValid,
		/// The history item does not exist.
		NoHistory,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_now: T::BlockNumber) -> Weight {
			let _ = Self::do_tick();
			Weight::zero()
		}
	}

	#[pallet::call(weight(<T as Config>::WeightInfo))]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		pub fn configure(origin: OriginFor<T>, config: ConfigRecordOf<T>) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_configure(config)?;
			Ok(())
		}

		#[pallet::call_index(1)]
		pub fn reserve(origin: OriginFor<T>, schedule: Schedule) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_reserve(schedule)?;
			Ok(())
		}

		#[pallet::call_index(2)]
		pub fn unreserve(origin: OriginFor<T>, item_index: u32) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_unreserve(item_index)?;
			Ok(())
		}

		#[pallet::call_index(3)]
		pub fn set_lease(origin: OriginFor<T>, task: TaskId, until: Timeslice) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_set_lease(task, until)?;
			Ok(())
		}

		#[pallet::call_index(4)]
		pub fn start_sales(origin: OriginFor<T>, initial_price: BalanceOf<T>, core_count: CoreIndex) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_start_sales(initial_price, core_count)?;
			Ok(())
		}

		#[pallet::call_index(5)]
		pub fn purchase(origin: OriginFor<T>, price_limit: BalanceOf<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_purchase(who, price_limit)?;
			Ok(())
		}

		#[pallet::call_index(6)]
		pub fn renew(origin: OriginFor<T>, core: CoreIndex) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_renew(who, core)?;
			Ok(())
		}

		#[pallet::call_index(7)]
		pub fn transfer(
			origin: OriginFor<T>,
			region_id: RegionId,
			new_owner: T::AccountId,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_transfer(region_id, Some(who), new_owner)?;
			Ok(())
		}

		#[pallet::call_index(8)]
		pub fn partition(
			origin: OriginFor<T>,
			region_id: RegionId,
			pivot: Timeslice,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_partition(region_id, Some(who), pivot)?;
			Ok(())
		}

		#[pallet::call_index(9)]
		pub fn interlace(
			origin: OriginFor<T>,
			region_id: RegionId,
			pivot: CoreMask,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_interlace(region_id, Some(who), pivot)?;
			Ok(())
		}

		#[pallet::call_index(10)]
		pub fn assign(
			origin: OriginFor<T>,
			region_id: RegionId,
			target: TaskId,
			finality: Finality,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_assign(region_id, Some(who), target, finality)?;
			Ok(())
		}

		#[pallet::call_index(11)]
		pub fn pool(
			origin: OriginFor<T>,
			region_id: RegionId,
			payee: T::AccountId,
			finality: Finality,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_pool(region_id, Some(who), payee, finality)?;
			Ok(())
		}

		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::claim_revenue(*max_timeslices))]
		pub fn claim_revenue(
			origin: OriginFor<T>,
			region_id: RegionId,
			max_timeslices: Timeslice,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			Self::do_claim_revenue(region_id, max_timeslices)?;
			Ok(())
		}

		#[pallet::call_index(13)]
		pub fn purchase_credit(
			origin: OriginFor<T>,
			amount: BalanceOf<T>,
			beneficiary: RelayAccountIdOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::do_purchase_credit(who, amount, beneficiary)?;
			Ok(())
		}

		#[pallet::call_index(14)]
		pub fn drop_region(
			origin: OriginFor<T>,
			region_id: RegionId,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_region(region_id)?;
			Ok(Pays::No.into())
		}

		#[pallet::call_index(15)]
		pub fn drop_contribution(
			origin: OriginFor<T>,
			region_id: RegionId,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_contribution(region_id)?;
			Ok(Pays::No.into())
		}

		#[pallet::call_index(16)]
		pub fn drop_history(
			origin: OriginFor<T>,
			when: Timeslice,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_history(when)?;
			Ok(Pays::No.into())
		}

		#[pallet::call_index(17)]
		pub fn request_core_count(origin: OriginFor<T>, core_count: CoreIndex) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_request_core_count(core_count)?;
			Ok(())
		}
	}
}
