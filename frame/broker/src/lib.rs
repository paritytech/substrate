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

mod adapt_price;
mod benchmarking;
mod core_mask;
mod coretime_interface;
mod dispatchable_impls;
#[cfg(test)]
mod mock;
mod nonfungible_impl;
#[cfg(test)]
mod test_fungibles;
#[cfg(test)]
mod tests;
mod tick_impls;
mod types;
mod utility_impls;

pub mod weights;
pub use weights::WeightInfo;

pub use adapt_price::*;
pub use core_mask::*;
pub use coretime_interface::*;
pub use nonfungible_impl::*;
pub use types::*;
pub use utility_impls::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		pallet_prelude::{DispatchResult, DispatchResultWithPostInfo, *},
		traits::{
			fungible::{Balanced, Credit, Mutate},
			EnsureOrigin, OnUnbalanced,
		},
		PalletId,
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::{Convert, ConvertBack};
	use sp_std::vec::Vec;

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
		type ConvertBalance: Convert<BalanceOf<Self>, RelayBalanceOf<Self>>
			+ ConvertBack<BalanceOf<Self>, RelayBalanceOf<Self>>;

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
	pub type AllowedRenewals<T> =
		StorageMap<_, Twox64Concat, AllowedRenewalId, AllowedRenewalRecordOf<T>, OptionQuery>;

	/// The current (unassigned) Regions.
	#[pallet::storage]
	pub type Regions<T> = StorageMap<_, Blake2_128Concat, RegionId, RegionRecordOf<T>, OptionQuery>;

	/// The work we plan on having each core do at a particular time in the future.
	#[pallet::storage]
	pub type Workplan<T> =
		StorageMap<_, Twox64Concat, (Timeslice, CoreIndex), Schedule, OptionQuery>;

	/// The current workload of each core. This gets updated with workplan as timeslices pass.
	#[pallet::storage]
	pub type Workload<T> = StorageMap<_, Twox64Concat, CoreIndex, Schedule, ValueQuery>;

	/// Record of a single contribution to the Instantaneous Coretime Pool.
	#[pallet::storage]
	pub type InstaPoolContribution<T> =
		StorageMap<_, Blake2_128Concat, RegionId, ContributionRecordOf<T>, OptionQuery>;

	/// Record of Coretime entering or leaving the Instantaneous Coretime Pool.
	#[pallet::storage]
	pub type InstaPoolIo<T> = StorageMap<_, Blake2_128Concat, Timeslice, PoolIoRecord, ValueQuery>;

	/// Total InstaPool rewards for each Timeslice and the number of core parts which contributed.
	#[pallet::storage]
	pub type InstaPoolHistory<T> =
		StorageMap<_, Blake2_128Concat, Timeslice, InstaPoolHistoryRecordOf<T>>;

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
		/// A new number of cores has been requested.
		CoreCountRequested {
			/// The number of cores requested.
			core_count: CoreIndex,
		},
		/// The number of cores available for scheduling has changed.
		CoreCountChanged {
			/// The new number of cores available for scheduling.
			core_count: CoreIndex,
		},
		/// There is a new reservation for a workload.
		ReservationMade {
			/// The index of the reservation.
			index: u32,
			/// The workload of the reservation.
			workload: Schedule,
		},
		/// A reservation for a workload has been cancelled.
		ReservationCancelled {
			/// The index of the reservation which was cancelled.
			index: u32,
			/// The workload of the now cancelled reservation.
			workload: Schedule,
		},
		/// A new sale has been initialized.
		SaleInitialized {
			/// The local block number at which the sale will/did start.
			sale_start: BlockNumberFor<T>,
			/// The length in blocks of the Leadin Period (where the price is decreasing).
			leadin_length: BlockNumberFor<T>,
			/// The price of Bulk Coretime at the beginning of the Leadin Period.
			start_price: BalanceOf<T>,
			/// The price of Bulk Coretime after the Leadin Period.
			regular_price: BalanceOf<T>,
			/// The first timeslice of the Regions which are being sold in this sale.
			region_begin: Timeslice,
			/// The timeslice on which the Regions which are being sold in the sale terminate.
			/// (i.e. One after the last timeslice which the Regions control.)
			region_end: Timeslice,
			/// The number of cores we want to sell, ideally. Selling this amount would result in
			/// no change to the price for the next sale.
			ideal_cores_sold: CoreIndex,
			/// Number of cores which are/have been offered for sale.
			cores_offered: CoreIndex,
		},
		/// A new lease has been created.
		Leased {
			/// The task to which a core will be assigned.
			task: TaskId,
			/// The timeslice contained in the sale period after which this lease will
			/// self-terminate (and therefore the earliest timeslice at which the lease may no
			/// longer apply).
			until: Timeslice,
		},
		/// A lease is about to end.
		LeaseEnding {
			/// The task to which a core was assigned.
			task: TaskId,
			/// The timeslice at which the task will no longer be scheduled.
			when: Timeslice,
		},
		/// The sale rotation has been started and a new sale is imminent.
		SalesStarted {
			/// The nominal price of an Region of Bulk Coretime.
			price: BalanceOf<T>,
			/// The maximum number of cores which this pallet will attempt to assign.
			core_count: CoreIndex,
		},
		/// The act of claiming revenue has begun.
		RevenueClaimBegun {
			/// The region to be claimed for.
			region: RegionId,
			/// The maximum number of timeslices which should be searched for claimed.
			max_timeslices: Timeslice,
		},
		/// A particular timeslice has a non-zero claim.
		RevenueClaimItem {
			/// The timeslice whose claim is being processed.
			when: Timeslice,
			/// The amount which was claimed at this timeslice.
			amount: BalanceOf<T>,
		},
		/// A revenue claim has (possibly only in part) been paid.
		RevenueClaimPaid {
			/// The account to whom revenue has been paid.
			who: T::AccountId,
			/// The total amount of revenue claimed and paid.
			amount: BalanceOf<T>,
			/// The next region which should be claimed for the continuation of this contribution.
			next: Option<RegionId>,
		},
		/// Some Instantaneous Coretime Pool credit has been purchased.
		CreditPurchased {
			/// The account which purchased the credit.
			who: T::AccountId,
			/// The Relay-chain account to which the credit will be made.
			beneficiary: RelayAccountIdOf<T>,
			/// The amount of credit purchased.
			amount: BalanceOf<T>,
		},
		/// A Region has been dropped due to being out of date.
		RegionDropped {
			/// The Region which no longer exists.
			region_id: RegionId,
			/// The duration of the Region.
			duration: Timeslice,
		},
		/// Some historical Instantaneous Core Pool contribution record has been dropped.
		ContributionDropped {
			/// The Region whose contribution is no longer exists.
			region_id: RegionId,
		},
		/// Some historical Instantaneous Core Pool payment record has been initialized.
		HistoryInitialized {
			/// The timeslice whose history has been initialized.
			when: Timeslice,
			/// The amount of privately contributed Coretime to the Instantaneous Coretime Pool.
			private_pool_size: CoreMaskBitCount,
			/// The amount of Coretime contributed to the Instantaneous Coretime Pool by the
			/// Polkadot System.
			system_pool_size: CoreMaskBitCount,
		},
		/// Some historical Instantaneous Core Pool payment record has been dropped.
		HistoryDropped {
			/// The timeslice whose history is no longer available.
			when: Timeslice,
			/// The amount of revenue the system has taken.
			revenue: BalanceOf<T>,
		},
		/// Some historical Instantaneous Core Pool payment record has been ignored because the
		/// timeslice was already known. Governance may need to intervene.
		HistoryIgnored {
			/// The timeslice whose history is was ignored.
			when: Timeslice,
			/// The amount of revenue which was ignored.
			revenue: BalanceOf<T>,
		},
		/// Some historical Instantaneous Core Pool Revenue is ready for payout claims.
		ClaimsReady {
			/// The timeslice whose history is available.
			when: Timeslice,
			/// The amount of revenue the Polkadot System has already taken.
			system_payout: BalanceOf<T>,
			/// The total amount of revenue remaining to be claimed.
			private_payout: BalanceOf<T>,
		},
		/// A Core has been assigned to one or more tasks and/or the Pool on the Relay-chain.
		CoreAssigned {
			/// The index of the Core which has been assigned.
			core: CoreIndex,
			/// The Relay-chain block at which this assignment should take effect.
			when: RelayBlockNumberOf<T>,
			/// The workload to be done on the Core.
			assignment: Vec<(CoreAssignment, PartsOf57600)>,
		},
		/// Some historical Instantaneous Core Pool payment record has been dropped.
		AllowedRenewalDropped {
			/// The timeslice whose renewal is no longer available.
			when: Timeslice,
			/// The core whose workload is no longer available to be renewed for `when`.
			core: CoreIndex,
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
		/// The pivot point of the partition at the beginning of the region.
		PivotTooEarly,
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
		/// The revenue for the Instantaneous Core Sales of this period is not (yet) known and thus
		/// this operation cannot proceed.
		UnknownRevenue,
		/// The identified contribution to the Instantaneous Core Pool is unknown.
		UnknownContribution,
		/// The workload assigned for renewal is incomplete. This is unexpected and indicates a
		/// logic error.
		IncompleteAssignment,
		/// An item cannot be dropped because it is still valid.
		StillValid,
		/// The history item does not exist.
		NoHistory,
		/// No reservation of the given index exists.
		UnknownReservation,
		/// The renewal record cannot be found.
		UnknownRenewal,
		/// The lease expiry time has already passed.
		AlreadyExpired,
		/// The configuration could not be applied because it is invalid.
		InvalidConfig,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_now: BlockNumberFor<T>) -> Weight {
			Self::do_tick()
		}
	}

	#[pallet::call(weight(<T as Config>::WeightInfo))]
	impl<T: Config> Pallet<T> {
		/// Configure the pallet.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `config`: The configuration for this pallet.
		#[pallet::call_index(0)]
		pub fn configure(
			origin: OriginFor<T>,
			config: ConfigRecordOf<T>,
		) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_configure(config)?;
			Ok(Pays::No.into())
		}

		/// Reserve a core for a workload.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `workload`: The workload which should be permanently placed on a core.
		#[pallet::call_index(1)]
		pub fn reserve(origin: OriginFor<T>, workload: Schedule) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_reserve(workload)?;
			Ok(Pays::No.into())
		}

		/// Cancel a reservation for a workload.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `item_index`: The index of the reservation. Usually this will also be the index of the
		///   core on which the reservation has been scheduled. However, it is possible that if
		///   other cores are reserved or unreserved in the same sale rotation that they won't
		///   correspond, so it's better to look up the core properly in the `Reservations` storage.
		#[pallet::call_index(2)]
		pub fn unreserve(origin: OriginFor<T>, item_index: u32) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_unreserve(item_index)?;
			Ok(Pays::No.into())
		}

		/// Reserve a core for a single task workload for a limited period.
		///
		/// In the interlude and sale period where Bulk Coretime is sold for the period immediately
		/// after `until`, then the same workload may be renewed.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `task`: The workload which should be placed on a core.
		/// - `until`: The timeslice now earlier than which `task` should be placed as a workload on
		///   a core.
		#[pallet::call_index(3)]
		pub fn set_lease(
			origin: OriginFor<T>,
			task: TaskId,
			until: Timeslice,
		) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_set_lease(task, until)?;
			Ok(Pays::No.into())
		}

		/// Begin the Bulk Coretime sales rotation.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `initial_price`: The price of Bulk Coretime in the first sale.
		/// - `core_count`: The number of cores which can be allocated.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::start_sales((*core_count).into()))]
		pub fn start_sales(
			origin: OriginFor<T>,
			initial_price: BalanceOf<T>,
			core_count: CoreIndex,
		) -> DispatchResultWithPostInfo {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_start_sales(initial_price, core_count)?;
			Ok(Pays::No.into())
		}

		/// Purchase Bulk Coretime in the ongoing Sale.
		///
		/// - `origin`: Must be a Signed origin with at least enough funds to pay the current price
		///   of Bulk Coretime.
		/// - `price_limit`: An amount no more than which should be paid.
		#[pallet::call_index(5)]
		pub fn purchase(
			origin: OriginFor<T>,
			price_limit: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_purchase(who, price_limit)?;
			Ok(Pays::No.into())
		}

		/// Renew Bulk Coretime in the ongoing Sale or its prior Interlude Period.
		///
		/// - `origin`: Must be a Signed origin with at least enough funds to pay the renewal price
		///   of the core.
		/// - `core`: The core which should be renewed.
		#[pallet::call_index(6)]
		pub fn renew(origin: OriginFor<T>, core: CoreIndex) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_renew(who, core)?;
			Ok(Pays::No.into())
		}

		/// Transfer a Bulk Coretime Region to a new owner.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region whose ownership should change.
		/// - `new_owner`: The new owner for the Region.
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

		/// Split a Bulk Coretime Region into two non-overlapping Regions at a particular time into
		/// the region.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region which should be partitioned into two non-overlapping Regions.
		/// - `pivot`: The offset in time into the Region at which to make the split.
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

		/// Split a Bulk Coretime Region into two wholly-overlapping Regions with complementary
		/// interlace masks which together make up the original Region's interlace mask.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region which should become two interlaced Regions of incomplete
		///   regularity.
		/// - `pivot`: The interlace mask of on of the two new regions (the other it its partial
		///   complement).
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

		/// Assign a Bulk Coretime Region to a task.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region which should be assigned to the task.
		/// - `task`: The task to assign.
		/// - `finality`: Indication of whether this assignment is final (in which case it may be
		///   eligible for renewal) or provisional (in which case it may be manipulated and/or
		/// reassigned at a later stage).
		#[pallet::call_index(10)]
		pub fn assign(
			origin: OriginFor<T>,
			region_id: RegionId,
			task: TaskId,
			finality: Finality,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_assign(region_id, Some(who), task, finality)?;
			Ok(if finality == Finality::Final { Pays::No } else { Pays::Yes }.into())
		}

		/// Place a Bulk Coretime Region into the Instantaneous Coretime Pool.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region which should be assigned to the Pool.
		/// - `payee`: The account which is able to collect any revenue due for the usage of this
		///   Coretime.
		#[pallet::call_index(11)]
		pub fn pool(
			origin: OriginFor<T>,
			region_id: RegionId,
			payee: T::AccountId,
			finality: Finality,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			Self::do_pool(region_id, Some(who), payee, finality)?;
			Ok(if finality == Finality::Final { Pays::No } else { Pays::Yes }.into())
		}

		/// Claim the revenue owed from inclusion in the Instantaneous Coretime Pool.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `region_id`: The Region which was assigned to the Pool.
		/// - `max_timeslices`: The maximum number of timeslices which should be processed. This may
		///   effect the weight of the call but should be ideally made equivalant to the length of
		///   the Region `region_id`. If it is less than this, then further dispatches will be
		///   required with the `region_id` which makes up any remainders of the region to be
		///   collected.
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::claim_revenue(*max_timeslices))]
		pub fn claim_revenue(
			origin: OriginFor<T>,
			region_id: RegionId,
			max_timeslices: Timeslice,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_claim_revenue(region_id, max_timeslices)?;
			Ok(Pays::No.into())
		}

		/// Purchase credit for use in the Instantaneous Coretime Pool.
		///
		/// - `origin`: Must be a Signed origin able to pay at least `amount`.
		/// - `amount`: The amount of credit to purchase.
		/// - `beneficiary`: The account on the Relay-chain which controls the credit (generally
		///   this will be the collator's hot wallet).
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

		/// Drop an expired Region from the chain.
		///
		/// - `origin`: Must be a Signed origin.
		/// - `region_id`: The Region which has expired.
		#[pallet::call_index(14)]
		pub fn drop_region(
			origin: OriginFor<T>,
			region_id: RegionId,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_region(region_id)?;
			Ok(Pays::No.into())
		}

		/// Drop an expired Instantaneous Pool Contribution record from the chain.
		///
		/// - `origin`: Must be a Signed origin.
		/// - `region_id`: The Region identifying the Pool Contribution which has expired.
		#[pallet::call_index(15)]
		pub fn drop_contribution(
			origin: OriginFor<T>,
			region_id: RegionId,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_contribution(region_id)?;
			Ok(Pays::No.into())
		}

		/// Drop an expired Instantaneous Pool History record from the chain.
		///
		/// - `origin`: Must be a Signed origin.
		/// - `region_id`: The time of the Pool History record which has expired.
		#[pallet::call_index(16)]
		pub fn drop_history(origin: OriginFor<T>, when: Timeslice) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_history(when)?;
			Ok(Pays::No.into())
		}

		/// Drop an expired Allowed Renewal record from the chain.
		///
		/// - `origin`: Must be a Signed origin of the account which owns the Region `region_id`.
		/// - `core`: The core to which the expired renewal refers.
		/// - `when`: The timeslice to which the expired renewal refers. This must have passed.
		#[pallet::call_index(17)]
		pub fn drop_renewal(
			origin: OriginFor<T>,
			core: CoreIndex,
			when: Timeslice,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;
			Self::do_drop_renewal(core, when)?;
			Ok(Pays::No.into())
		}

		/// Request a change to the number of cores available for scheduling work.
		///
		/// - `origin`: Must be Root or pass `AdminOrigin`.
		/// - `core_count`: The desired number of cores to be made available.
		#[pallet::call_index(18)]
		#[pallet::weight(T::WeightInfo::request_core_count((*core_count).into()))]
		pub fn request_core_count(origin: OriginFor<T>, core_count: CoreIndex) -> DispatchResult {
			T::AdminOrigin::ensure_origin_or_root(origin)?;
			Self::do_request_core_count(core_count)?;
			Ok(())
		}
	}
}
