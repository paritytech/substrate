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
	use frame_support::{
		pallet_prelude::{*, DispatchResult},
		traits::{
			tokens::{Precision::Exact, Preservation::Expendable, Fortitude::Polite},
			fungible::{self, Credit, Inspect, Balanced, HandleImbalanceDrop}, OnUnbalanced
		}
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::{AccountId32, traits::{ConvertBack, Convert}, DispatchError};
	use sp_arithmetic::{traits::{Zero, Bounded, AtLeast32BitUnsigned, SaturatedConversion, Saturating, BaseArithmetic}, Perbill, PerThing};
	use types::CorePart;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	pub type PartsOf57600 = u16;

	#[derive(Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum CoreAssignment {
		Idle,
		Pool,
		Task(TaskId),
	}
	pub type WholeCoreAssignment = BoundedVec<(CoreAssignment, PartsOf57600), ConstU32<80>>;

	pub trait CoretimeInterface {
		type AccountId: Parameter;
		type Balance;
		type BlockNumber: AtLeast32BitUnsigned + Copy + TypeInfo + Encode;
		fn latest() -> Self::BlockNumber;
		fn request_core_count(count: CoreIndex);
		fn request_revenue_info_at(when: Self::BlockNumber);
		fn credit_account(who: Self::AccountId, amount: Self::Balance);
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
		fn request_revenue_info_at(_when: Self::BlockNumber) {}
		fn credit_account(_who: Self::AccountId, _amount: Self::Balance) {}
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

		/// Weight information for all calls of this pallet.
		type WeightInfo: WeightInfo;

		/// Currency used to pay for Coretime.
		type Currency: Balanced<Self::AccountId>;

		/// What to do with any revenues collected from the sale of Coretime.
		type OnRevenue: OnUnbalanced<Credit<Self::AccountId, Self::Currency>>;

		/// Relay chain's Coretime API used to interact with and instruct the low-level scheduling
		/// system.
		type Coretime: CoretimeInterface;

		/// Reversible conversion from local balance to Relay-chain balance. This will typically be
		/// the `Identity`, but provided just in case the chains use different representations.
		type ConvertBalance: Convert<BalanceOf<Self>, RelayBalanceOf<Self>> + ConvertBack<BalanceOf<Self>, RelayBalanceOf<Self>>;

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

	pub type BalanceOf<T> = <<T as Config>::Currency as Inspect<<T as frame_system::Config>::AccountId>>::Balance;
	pub type RelayBalanceOf<T> = <<T as Config>::Coretime as CoretimeInterface>::Balance;
	pub type RelayBlockNumberOf<T> = <<T as Config>::Coretime as CoretimeInterface>::BlockNumber;

	/// Relay-chain block number with a fixed divisor of Config::TimeslicePeriod.
	pub type Timeslice = u32;
	/// Index of a Polkadot Core.
	pub type CoreIndex = u16;
	/// A Task Id. In general this is called a ParachainId.
	pub type TaskId = u32;
	/// Counter for the total number of set bits over every core's `CorePart`. `u32` so we don't
	/// ever get an overflow.
	pub type PartCount = u32;
	/// The same as `PartCount` but signed.
	pub type SignedPartCount = i32;

	/// Self-describing identity for a Region of Bulk Coretime.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionId {
		/// The timeslice at which this Region begins.
		pub begin: Timeslice,
		/// The index of the Polakdot Core on which this Region will be scheduled.
		pub core: CoreIndex,
		/// The regularity parts in which this Region will be scheduled.
		pub part: CorePart,
	}

	/// The rest of the information describing a Region.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct RegionRecord<AccountId, Balance> {
		/// The end of the Region.
		end: Timeslice,
		/// The owner of the Region.
		owner: AccountId,
		/// The amount paid to Polkadot for this Region.
		paid: Option<Balance>,
	}
	pub type RegionRecordOf<T> = RegionRecord<<T as frame_system::Config>::AccountId, BalanceOf<T>>;

	/// An distinct item which can be scheduled on a Polkadot Core.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ScheduleItem {
		/// The regularity parts in which this Item will be scheduled on the Core.
		pub part: CorePart,
		/// The job that the Core should be doing.
		pub assignment: CoreAssignment,
	}
	pub type Schedule = BoundedVec<ScheduleItem, ConstU32<80>>;

	/// Identity of a contributor to the Instantaneous Coretime Pool.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum Contributor<AccountId> {
		/// The Polkadot system; revenue collected on its behalf goes to the `Config::OnRevenue`
		/// handler.
		System,
		/// A private Bulk Coretime holder; revenue collected may be paid out to them.
		Private(AccountId),
	}
	pub type ContributorOf<T> = Contributor<<T as frame_system::Config>::AccountId>;

	/// The record of a Region which was contributed to the Instantaneous Coretime Pool. This helps
	/// with making pro rata payments to contributors.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ContributionRecord<AccountId> {
		/// The beginning of the Region contributed.
		begin: Timeslice,
		/// The end of the Region contributed.
		end: Timeslice,
		/// The index of the Polkadot Core contributed.
		core: CoreIndex,
		/// The regularity parts of the Polkadot Core contributed.
		part: CorePart,
		/// The identity of the contributor.
		payee: Contributor<AccountId>,
	}
	pub type ContributionRecordOf<T> = ContributionRecord<<T as frame_system::Config>::AccountId>;

	/// A per-timeslice bookkeeping record for tracking Instantaneous Coretime Pool activity and
	/// making proper payments to contributors.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct InstaPoolHistoryRecord<Balance> {
		/// The total amount of Coretime (measured in Regularity Parts or 1/80th of a single block
		/// of a Polkadot Core) contributed over a timeslice minus any contributions which have
		/// already been paid out.
		total_contributions: PartCount,
		/// The payout remaining for the `total_contributions`, or `None` if the revenue is not yet
		/// known.
		maybe_payout: Option<Balance>,
	}
	pub type InstaPoolHistoryRecordOf<T> = InstaPoolHistoryRecord<BalanceOf<T>>;

	/// A record of an allowed renewal.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct AllowedRenewalRecord<Balance> {
		/// The timeslice denoting the beginning of the Region for which a renewal can secure.
		begin: Timeslice,
		/// The price for which the next renewal can be made.
		price: Balance,
		/// The workload which will be scheduled on the Core in the case a renewal is made.
		workload: Schedule,
	}
	pub type AllowedRenewalRecordOf<T> = AllowedRenewalRecord<BalanceOf<T>>;

	/// General status of the system.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct StatusRecord {
		/// The current size of the Instantaneous Coretime Pool, measured in (measured in
		/// Regularity Parts or 1/80th of a single block of a Polkadot Core).
		pool_size: PartCount,
		/// The last (Relay-chain) timeslice which we processed for (this processing is generally
		/// done some number of timeslices in advance of actual Relay-chain execution to make up
		/// for latencies and any needed Relay-side preparations).
		last_timeslice: Timeslice,
	}

	/// The status of a Bulk Coretime Sale.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct SaleInfoRecord<Balance, BlockNumber> {
		/// The local block number at which the sale will/did start.
		sale_start: BlockNumber,
		/// The length in blocks of the Leadin Period (where the price is decreasing).
		leadin_length: BlockNumber,
		/// The price of Bulk Coretime at the beginning of the Leadin Period.
		start_price: Balance,
		/// The price of Bulk Coretime by the end of the Leadin Period.
		reserve_price: Balance,
		/// The first timeslice of the Regions which are being sold in this sale.
		region_begin: Timeslice,
		/// The timeslice on which the Regions which are being sold in the sale terminate. (i.e. One
		/// after the last timeslice which the Regions control.)
		region_end: Timeslice,
		/// The index of the first core which is for sale. Core of Regions which are sold have
		/// incrementing indices from this.
		first_core: CoreIndex,
		/// The number of cores we want to sell, ideally. Selling this amount would result in no
		/// change to the reserve_price for the next sale.
		ideal_cores_sold: CoreIndex,
		/// Number of cores which are/have been offered for sale.
		cores_offered: CoreIndex,
		/// Number of cores which have been sold; never more than cores_offered.
		cores_sold: CoreIndex,
	}
	pub type SaleInfoRecordOf<T> = SaleInfoRecord<
		BalanceOf<T>,
		<T as frame_system::Config>::BlockNumber,
	>;

	/// Record for Polkadot Core reservations (generally tasked with the maintenance of System
	/// Chains).
	pub type ReservationsRecord<Max> = BoundedVec<Schedule, Max>;
	pub type ReservationsRecordOf<T> = ReservationsRecord<<T as Config>::MaxReservedCores>;
	/// Record for Polkadot Core legacy leases.
	pub type LeasesRecord<Max> = BoundedVec<(Timeslice, TaskId), Max>;
	pub type LeasesRecordOf<T> = LeasesRecord<<T as Config>::MaxLeasedCores>;

	/// Configuration of this pallet.
	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ConfigRecord<BlockNumber> {
		/// The total number of cores which can be assigned (one plus the maximum index which can
		/// be used in `Coretime::assign`).
		pub core_count: CoreIndex,
		/// The number of timeslices in advance which scheduling should be fixed and the
		/// `Coretime::assign` API used to inform the Relay-chain.
		pub advance_notice: Timeslice,
		/// The length in blocks of the Interlude Period for forthcoming sales.
		pub interlude_length: BlockNumber,
		/// The length in blocks of the Leadin Period for forthcoming sales.
		pub leadin_length: BlockNumber,
		/// The length in timeslices of Regions which are up for sale in forthcoming sales.
		pub region_length: Timeslice,
		/// The proportion of cores available for sale which should be sold in order for the price
		/// to remain the same in the next sale.
		pub ideal_bulk_proportion: Perbill,
		/// An artificial limit to the number of cores which are allowed to be sold. If `Some` then
		/// no more cores will be sold than this.
		pub limit_cores_offered: Option<CoreIndex>,
	}
	pub type ConfigRecordOf<T> = ConfigRecord<
		<T as frame_system::Config>::BlockNumber,
	>;

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
	pub type InstaPoolContribution<T> = StorageMap<_, Blake2_128Concat, ContributionRecordOf<T>, (), OptionQuery>;

	/// Record of Coretime entering or leaving the Instantaneous Coretime Pool.
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
			task: TaskId,
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
		NoSales,
		IndeterminablePrice,
		Overpriced,
		Unavailable,
		SoldOut,
		WrongTime,
		NotAllowed,
		Uninitialized,
		TooEarly,
		NothingToDo,
		TooManyReservations,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(now: T::BlockNumber) -> Weight {
			Self::do_tick();
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

	fn lerp<T: TryInto<u128>, S: TryInto<u128> + TryFrom<u128> + Bounded>(v: T, a: T, d: T, x: S, y: S) -> Option<S> {
		use sp_arithmetic::{Rounding::NearestPrefUp, helpers_128bit::multiply_by_rational_with_rounding};
		let v: u128 = v.try_into().ok()?;
		let a: u128 = a.try_into().ok()?;
		let d: u128 = d.try_into().ok()?;
		let r: u128 = x.try_into().ok()?;
		let s: u128 = y.try_into().ok()?;
		let rsd = r.max(s) - r.min(s);
		let td = multiply_by_rational_with_rounding(rsd, (v.max(a) - a).min(d), d, NearestPrefUp)?;
		if r < s { r + td } else { r - td }.try_into().ok()
	}

	impl<T: Config> Pallet<T> {
		pub(crate) fn do_configure(config: ConfigRecordOf<T>) -> DispatchResult {
			Configuration::<T>::put(config);
			Ok(())
		}

		/// Attempt to tick things along. Will only do anything if the `Status.last_timeslice` is
		/// less than `Self::last_timeslice`.
		pub(crate) fn do_tick() -> DispatchResult {
			let mut status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let current_timeslice = Self::current_timeslice();
			ensure!(status.last_timeslice < current_timeslice, Error::<T>::NothingToDo);
			status.last_timeslice.saturating_inc();
			
			let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let commit_timeslice = status.last_timeslice + config.advance_notice;
			Self::process_timeslice(commit_timeslice, &mut status, &config);

			if let Some(sale) = SaleInfo::<T>::get() {
				if commit_timeslice >= sale.region_begin {
					// Sale can be rotated.
					Self::rotate_sale(commit_timeslice, sale, &status, &config);
				}
			}

			Status::<T>::put(&status);
			Ok(())
		}

		pub(crate) fn do_start_sales(
			reserve_price: BalanceOf<T>,
		) -> DispatchResult {
			let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let current_schedulable_timeslice = Self::current_schedulable_timeslice();
			let status = StatusRecord {
				pool_size: 0,
				last_timeslice: current_schedulable_timeslice,
			};
			Status::<T>::put(&status);
			let now = frame_system::Pallet::<T>::block_number();
			let dummy_sale = SaleInfoRecord {
				sale_start: now,
				leadin_length: Zero::zero(),
				start_price: Zero::zero(),
				reserve_price,
				region_begin: current_schedulable_timeslice,
				region_end: current_schedulable_timeslice + config.region_length,
				first_core: 0,
				ideal_cores_sold: 0,
				cores_offered: 0,
				cores_sold: 0,
			};
			Self::rotate_sale(current_schedulable_timeslice, dummy_sale, &status, &config);
			Ok(())
		}

		fn bump_price(
			offered: CoreIndex,
			ideal: CoreIndex,
			sold: CoreIndex,
			old: BalanceOf<T>,
		) -> BalanceOf<T> {
			if sold > ideal {
				let extra = if offered > ideal {
					Perbill::from_rational((sold - ideal) as u32, (offered - ideal) as u32)
				} else {
					Perbill::zero()
				};
				old + extra * old
			} else {
				let extra = if ideal > 0 {
					Perbill::from_rational(sold as u32, ideal as u32).left_from_one()
				} else {
					Perbill::zero()
				};
				old - extra * old
			}
		}

		/// Begin selling for the next sale period.
		///
		/// Triggered by Relay-chain block number/timeslice.
		pub(crate) fn rotate_sale(
			commit_timeslice: Timeslice,
			old_sale: SaleInfoRecordOf<T>,
			status: &StatusRecord,
			config: &ConfigRecordOf<T>,
		) -> Option<()> {
			let now = frame_system::Pallet::<T>::block_number();

			// Calculate the start price for the sale after.
			let reserve_price = {
				let core_count = config.core_count;
				let max_retail = core_count.saturating_sub(old_sale.first_core);
				let offered = old_sale.cores_offered.min(max_retail);
				let ideal = old_sale.ideal_cores_sold.min(max_retail);
				let sold = old_sale.cores_sold;
				let old_price = old_sale.reserve_price;
				if offered > 0 {
					Self::bump_price(offered, ideal, sold, old_price)
				} else {
					old_price
				}
			};
			let start_price = reserve_price * 2u32.into();

			// TODO: commission system InstaPool cores.

			// Set workload for the reserved (system, probably) workloads.
			let region_begin = old_sale.region_end;
			let region_end = region_begin + config.region_length;

			let mut first_core = 0;
			for schedule in Reservations::<T>::get().into_iter() {
				Workplan::<T>::insert((region_begin, first_core), schedule);
				first_core.saturating_inc();
			}

			let mut leases = Leases::<T>::get();
			// can morph to a renewable as long as it's > begin and < end.
			leases.retain(|&(until, para)| {
				let part = CorePart::complete();
				let assignment = CoreAssignment::Task(para);
				let schedule = BoundedVec::truncate_from(vec![ScheduleItem { part, assignment }]);
				Workplan::<T>::insert((region_begin, first_core), &schedule);
				let expiring = until >= region_begin;
				if expiring {
					// last time for this one - make it renewable.
					let record = AllowedRenewalRecord {
						begin: region_end,
						price: reserve_price,
						workload: schedule,
					};
					AllowedRenewals::<T>::insert(first_core, record);
				}
				first_core.saturating_inc();
				!expiring
			});
			Leases::<T>::put(&leases);

			let max_possible_sales = config.core_count.saturating_sub(first_core);
			let limit_cores_offered = config.limit_cores_offered.unwrap_or(CoreIndex::max_value());
			let cores_offered = limit_cores_offered.min(max_possible_sales);
			// Update SaleInfo
			let new_sale = SaleInfoRecord {
				sale_start: now.saturating_add(config.interlude_length),
				leadin_length: config.leadin_length,
				start_price,
				reserve_price,
				region_begin,
				region_end,
				first_core,
				ideal_cores_sold: (config.ideal_bulk_proportion * cores_offered as u32) as u16,
				cores_offered,
				cores_sold: 0,
			};
			SaleInfo::<T>::put(&new_sale);

			Some(())
		}

		pub(crate) fn do_reserve(schedule: Schedule) -> DispatchResult {
			let mut r = Reservations::<T>::get();
			r.try_push(schedule).map_err(|_| Error::<T>::TooManyReservations)?;
			Reservations::<T>::put(r);
			Ok(())
		}

		pub(crate) fn current_timeslice() -> Timeslice {
			let latest = T::Coretime::latest();
			let timeslice_period = T::TimeslicePeriod::get();
			(latest / timeslice_period).saturated_into()
		}

		pub(crate) fn current_schedulable_timeslice() -> Timeslice {
			Self::current_timeslice() + Configuration::<T>::get().map_or(0, |x| x.advance_notice)
		}

		pub(crate) fn next_schedulable_timeslice() -> Timeslice {
			Self::current_schedulable_timeslice().saturating_add(1)
		}

		pub(crate) fn process_timeslice(timeslice: Timeslice, status: &mut StatusRecord, config: &ConfigRecordOf<T>) {
			Self::process_pool(timeslice, status);
			let rc_begin = RelayBlockNumberOf::<T>::from(timeslice) * T::TimeslicePeriod::get();
			for core in 0..config.core_count {
				Self::process_core_schedule(timeslice, rc_begin, core, status);
			}
		}

		fn process_pool(timeslice: Timeslice, status: &mut StatusRecord) {
			let pool_io = InstaPoolIo::<T>::take(timeslice);
			status.pool_size = (status.pool_size as i32).saturating_add(pool_io) as u32;
			let record = InstaPoolHistoryRecord {
				total_contributions: status.pool_size,
				maybe_payout: None,
			};
			InstaPoolHistory::<T>::insert(timeslice, record);
		}

		/// Schedule cores for the given `timeslice`.
		fn process_core_schedule(
			timeslice: Timeslice,
			rc_begin: RelayBlockNumberOf<T>,
			core: CoreIndex,
			status: &mut StatusRecord,
		) {
			let mut workplan = match Workplan::<T>::take((timeslice, core)) {
				Some(w) => w,
				None => return,
			};
			let workload = Workload::<T>::get(core);
			let parts_used = workplan.iter().map(|i| i.part).fold(CorePart::void(), |a, i| a | i);
			let mut workplan = workplan.into_inner();
			workplan.extend(workload.into_iter().filter(|i| (i.part & parts_used).is_void()));
			let workplan = Schedule::truncate_from(workplan);
			Workload::<T>::insert(core, &workplan);

			let mut total_used = 0;
			let mut intermediate = workplan
				.into_iter()
				.map(|i| (i.assignment, i.part.count_ones() as u16 * (57_600 / 80)))
				.inspect(|i| total_used += i.1)
				.collect::<Vec<_>>();
			if total_used < 80 {
				intermediate.push((CoreAssignment::Idle, 80 - total_used));
			}
			intermediate.sort();
			let mut assignment: Vec<(CoreAssignment, PartsOf57600)> = Vec::with_capacity(intermediate.len());
			for i in intermediate.into_iter() {
				if let Some(ref mut last) = assignment.last_mut() {
					if last.0 == i.0 {
						last.1 += i.1;
						continue;
					}
				}
				assignment.push(i);
			}
			T::Coretime::assign_core(core, rc_begin, assignment, None);
		}

		fn charge(who: &T::AccountId, amount: BalanceOf<T>) -> DispatchResult {
			T::OnRevenue::on_unbalanced(T::Currency::withdraw(&who, amount, Exact, Expendable, Polite)?);
			Ok(())
		}

		/// Must be called on a core in `AllowedRenewals` whose value is a timeslice equal to the
		/// current sale status's `region_end`.
		pub(crate) fn do_renew(who: &T::AccountId, core: CoreIndex) -> DispatchResult {
			let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let record = AllowedRenewals::<T>::get(core).ok_or(Error::<T>::NotAllowed)?;
			let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;

			ensure!(record.begin == sale.region_begin, Error::<T>::WrongTime);
			ensure!(sale.first_core < config.core_count, Error::<T>::Unavailable);
			ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);

			Self::charge(who, record.price)?;

			let core = sale.first_core + sale.cores_sold;
			sale.cores_sold.saturating_inc();

			Workplan::<T>::insert((record.begin, core), &record.workload);

			let begin = sale.region_end;
			let price = record.price + record.price / 100u32.into() * 2u32.into();
			let new_record = AllowedRenewalRecord { begin, price, .. record };
			AllowedRenewals::<T>::insert(core, new_record);
			SaleInfo::<T>::put(&sale);
			Ok(())
		}

		pub(crate) fn do_purchase(who: T::AccountId, price_limit: BalanceOf<T>) -> DispatchResult {
			let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
			ensure!(sale.first_core < config.core_count, Error::<T>::Unavailable);
			ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now > sale.sale_start, Error::<T>::TooEarly);
			let current_price = lerp(
				now,
				sale.sale_start,
				sale.leadin_length,
				sale.start_price,
				sale.reserve_price,
			).ok_or(Error::<T>::IndeterminablePrice)?;
			ensure!(price_limit >= current_price, Error::<T>::Overpriced);

			Self::charge(&who, current_price)?;
			let core = sale.first_core + sale.cores_sold;
			sale.cores_sold.saturating_inc();
			SaleInfo::<T>::put(&sale);
			Self::issue(core, sale.region_begin, sale.region_end, who, Some(current_price));
			Ok(())
		}

		pub(crate) fn issue(
			core: CoreIndex,
			begin: Timeslice,
			end: Timeslice,
			owner: T::AccountId,
			paid: Option<BalanceOf<T>>,
		) {
			let id = RegionId { begin, core, part: CorePart::complete() };
			let record = RegionRecord { end, owner, paid };
			Regions::<T>::insert(id, record);
		}

		pub(crate) fn do_transfer(
			region_id: RegionId,
			maybe_check_owner: Option<T::AccountId>,
			new_owner: T::AccountId,
		) -> Result<(), Error<T>> {
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

			region.paid = None;
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

			let next_timeslice = Self::next_schedulable_timeslice();
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
			target: TaskId,
		) -> Result<(), Error<T>> {
			let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			if let Some((region_id, region)) = Self::utilize(region_id, maybe_check_owner)? {
				let workplan_key = (region_id.begin, region_id.core);
				let mut workplan = Workplan::<T>::get(&workplan_key)
					.unwrap_or_default();
				if workplan.try_push(ScheduleItem {
					part: region_id.part,
					assignment: CoreAssignment::Task(target),
				}).is_ok() {
					Workplan::<T>::insert(&workplan_key, &workplan);
				}
				if region.end.saturating_sub(region_id.begin) == config.region_length {
					if workplan.iter()
						.filter(|i| matches!(i.assignment, CoreAssignment::Task(..)))
						.fold(CorePart::void(), |a, i| a | i.part)
						.is_complete()
					{
						if let Some(price) = region.paid {
							let record = AllowedRenewalRecord {
								begin: region.end,
								price,
								workload: workplan,
							};
							AllowedRenewals::<T>::insert(region_id.core, &record);
						}
					}
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
					assignment: CoreAssignment::Pool,
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
	}
}
