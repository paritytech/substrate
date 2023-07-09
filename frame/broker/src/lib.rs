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

/* TODO:
- Purchase and renewal
- Advance notice & on_initialize
- Initialization
- Pool rewards
*/

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
	use sp_arithmetic::{traits::{Bounded, AtLeast32BitUnsigned, SaturatedConversion, Saturating, BaseArithmetic}, Perbill};
	use types::CorePart;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	pub type PartsOf57600 = u16;

	#[derive(Encode, Decode, Clone, Eq, PartialEq, Ord, PartialOrd, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub enum CoreAssignment {
		Idle,
		Pool,
		Task(ParaId),
	}
	pub type WholeCoreAssignment = BoundedVec<(CoreAssignment, PartsOf57600), ConstU32<80>>;

	pub trait CoretimeInterface {
		type AccountId: Parameter;
		type Balance;
		type BlockNumber: AtLeast32BitUnsigned + Copy + TypeInfo + Encode;
		fn latest() -> Self::BlockNumber;
		fn request_core_count(count: CoreIndex);
		fn request_revenue_info_at(when: Self::BlockNumber);
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
		fn request_revenue_info_at(_when: Self::BlockNumber) {}
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

		type Currency: Balanced<Self::AccountId>;

		type OnRevenue: OnUnbalanced<Credit<Self::AccountId, Self::Currency>>;

		/// Number of Relay-chain blocks ahead of time which we fix and notify of core assignments.
		#[pallet::constant]
		type AdvanceNotice: Get<RelayBlockNumberOf<Self>>;

		/// Number of Relay-chain blocks per timeslice.
		#[pallet::constant]
		type TimeslicePeriod: Get<RelayBlockNumberOf<Self>>;

		/// Period, in timeslices, of the Bulk Coretime placed for sale.
		#[pallet::constant]
		type BulkPeriod: Get<Timeslice>;

		/// Maximum number of legacy leases.
		#[pallet::constant]
		type MaxLeasedCores: Get<u32>;

		/// Maximum number of system cores.
		#[pallet::constant]
		type MaxReservedCores: Get<u32>;

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
	pub struct RegionRecord<AccountId, Balance> {
		end: Timeslice,
		owner: AccountId,
		paid: Option<Balance>,
	}
	pub type RegionRecordOf<T> = RegionRecord<<T as frame_system::Config>::AccountId, BalanceOf<T>>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct ScheduleItem {
		part: CorePart,
		assignment: CoreAssignment,
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

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct AllowedRenewalRecord<Balance> {
		begin: Timeslice,
		price: Balance,
		workload: Schedule,
	}
	pub type AllowedRenewalRecordOf<T> = AllowedRenewalRecord<BalanceOf<T>>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct StatusRecord {
		core_count: CoreIndex,
		pool_size: PartCount,
		last_timeslice: Timeslice,
	}

	/*
	SALE:
	                    1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2
	0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7
	--------------------------------------------------------
	<  renewals  >
	              <                   sale                 >
	                            ... of which ...           >
	              <       auction       ><   fixed-price   >
	                                                        | <-------\
    price fixed, unsold assigned to instapool, system cores reserved -/
	*/

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct SaleStatusRecord<Balance, BlockNumber> {
		sale_start: BlockNumber,
		auction_length: BlockNumber,
		start_price: Balance,
		reserve_price: Balance,
		region_begin: Timeslice,
		region_length: Timeslice,
		first_core: CoreIndex,
		/// The number of cores we want to sell, ideally. Selling this amount would result in no
		/// change to the reserve_price for the next sale.
		ideal_cores_sold: CoreIndex,
		/// Number of cores which are/have been offered for sale.
		cores_offered: CoreIndex,
		/// Number of cores which have been sold; never more than cores_offered.
		cores_sold: CoreIndex,
	}
	pub type SaleStatusRecordOf<T> = SaleStatusRecord<
		BalanceOf<T>,
		<T as frame_system::Config>::BlockNumber,
	>;

	pub type ReservationsRecord<Max> = BoundedVec<Schedule, Max>;
	pub type ReservationsRecordOf<T> = ReservationsRecord<<T as Config>::MaxReservedCores>;
	pub type LeasesRecord<Max> = BoundedVec<(Timeslice, ParaId), Max>;
	pub type LeasesRecordOf<T> = LeasesRecord<<T as Config>::MaxLeasedCores>;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	pub struct SaleConfigRecord<BlockNumber> {
		presale_length: BlockNumber,
		auction_length: BlockNumber,
		ideal_cores_sold: CoreIndex,
		cores_offered: CoreIndex,
	}
	pub type SaleConfigRecordOf<T> = SaleConfigRecord<
		<T as frame_system::Config>::BlockNumber,
	>;

	#[pallet::storage]
	pub type Reservations<T> = StorageValue<_, ReservationsRecordOf<T>, ValueQuery>;

	#[pallet::storage]
	pub type Leases<T> = StorageValue<_, LeasesRecordOf<T>, ValueQuery>;

	#[pallet::storage]
	pub type AllowedRenewals<T> = StorageMap<_, Twox64Concat, CoreIndex, AllowedRenewalRecordOf<T>, OptionQuery>;

	#[pallet::storage]
	pub type SaleConfig<T> = StorageValue<_, SaleConfigRecordOf<T>, OptionQuery>;

	#[pallet::storage]
	pub type SaleStatus<T> = StorageValue<_, SaleStatusRecordOf<T>, OptionQuery>;

	#[pallet::storage]
	pub type Regions<T> = StorageMap<_, Blake2_128Concat, RegionId, RegionRecordOf<T>, OptionQuery>;

	/// The work we plan on having each core do at a particular time in the future.
	#[pallet::storage]
	pub type Workplan<T> = StorageMap<_, Twox64Concat, (Timeslice, CoreIndex), Schedule, OptionQuery>;

	/// The current workload of each core. This gets updated with workplan as timeslices pass.
	#[pallet::storage]
	pub type Workload<T> = StorageMap<_, Twox64Concat, CoreIndex, Schedule, ValueQuery>;

	#[pallet::storage]
	pub type Status<T> = StorageValue<_, StatusRecord, OptionQuery>;

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
		NoSales,
		IndeterminablePrice,
		Overpriced,
		Unavailable,
		SoldOut,
		WrongTime,
		NotAllowed,
		Uninitialized,
		TooEarly,
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
		/// Begin selling for the next sale period.
		///
		/// Triggered by Relay-chain block number/timeslice.
		pub(crate) fn rotate_sale(reserve_price: BalanceOf<T>) -> Option<()> {
			let config = SaleConfig::<T>::get()?;
			let old_sale = SaleStatus::<T>::get()?;

			let now = frame_system::Pallet::<T>::block_number();

			// Calculate the start price for the sale after.
			let start_price = old_sale.start_price;
			let reserve_price = old_sale.reserve_price;

			// Set workload for the reserved (system, probably) workloads.
			let region_begin = old_sale.region_begin + old_sale.region_length;
			let region_length = old_sale.region_length;

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
						begin: region_begin + region_length,
						price: reserve_price,
						workload: schedule,
					};
					AllowedRenewals::<T>::insert(first_core, record);
				}
				first_core.saturating_inc();
				!expiring
			});
			Leases::<T>::put(&leases);

			// Update SaleStatus
			let new_sale = SaleStatusRecord {
				sale_start: now.saturating_add(config.presale_length),
				auction_length: config.auction_length,
				start_price,
				reserve_price,
				region_begin,
				region_length,
				first_core,
				ideal_cores_sold: config.ideal_cores_sold,
				cores_offered: config.cores_offered,
				cores_sold: 0,
			};
			SaleStatus::<T>::put(&new_sale);

			Some(())
		}

		pub(crate) fn next_timeslice() -> Timeslice {
			let latest = T::Coretime::latest();
			let advance = T::AdvanceNotice::get();
			let timeslice_period = T::TimeslicePeriod::get();
			let last_scheduled = (latest + advance) / timeslice_period;
			let mut next_scheduled: Timeslice = last_scheduled.saturated_into();
			next_scheduled.saturating_add(1)
		}

		pub(crate) fn process_timeslice(timeslice: Timeslice) {
			let mut status = match Status::<T>::get() {
				Some(s) => s,
				None => return,
			};
			Self::process_pool(timeslice, &mut status);
			let rc_begin = RelayBlockNumberOf::<T>::from(timeslice) * T::TimeslicePeriod::get();
			for core in 0..status.core_count {
				Self::process_core_schedule(timeslice, rc_begin, core, &mut status);
			}
			Status::<T>::put(status);
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
			let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let record = AllowedRenewals::<T>::get(core).ok_or(Error::<T>::NotAllowed)?;
			let mut sale = SaleStatus::<T>::get().ok_or(Error::<T>::NoSales)?;

			ensure!(record.begin == sale.region_begin, Error::<T>::WrongTime);
			ensure!(sale.first_core < status.core_count, Error::<T>::Unavailable);
			ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);

			Self::charge(who, record.price)?;

			let core = sale.first_core + sale.cores_sold;
			sale.cores_sold.saturating_inc();

			Workplan::<T>::insert((record.begin, core), &record.workload);

			let begin = sale.region_begin + sale.region_length;
			let price = record.price + record.price / 100u32.into() * 2u32.into();
			let new_record = AllowedRenewalRecord { begin, price, .. record };
			AllowedRenewals::<T>::insert(core, new_record);
			SaleStatus::<T>::put(&sale);
			Ok(())
		}

		pub(crate) fn do_purchase(who: T::AccountId, price_limit: BalanceOf<T>) -> DispatchResult {
			let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
			let mut sale = SaleStatus::<T>::get().ok_or(Error::<T>::NoSales)?;
			ensure!(sale.first_core < status.core_count, Error::<T>::Unavailable);
			ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);
			let now = frame_system::Pallet::<T>::block_number();
			ensure!(now > sale.sale_start, Error::<T>::TooEarly);
			let current_price = lerp(
				now,
				sale.sale_start,
				sale.auction_length,
				sale.start_price,
				sale.reserve_price,
			).ok_or(Error::<T>::IndeterminablePrice)?;
			ensure!(price_limit >= current_price, Error::<T>::Overpriced);

			Self::charge(&who, current_price)?;
			let core = sale.first_core + sale.cores_sold;
			sale.cores_sold.saturating_inc();
			SaleStatus::<T>::put(&sale);
			Self::issue(core, sale.region_begin, sale.region_length, who, Some(current_price));
			Ok(())
		}

		pub(crate) fn issue(
			core: CoreIndex,
			begin: Timeslice,
			length: Timeslice,
			owner: T::AccountId,
			paid: Option<BalanceOf<T>>,
		) {
			let id = RegionId { begin, core, part: CorePart::complete() };
			let record = RegionRecord { end: begin + length, owner, paid };
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
					assignment: CoreAssignment::Task(target),
				}).is_ok() {
					Workplan::<T>::insert(&workplan_key, &workplan);
				}
				if region.end.saturating_sub(region_id.begin) == T::BulkPeriod::get() {
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
