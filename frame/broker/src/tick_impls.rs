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

use super::*;
use frame_support::{pallet_prelude::*, weights::WeightMeter};
use sp_arithmetic::{
	traits::{One, SaturatedConversion, Saturating, Zero},
	FixedPointNumber,
};
use sp_runtime::traits::ConvertBack;
use sp_std::{vec, vec::Vec};
use CompletionStatus::Complete;

impl<T: Config> Pallet<T> {
	/// Attempt to tick things along.
	///
	/// This may do several things:
	/// - Processes notifications of the core count changing
	/// - Processes reports of Instantaneous Core Market Revenue
	/// - Commit a timeslice
	/// - Rotate the sale period
	/// - Request revenue information for a previous timeslice
	/// - Initialize an instantaneous core pool historical revenue record
	pub(crate) fn do_tick() -> Weight {
		let (mut status, config) = match (Status::<T>::get(), Configuration::<T>::get()) {
			(Some(s), Some(c)) => (s, c),
			_ => return Weight::zero(),
		};

		let mut meter = WeightMeter::max_limit();

		if Self::process_core_count(&mut status) {
			meter.consume(T::WeightInfo::process_core_count(status.core_count.into()));
		}

		if Self::process_revenue() {
			meter.consume(T::WeightInfo::process_revenue());
		}

		if let Some(commit_timeslice) = Self::next_timeslice_to_commit(&config, &status) {
			status.last_committed_timeslice = commit_timeslice;
			if let Some(sale) = SaleInfo::<T>::get() {
				if commit_timeslice >= sale.region_begin {
					// Sale can be rotated.
					Self::rotate_sale(sale, &config, &status);
					meter.consume(T::WeightInfo::rotate_sale(status.core_count.into()));
				}
			}

			Self::process_pool(commit_timeslice, &mut status);
			meter.consume(T::WeightInfo::process_pool());

			let timeslice_period = T::TimeslicePeriod::get();
			let rc_begin = RelayBlockNumberOf::<T>::from(commit_timeslice) * timeslice_period;
			for core in 0..status.core_count {
				Self::process_core_schedule(commit_timeslice, rc_begin, core);
				meter.consume(T::WeightInfo::process_core_schedule());
			}
		}

		let current_timeslice = Self::current_timeslice();
		if status.last_timeslice < current_timeslice {
			status.last_timeslice.saturating_inc();
			let rc_block = T::TimeslicePeriod::get() * status.last_timeslice.into();
			T::Coretime::request_revenue_info_at(rc_block);
			meter.consume(T::WeightInfo::request_revenue_info_at());
		}

		Status::<T>::put(&status);

		meter.consumed()
	}

	pub(crate) fn process_core_count(status: &mut StatusRecord) -> bool {
		if let Some(core_count) = T::Coretime::check_notify_core_count() {
			status.core_count = core_count;
			Self::deposit_event(Event::<T>::CoreCountChanged { core_count });
			return true
		}
		false
	}

	pub(crate) fn process_revenue() -> bool {
		let Some((until, amount)) = T::Coretime::check_notify_revenue_info() else {
			return false;
		};
		let when: Timeslice =
			(until / T::TimeslicePeriod::get()).saturating_sub(One::one()).saturated_into();
		let mut revenue = T::ConvertBalance::convert_back(amount);
		if revenue.is_zero() {
			Self::deposit_event(Event::<T>::HistoryDropped { when, revenue });
			InstaPoolHistory::<T>::remove(when);
			return true
		}
		let mut r = InstaPoolHistory::<T>::get(when).unwrap_or_default();
		if r.maybe_payout.is_some() {
			Self::deposit_event(Event::<T>::HistoryIgnored { when, revenue });
			return true
		}
		// Payout system InstaPool Cores.
		let total_contrib = r.system_contributions.saturating_add(r.private_contributions);
		let system_payout =
			revenue.saturating_mul(r.system_contributions.into()) / total_contrib.into();
		let _ = Self::charge(&Self::account_id(), system_payout);
		revenue.saturating_reduce(system_payout);

		if !revenue.is_zero() && r.private_contributions > 0 {
			r.maybe_payout = Some(revenue);
			InstaPoolHistory::<T>::insert(when, &r);
			Self::deposit_event(Event::<T>::ClaimsReady {
				when,
				system_payout,
				private_payout: revenue,
			});
		} else {
			InstaPoolHistory::<T>::remove(when);
			Self::deposit_event(Event::<T>::HistoryDropped { when, revenue });
		}
		true
	}

	/// Begin selling for the next sale period.
	///
	/// Triggered by Relay-chain block number/timeslice.
	pub(crate) fn rotate_sale(
		old_sale: SaleInfoRecordOf<T>,
		config: &ConfigRecordOf<T>,
		status: &StatusRecord,
	) -> Option<()> {
		let now = frame_system::Pallet::<T>::block_number();

		let pool_item =
			ScheduleItem { assignment: CoreAssignment::Pool, mask: CoreMask::complete() };
		let just_pool = Schedule::truncate_from(vec![pool_item]);

		// Clean up the old sale - we need to use up any unused cores by putting them into the
		// InstaPool.
		let mut old_pooled: SignedCoreMaskBitCount = 0;
		for i in old_sale.cores_sold..old_sale.cores_offered {
			old_pooled.saturating_accrue(80);
			Workplan::<T>::insert((old_sale.region_begin, old_sale.first_core + i), &just_pool);
		}
		InstaPoolIo::<T>::mutate(old_sale.region_begin, |r| r.system.saturating_accrue(old_pooled));
		InstaPoolIo::<T>::mutate(old_sale.region_end, |r| r.system.saturating_reduce(old_pooled));

		// Calculate the start price for the upcoming sale.
		let price = {
			let offered = old_sale.cores_offered;
			let ideal = old_sale.ideal_cores_sold;
			let sold = old_sale.cores_sold;

			let maybe_purchase_price = if offered == 0 {
				// No cores offered for sale - no purchase price.
				None
			} else if sold >= ideal {
				// Sold more than the ideal amount. We should look for the last purchase price
				// before the sell-out. If there was no purchase at all, then we avoid having a
				// price here so that we make no alterations to it (since otherwise we would
				// increase it).
				old_sale.sellout_price
			} else {
				// Sold less than the ideal - we fall back to the regular price.
				Some(old_sale.price)
			};
			if let Some(purchase_price) = maybe_purchase_price {
				T::PriceAdapter::adapt_price(sold.min(offered), ideal, offered)
					.saturating_mul_int(purchase_price)
			} else {
				old_sale.price
			}
		};

		// Set workload for the reserved (system, probably) workloads.
		let region_begin = old_sale.region_end;
		let region_end = region_begin + config.region_length;

		let mut first_core = 0;
		let mut total_pooled: SignedCoreMaskBitCount = 0;
		for schedule in Reservations::<T>::get().into_iter() {
			let parts: u32 = schedule
				.iter()
				.filter(|i| matches!(i.assignment, CoreAssignment::Pool))
				.map(|i| i.mask.count_ones())
				.sum();
			total_pooled.saturating_accrue(parts as i32);

			Workplan::<T>::insert((region_begin, first_core), &schedule);
			first_core.saturating_inc();
		}
		InstaPoolIo::<T>::mutate(region_begin, |r| r.system.saturating_accrue(total_pooled));
		InstaPoolIo::<T>::mutate(region_end, |r| r.system.saturating_reduce(total_pooled));

		let mut leases = Leases::<T>::get();
		// Can morph to a renewable as long as it's >=begin and <end.
		leases.retain(|&LeaseRecordItem { until, task }| {
			let mask = CoreMask::complete();
			let assignment = CoreAssignment::Task(task);
			let schedule = BoundedVec::truncate_from(vec![ScheduleItem { mask, assignment }]);
			Workplan::<T>::insert((region_begin, first_core), &schedule);
			let expiring = until >= region_begin && until < region_end;
			if expiring {
				// last time for this one - make it renewable.
				let renewal_id = AllowedRenewalId { core: first_core, when: region_end };
				let record = AllowedRenewalRecord { price, completion: Complete(schedule) };
				AllowedRenewals::<T>::insert(renewal_id, &record);
				Self::deposit_event(Event::Renewable {
					core: first_core,
					price,
					begin: region_end,
					workload: record.completion.drain_complete().unwrap_or_default(),
				});
				Self::deposit_event(Event::LeaseEnding { when: region_end, task });
			}
			first_core.saturating_inc();
			!expiring
		});
		Leases::<T>::put(&leases);

		let max_possible_sales = status.core_count.saturating_sub(first_core);
		let limit_cores_offered = config.limit_cores_offered.unwrap_or(CoreIndex::max_value());
		let cores_offered = limit_cores_offered.min(max_possible_sales);
		let sale_start = now.saturating_add(config.interlude_length);
		let leadin_length = config.leadin_length;
		let ideal_cores_sold = (config.ideal_bulk_proportion * cores_offered as u32) as u16;
		// Update SaleInfo
		let new_sale = SaleInfoRecord {
			sale_start,
			leadin_length,
			price,
			sellout_price: None,
			region_begin,
			region_end,
			first_core,
			ideal_cores_sold,
			cores_offered,
			cores_sold: 0,
		};
		SaleInfo::<T>::put(&new_sale);
		Self::deposit_event(Event::SaleInitialized {
			sale_start,
			leadin_length,
			start_price: Self::sale_price(&new_sale, now),
			regular_price: price,
			region_begin,
			region_end,
			ideal_cores_sold,
			cores_offered,
		});

		Some(())
	}

	pub(crate) fn process_pool(when: Timeslice, status: &mut StatusRecord) {
		let pool_io = InstaPoolIo::<T>::take(when);
		status.private_pool_size = (status.private_pool_size as SignedCoreMaskBitCount)
			.saturating_add(pool_io.private) as CoreMaskBitCount;
		status.system_pool_size = (status.system_pool_size as SignedCoreMaskBitCount)
			.saturating_add(pool_io.system) as CoreMaskBitCount;
		let record = InstaPoolHistoryRecord {
			private_contributions: status.private_pool_size,
			system_contributions: status.system_pool_size,
			maybe_payout: None,
		};
		InstaPoolHistory::<T>::insert(when, record);
		Self::deposit_event(Event::<T>::HistoryInitialized {
			when,
			private_pool_size: status.private_pool_size,
			system_pool_size: status.system_pool_size,
		});
	}

	/// Schedule cores for the given `timeslice`.
	pub(crate) fn process_core_schedule(
		timeslice: Timeslice,
		rc_begin: RelayBlockNumberOf<T>,
		core: CoreIndex,
	) {
		let Some(workplan) = Workplan::<T>::take((timeslice, core)) else {
			return;
		};
		let workload = Workload::<T>::get(core);
		let parts_used = workplan.iter().map(|i| i.mask).fold(CoreMask::void(), |a, i| a | i);
		let mut workplan = workplan.into_inner();
		workplan.extend(workload.into_iter().filter(|i| (i.mask & parts_used).is_void()));
		let workplan = Schedule::truncate_from(workplan);
		Workload::<T>::insert(core, &workplan);

		let mut total_used = 0;
		let mut intermediate = workplan
			.into_iter()
			.map(|i| (i.assignment, i.mask.count_ones() as u16 * (57_600 / 80)))
			.inspect(|i| total_used.saturating_accrue(i.1))
			.collect::<Vec<_>>();
		if total_used < 57_600 {
			intermediate.push((CoreAssignment::Idle, 57_600 - total_used));
		}
		intermediate.sort();
		let mut assignment: Vec<(CoreAssignment, PartsOf57600)> =
			Vec::with_capacity(intermediate.len());
		for i in intermediate.into_iter() {
			if let Some(ref mut last) = assignment.last_mut() {
				if last.0 == i.0 {
					last.1 += i.1;
					continue
				}
			}
			assignment.push(i);
		}
		T::Coretime::assign_core(core, rc_begin, assignment.clone(), None);
		Self::deposit_event(Event::<T>::CoreAssigned { core, when: rc_begin, assignment });
	}
}
