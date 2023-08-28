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
use frame_support::{
	pallet_prelude::{DispatchResult, *},
	traits::{fungible::Mutate, tokens::Preservation::Expendable, DefensiveResult},
};
use sp_arithmetic::traits::{CheckedDiv, Saturating, Zero};
use sp_runtime::traits::Convert;
use CompletionStatus::{Complete, Partial};

impl<T: Config> Pallet<T> {
	pub(crate) fn do_configure(config: ConfigRecordOf<T>) -> DispatchResult {
		config.validate().map_err(|()| Error::<T>::InvalidConfig)?;
		Configuration::<T>::put(config);
		Ok(())
	}

	pub(crate) fn do_request_core_count(core_count: CoreIndex) -> DispatchResult {
		T::Coretime::request_core_count(core_count);
		Self::deposit_event(Event::<T>::CoreCountRequested { core_count });
		Ok(())
	}

	pub(crate) fn do_reserve(workload: Schedule) -> DispatchResult {
		let mut r = Reservations::<T>::get();
		let index = r.len() as u32;
		r.try_push(workload.clone()).map_err(|_| Error::<T>::TooManyReservations)?;
		Reservations::<T>::put(r);
		Self::deposit_event(Event::<T>::ReservationMade { index, workload });
		Ok(())
	}

	pub(crate) fn do_unreserve(index: u32) -> DispatchResult {
		let mut r = Reservations::<T>::get();
		ensure!(index < r.len() as u32, Error::<T>::UnknownReservation);
		let workload = r.remove(index as usize);
		Reservations::<T>::put(r);
		Self::deposit_event(Event::<T>::ReservationCancelled { index, workload });
		Ok(())
	}

	pub(crate) fn do_set_lease(task: TaskId, until: Timeslice) -> DispatchResult {
		let mut r = Leases::<T>::get();
		ensure!(until > Self::current_timeslice(), Error::<T>::AlreadyExpired);
		r.try_push(LeaseRecordItem { until, task })
			.map_err(|_| Error::<T>::TooManyLeases)?;
		Leases::<T>::put(r);
		Self::deposit_event(Event::<T>::Leased { until, task });
		Ok(())
	}

	pub(crate) fn do_start_sales(price: BalanceOf<T>, core_count: CoreIndex) -> DispatchResult {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let commit_timeslice = Self::latest_timeslice_ready_to_commit(&config);
		let status = StatusRecord {
			core_count,
			private_pool_size: 0,
			system_pool_size: 0,
			last_committed_timeslice: commit_timeslice.saturating_sub(1),
			last_timeslice: Self::current_timeslice(),
		};
		let now = frame_system::Pallet::<T>::block_number();
		let dummy_sale = SaleInfoRecord {
			sale_start: now,
			leadin_length: Zero::zero(),
			price,
			sellout_price: None,
			region_begin: commit_timeslice,
			region_end: commit_timeslice.saturating_add(config.region_length),
			first_core: 0,
			ideal_cores_sold: 0,
			cores_offered: 0,
			cores_sold: 0,
		};
		Self::deposit_event(Event::<T>::SalesStarted { price, core_count });
		Self::rotate_sale(dummy_sale, &config, &status);
		Status::<T>::put(&status);
		Ok(())
	}

	pub(crate) fn do_purchase(
		who: T::AccountId,
		price_limit: BalanceOf<T>,
	) -> Result<RegionId, DispatchError> {
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
		ensure!(sale.first_core < status.core_count, Error::<T>::Unavailable);
		ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);
		let now = frame_system::Pallet::<T>::block_number();
		ensure!(now > sale.sale_start, Error::<T>::TooEarly);
		let price = Self::sale_price(&sale, now);
		ensure!(price_limit >= price, Error::<T>::Overpriced);

		Self::charge(&who, price)?;
		let core = sale.first_core.saturating_add(sale.cores_sold);
		sale.cores_sold.saturating_inc();
		if sale.cores_sold <= sale.ideal_cores_sold || sale.sellout_price.is_none() {
			sale.sellout_price = Some(price);
		}
		SaleInfo::<T>::put(&sale);
		let id = Self::issue(core, sale.region_begin, sale.region_end, who.clone(), Some(price));
		let duration = sale.region_end.saturating_sub(sale.region_begin);
		Self::deposit_event(Event::Purchased { who, region_id: id, price, duration });
		Ok(id)
	}

	/// Must be called on a core in `AllowedRenewals` whose value is a timeslice equal to the
	/// current sale status's `region_end`.
	pub(crate) fn do_renew(who: T::AccountId, core: CoreIndex) -> Result<CoreIndex, DispatchError> {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
		ensure!(sale.first_core < status.core_count, Error::<T>::Unavailable);
		ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);

		let renewal_id = AllowedRenewalId { core, when: sale.region_begin };
		let record = AllowedRenewals::<T>::get(renewal_id).ok_or(Error::<T>::NotAllowed)?;
		let workload =
			record.completion.drain_complete().ok_or(Error::<T>::IncompleteAssignment)?;

		let old_core = core;
		let core = sale.first_core.saturating_add(sale.cores_sold);
		Self::charge(&who, record.price)?;
		Self::deposit_event(Event::Renewed {
			who,
			old_core,
			core,
			price: record.price,
			begin: sale.region_begin,
			duration: sale.region_end.saturating_sub(sale.region_begin),
			workload: workload.clone(),
		});

		sale.cores_sold.saturating_inc();

		Workplan::<T>::insert((sale.region_begin, core), &workload);

		let begin = sale.region_end;
		let price_cap = record.price + config.renewal_bump * record.price;
		let now = frame_system::Pallet::<T>::block_number();
		let price = Self::sale_price(&sale, now).min(price_cap);
		let new_record = AllowedRenewalRecord { price, completion: Complete(workload) };
		AllowedRenewals::<T>::remove(renewal_id);
		AllowedRenewals::<T>::insert(AllowedRenewalId { core, when: begin }, &new_record);
		SaleInfo::<T>::put(&sale);
		if let Some(workload) = new_record.completion.drain_complete() {
			Self::deposit_event(Event::Renewable { core, price, begin, workload });
		}
		Ok(core)
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
		let duration = region.end.saturating_sub(region_id.begin);
		Self::deposit_event(Event::Transferred {
			region_id,
			old_owner,
			owner: region.owner,
			duration,
		});

		Ok(())
	}

	pub(crate) fn do_partition(
		region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		pivot_offset: Timeslice,
	) -> Result<(RegionId, RegionId), Error<T>> {
		let mut region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

		if let Some(check_owner) = maybe_check_owner {
			ensure!(check_owner == region.owner, Error::<T>::NotOwner);
		}
		let pivot = region_id.begin.saturating_add(pivot_offset);
		ensure!(pivot < region.end, Error::<T>::PivotTooLate);
		ensure!(pivot > region_id.begin, Error::<T>::PivotTooEarly);

		region.paid = None;
		let new_region_ids = (region_id, RegionId { begin: pivot, ..region_id });

		Regions::<T>::insert(&new_region_ids.0, &RegionRecord { end: pivot, ..region.clone() });
		Regions::<T>::insert(&new_region_ids.1, &region);
		Self::deposit_event(Event::Partitioned { old_region_id: region_id, new_region_ids });

		Ok(new_region_ids)
	}

	pub(crate) fn do_interlace(
		region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		pivot: CoreMask,
	) -> Result<(RegionId, RegionId), Error<T>> {
		let region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

		if let Some(check_owner) = maybe_check_owner {
			ensure!(check_owner == region.owner, Error::<T>::NotOwner);
		}

		ensure!((pivot & !region_id.mask).is_void(), Error::<T>::ExteriorPivot);
		ensure!(!pivot.is_void(), Error::<T>::VoidPivot);
		ensure!(pivot != region_id.mask, Error::<T>::CompletePivot);

		let one = RegionId { mask: pivot, ..region_id };
		Regions::<T>::insert(&one, &region);
		let other = RegionId { mask: region_id.mask ^ pivot, ..region_id };
		Regions::<T>::insert(&other, &region);

		let new_region_ids = (one, other);
		Self::deposit_event(Event::Interlaced { old_region_id: region_id, new_region_ids });
		Ok(new_region_ids)
	}

	pub(crate) fn do_assign(
		region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		target: TaskId,
		finality: Finality,
	) -> Result<(), Error<T>> {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		if let Some((region_id, region)) = Self::utilize(region_id, maybe_check_owner, finality)? {
			let workplan_key = (region_id.begin, region_id.core);
			let mut workplan = Workplan::<T>::get(&workplan_key).unwrap_or_default();
			// Ensure no previous allocations exist.
			workplan.retain(|i| (i.mask & region_id.mask).is_void());
			if workplan
				.try_push(ScheduleItem {
					mask: region_id.mask,
					assignment: CoreAssignment::Task(target),
				})
				.is_ok()
			{
				Workplan::<T>::insert(&workplan_key, &workplan);
			}

			let duration = region.end.saturating_sub(region_id.begin);
			if duration == config.region_length && finality == Finality::Final {
				if let Some(price) = region.paid {
					let renewal_id = AllowedRenewalId { core: region_id.core, when: region.end };
					let assigned = match AllowedRenewals::<T>::get(renewal_id) {
						Some(AllowedRenewalRecord { completion: Partial(w), price: p })
							if price == p =>
							w,
						_ => CoreMask::void(),
					} | region_id.mask;
					let workload =
						if assigned.is_complete() { Complete(workplan) } else { Partial(assigned) };
					let record = AllowedRenewalRecord { price, completion: workload };
					AllowedRenewals::<T>::insert(&renewal_id, &record);
					if let Some(workload) = record.completion.drain_complete() {
						Self::deposit_event(Event::Renewable {
							core: region_id.core,
							price,
							begin: region.end,
							workload,
						});
					}
				}
			}
			Self::deposit_event(Event::Assigned { region_id, task: target, duration });
		}
		Ok(())
	}

	pub(crate) fn do_pool(
		region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		payee: T::AccountId,
		finality: Finality,
	) -> Result<(), Error<T>> {
		if let Some((region_id, region)) = Self::utilize(region_id, maybe_check_owner, finality)? {
			let workplan_key = (region_id.begin, region_id.core);
			let mut workplan = Workplan::<T>::get(&workplan_key).unwrap_or_default();
			let duration = region.end.saturating_sub(region_id.begin);
			if workplan
				.try_push(ScheduleItem { mask: region_id.mask, assignment: CoreAssignment::Pool })
				.is_ok()
			{
				Workplan::<T>::insert(&workplan_key, &workplan);
				let size = region_id.mask.count_ones() as i32;
				InstaPoolIo::<T>::mutate(region_id.begin, |a| a.private.saturating_accrue(size));
				InstaPoolIo::<T>::mutate(region.end, |a| a.private.saturating_reduce(size));
				let record = ContributionRecord { length: duration, payee };
				InstaPoolContribution::<T>::insert(&region_id, record);
			}

			Self::deposit_event(Event::Pooled { region_id, duration });
		}
		Ok(())
	}

	pub(crate) fn do_claim_revenue(
		mut region: RegionId,
		max_timeslices: Timeslice,
	) -> DispatchResult {
		let mut contribution =
			InstaPoolContribution::<T>::take(region).ok_or(Error::<T>::UnknownContribution)?;
		let contributed_parts = region.mask.count_ones();

		Self::deposit_event(Event::RevenueClaimBegun { region, max_timeslices });

		let mut payout = BalanceOf::<T>::zero();
		let last = region.begin + contribution.length.min(max_timeslices);
		for r in region.begin..last {
			region.begin = r + 1;
			contribution.length.saturating_dec();

			let Some(mut pool_record) = InstaPoolHistory::<T>::get(r) else { continue };
			let Some(total_payout) = pool_record.maybe_payout else { break };
			let p = total_payout
				.saturating_mul(contributed_parts.into())
				.checked_div(&pool_record.private_contributions.into())
				.unwrap_or_default();

			payout.saturating_accrue(p);
			pool_record.private_contributions.saturating_reduce(contributed_parts);

			let remaining_payout = total_payout.saturating_sub(p);
			if !remaining_payout.is_zero() && pool_record.private_contributions > 0 {
				pool_record.maybe_payout = Some(remaining_payout);
				InstaPoolHistory::<T>::insert(r, &pool_record);
			} else {
				InstaPoolHistory::<T>::remove(r);
			}
			if !p.is_zero() {
				Self::deposit_event(Event::RevenueClaimItem { when: r, amount: p });
			}
		}

		if contribution.length > 0 {
			InstaPoolContribution::<T>::insert(region, &contribution);
		}
		T::Currency::transfer(&Self::account_id(), &contribution.payee, payout, Expendable)
			.defensive_ok();
		let next = if last < region.begin + contribution.length { Some(region) } else { None };
		Self::deposit_event(Event::RevenueClaimPaid {
			who: contribution.payee,
			amount: payout,
			next,
		});
		Ok(())
	}

	pub(crate) fn do_purchase_credit(
		who: T::AccountId,
		amount: BalanceOf<T>,
		beneficiary: RelayAccountIdOf<T>,
	) -> DispatchResult {
		T::Currency::transfer(&who, &Self::account_id(), amount, Expendable)?;
		let rc_amount = T::ConvertBalance::convert(amount);
		T::Coretime::credit_account(beneficiary.clone(), rc_amount);
		Self::deposit_event(Event::<T>::CreditPurchased { who, beneficiary, amount });
		Ok(())
	}

	pub(crate) fn do_drop_region(region_id: RegionId) -> DispatchResult {
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;
		ensure!(status.last_committed_timeslice >= region.end, Error::<T>::StillValid);

		Regions::<T>::remove(&region_id);
		let duration = region.end.saturating_sub(region_id.begin);
		Self::deposit_event(Event::RegionDropped { region_id, duration });
		Ok(())
	}

	pub(crate) fn do_drop_contribution(region_id: RegionId) -> DispatchResult {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let contrib =
			InstaPoolContribution::<T>::get(&region_id).ok_or(Error::<T>::UnknownContribution)?;
		let end = region_id.begin.saturating_add(contrib.length);
		ensure!(
			status.last_timeslice >= end.saturating_add(config.contribution_timeout),
			Error::<T>::StillValid
		);
		InstaPoolContribution::<T>::remove(region_id);
		Self::deposit_event(Event::ContributionDropped { region_id });
		Ok(())
	}

	pub(crate) fn do_drop_history(when: Timeslice) -> DispatchResult {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		ensure!(status.last_timeslice > when + config.contribution_timeout, Error::<T>::StillValid);
		let record = InstaPoolHistory::<T>::take(when).ok_or(Error::<T>::NoHistory)?;
		if let Some(payout) = record.maybe_payout {
			let _ = Self::charge(&Self::account_id(), payout);
		}
		let revenue = record.maybe_payout.unwrap_or_default();
		Self::deposit_event(Event::HistoryDropped { when, revenue });
		Ok(())
	}

	pub(crate) fn do_drop_renewal(core: CoreIndex, when: Timeslice) -> DispatchResult {
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		ensure!(status.last_committed_timeslice >= when, Error::<T>::StillValid);
		let id = AllowedRenewalId { core, when };
		ensure!(AllowedRenewals::<T>::contains_key(id), Error::<T>::UnknownRenewal);
		AllowedRenewals::<T>::remove(id);
		Self::deposit_event(Event::AllowedRenewalDropped { core, when });
		Ok(())
	}
}
