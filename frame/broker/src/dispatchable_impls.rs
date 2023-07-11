use super::*;
use CompletionStatus::{Complete, Partial};
use sp_runtime::traits::{Convert, ConvertBack, AccountIdConversion};
use frame_support::{
	pallet_prelude::{*, DispatchResult},
	traits::{
		tokens::{Precision::Exact, Preservation::Expendable, Fortitude::Polite},
		fungible::{Mutate, Balanced}, OnUnbalanced, DefensiveResult,
	}
};
use sp_arithmetic::{traits::{Zero, SaturatedConversion, Saturating}, Perbill, PerThing};

impl<T: Config> Pallet<T> {
	pub(crate) fn do_configure(config: ConfigRecordOf<T>) -> DispatchResult {
		Configuration::<T>::put(config);
		Ok(())
	}

	pub(crate) fn do_reserve(schedule: Schedule) -> DispatchResult {
		let mut r = Reservations::<T>::get();
		r.try_push(schedule).map_err(|_| Error::<T>::TooManyReservations)?;
		Reservations::<T>::put(r);
		Ok(())
	}

	pub(crate) fn do_unreserve(item_index: u32) -> DispatchResult {
		let mut r = Reservations::<T>::get();
		r.remove(item_index as usize);
		Reservations::<T>::put(r);
		Ok(())
	}

	pub(crate) fn do_set_lease(task: TaskId, until: Timeslice) -> DispatchResult {
		let mut r = Leases::<T>::get();
		r.try_push((until, task)).map_err(|_| Error::<T>::TooManyLeases)?;
		Leases::<T>::put(r);
		Ok(())
	}

	pub(crate) fn do_start_sales(
		reserve_price: BalanceOf<T>,
	) -> DispatchResult {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let status = StatusRecord {
			pool_size: 0,
			last_timeslice: Self::current_timeslice(),
			system_pool_size: 0,
		};
		let commit_timeslice = status.last_timeslice + config.advance_notice;
		let now = frame_system::Pallet::<T>::block_number();
		let dummy_sale = SaleInfoRecord {
			sale_start: now,
			leadin_length: Zero::zero(),
			start_price: Zero::zero(),
			reserve_price,
			region_begin: commit_timeslice,
			region_end: commit_timeslice + config.region_length,
			first_core: 0,
			ideal_cores_sold: 0,
			cores_offered: 0,
			cores_sold: 0,
		};
		Self::rotate_sale(dummy_sale, &config);
		Status::<T>::put(&status);
		Ok(())
	}

	pub(crate) fn do_purchase(
		who: T::AccountId,
		price_limit: BalanceOf<T>,
	) -> Result<RegionId, DispatchError> {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
		ensure!(sale.first_core < config.core_count, Error::<T>::Unavailable);
		ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);
		let now = frame_system::Pallet::<T>::block_number();
		ensure!(now > sale.sale_start, Error::<T>::TooEarly);
		let price = lerp(
			now,
			sale.sale_start,
			sale.leadin_length,
			sale.start_price,
			sale.reserve_price,
		).ok_or(Error::<T>::IndeterminablePrice)?;
		ensure!(price_limit >= price, Error::<T>::Overpriced);

		Self::charge(&who, price)?;
		let core = sale.first_core + sale.cores_sold;
		sale.cores_sold.saturating_inc();
		SaleInfo::<T>::put(&sale);
		let id = Self::issue(core, sale.region_begin, sale.region_end, who.clone(), Some(price));
		let length = sale.region_end.saturating_sub(sale.region_begin);
		Self::deposit_event(Event::Purchased { who, region_id: id, price, length });
		Ok(id)
	}

	/// Must be called on a core in `AllowedRenewals` whose value is a timeslice equal to the
	/// current sale status's `region_end`.
	pub(crate) fn do_renew(who: T::AccountId, core: CoreIndex) -> Result<CoreIndex, DispatchError> {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let record = AllowedRenewals::<T>::get(core).ok_or(Error::<T>::NotAllowed)?;
		let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
		let workload = record.completion.drain_complete().ok_or(Error::<T>::IncompleteAssignment)?;

		ensure!(record.begin == sale.region_begin, Error::<T>::WrongTime);
		ensure!(sale.first_core < config.core_count, Error::<T>::Unavailable);
		ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);

		Self::charge(&who, record.price)?;
		Self::deposit_event(Event::Renewed {
			who,
			core,
			price: record.price,
			begin: sale.region_begin,
			length: sale.region_end.saturating_sub(sale.region_begin),
			workload: workload.clone(),
		});

		let core = sale.first_core + sale.cores_sold;
		sale.cores_sold.saturating_inc();

		Workplan::<T>::insert((record.begin, core), &workload);

		let begin = sale.region_end;
		let price = record.price + config.renewal_bump * record.price;
		let new_record = AllowedRenewalRecord { begin, price, completion: Complete(workload) };
		AllowedRenewals::<T>::insert(core, &new_record);
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
		Self::deposit_event(Event::Transferred { region_id, old_owner, owner: region.owner });

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

		region.paid = None;
		let new_region_id = RegionId { begin: pivot, ..region_id.clone() };
		let new_region = RegionRecord { end: pivot, ..region.clone() };

		Regions::<T>::insert(&region_id, &new_region);
		Regions::<T>::insert(&new_region_id, &region);
		Self::deposit_event(Event::Partitioned { region_id, pivot, new_region_id });

		Ok((region_id, new_region_id))
	}

	pub(crate) fn do_interlace(
		mut region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		pivot: CorePart,
	) -> Result<(RegionId, RegionId), Error<T>> {
		let region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

		if let Some(check_owner) = maybe_check_owner {
			ensure!(check_owner == region.owner, Error::<T>::NotOwner);
		}

		ensure!((pivot & !region_id.part).is_void(), Error::<T>::ExteriorPivot);
		ensure!(!pivot.is_void(), Error::<T>::NullPivot);
		ensure!(pivot != region_id.part, Error::<T>::CompletePivot);

		let antipivot = region_id.part ^ pivot;
		region_id.part = pivot;
		Regions::<T>::insert(&region_id, &region);
		let new_region_id = RegionId { part: antipivot, ..region_id };
		Regions::<T>::insert(&new_region_id, &region);

		Self::deposit_event(Event::Interlaced { region_id, pivot, new_region_id });

		Ok((region_id, new_region_id))
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
				if let Some(price) = region.paid {
					let begin = region.end;
					let assigned = match AllowedRenewals::<T>::get(region_id.core) {
						Some(AllowedRenewalRecord { completion: Partial(w), begin: b, price: p })
							if begin == b && price == p => w,
						_ => CorePart::void(),
					} | region_id.part;
					let workload = if assigned.is_complete() {
						Complete(workplan)
					} else {
						Partial(assigned)
					};
					let record = AllowedRenewalRecord { begin, price, completion: workload };
					AllowedRenewals::<T>::insert(region_id.core, &record);
					if let Some(workload) = record.completion.drain_complete() {
						Self::deposit_event(Event::Renewable { core: region_id.core, price, begin, workload });
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
				let size = region_id.part.count_ones() as i32;
				InstaPoolIo::<T>::mutate(region_id.begin, |a| a.total.saturating_accrue(size));
				InstaPoolIo::<T>::mutate(region.end, |a| a.total.saturating_reduce(size));
				let record = ContributionRecord {
					length: region.end.saturating_sub(region_id.begin),
					payee,
				};
				InstaPoolContribution::<T>::insert(&region_id, record);
			}
			Self::deposit_event(Event::Pooled { region_id });
		}
		Ok(())
	}

	// TODO: Consolidation of InstaPoolHistory records as long as contributors don't change.
	pub(crate) fn do_claim_revenue(mut region: RegionId, max_timeslices: Timeslice) -> DispatchResult {
		let mut contribution = InstaPoolContribution::<T>::take(region)
			.ok_or(Error::<T>::UnknownContribution)?;
		let contributed_parts = region.part.count_ones();

		let mut payout = BalanceOf::<T>::zero();
		let last = region.begin + contribution.length.min(max_timeslices);
		for r in region.begin..last {
			let mut pool_record = match InstaPoolHistory::<T>::get(r) { Some(x) => x, None => continue };
			let total_payout = match pool_record.maybe_payout { Some(x) => x, None => break };
			region.begin = r;
			contribution.length.saturating_dec();
			payout.saturating_accrue(total_payout.saturating_mul(contributed_parts.into())
				/ pool_record.total_contributions.into());
			pool_record.total_contributions.saturating_reduce(contributed_parts);

			let remaining_payout = total_payout.saturating_sub(payout);
			if !remaining_payout.is_zero() && pool_record.total_contributions > 0 {
				pool_record.maybe_payout = Some(remaining_payout);
				InstaPoolHistory::<T>::insert(region.begin, &pool_record);
			} else {
				InstaPoolHistory::<T>::remove(region.begin);
			}
		};

		if contribution.length > 0 {
			InstaPoolContribution::<T>::insert(region, &contribution);
		}
		T::Currency::transfer(&Self::account_id(), &contribution.payee, payout, Expendable).defensive_ok();
		Ok(())
	}

	pub(crate) fn do_purchase_credit(
		who: T::AccountId,
		amount: BalanceOf<T>,
		beneficiary: RelayAccountIdOf<T>,
	) -> DispatchResult {
		T::Currency::transfer(&who, &Self::account_id(), amount, Expendable)?;
		let amount = T::ConvertBalance::convert(amount);
		T::Coretime::credit_account(beneficiary, amount);
		Ok(())
	}
}