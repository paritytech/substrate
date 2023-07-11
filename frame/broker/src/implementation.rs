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

	/// Attempt to tick things along. Will only do anything if the `Status.last_timeslice` is
	/// less than `Self::current_timeslice`.
	pub(crate) fn do_tick() -> DispatchResult {
		let mut status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let current_timeslice = Self::current_timeslice();
		ensure!(status.last_timeslice < current_timeslice, Error::<T>::NothingToDo);
		status.last_timeslice.saturating_inc();

		T::Coretime::request_revenue_info_at(T::TimeslicePeriod::get() * status.last_timeslice.into());

		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let commit_timeslice = status.last_timeslice + config.advance_notice;

		if let Some(sale) = SaleInfo::<T>::get() {
			if commit_timeslice >= sale.region_begin {
				// Sale can be rotated.
				Self::rotate_sale(sale, &config);
			}
		}

		Self::process_timeslice(commit_timeslice, &mut status, &config);

		Status::<T>::put(&status);
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
		old_sale: SaleInfoRecordOf<T>,
		config: &ConfigRecordOf<T>,
	) -> Option<()> {
		let now = frame_system::Pallet::<T>::block_number();

		let pool_item = ScheduleItem { assignment: CoreAssignment::Pool, part: CorePart::complete() };
		let just_pool = Schedule::truncate_from(vec![pool_item]);

		// Clean up the old sale - we need to use up any unused cores by putting them into the
		// InstaPool.
		let mut total_old_pooled: SignedPartCount = 0;
		for i in old_sale.cores_sold..old_sale.cores_offered {
			total_old_pooled.saturating_accrue(80);
			Workplan::<T>::insert((old_sale.region_begin, old_sale.first_core + i), &just_pool);
		}
		InstaPoolIo::<T>::mutate(old_sale.region_begin, |r| {
			r.total.saturating_accrue(total_old_pooled);
			r.system.saturating_accrue(total_old_pooled);
		});
		InstaPoolIo::<T>::mutate(old_sale.region_end, |r| {
			r.total.saturating_reduce(total_old_pooled);
			r.system.saturating_reduce(total_old_pooled);
		});

		// Calculate the start price for the sale after.
		let reserve_price = {
			let offered = old_sale.cores_offered;
			let ideal = old_sale.ideal_cores_sold;
			let sold = old_sale.cores_sold;
			let old_price = old_sale.reserve_price;
			if offered > 0 {
				Self::bump_price(offered, ideal, sold, old_price)
			} else {
				old_price
			}
		};
		let start_price = reserve_price * 2u32.into();

		// Set workload for the reserved (system, probably) workloads.
		let region_begin = old_sale.region_end;
		let region_end = region_begin + config.region_length;

		let mut first_core = 0;
		let mut total_pooled: SignedPartCount = 0;
		for schedule in Reservations::<T>::get().into_iter() {
			let parts: u32 = schedule.iter()
				.filter(|i| matches!(i.assignment, CoreAssignment::Pool))
				.map(|i| i.part.count_ones())
				.sum();
			total_pooled.saturating_accrue(parts as i32);

			Workplan::<T>::insert((region_begin, first_core), &schedule);
			first_core.saturating_inc();
		}
		InstaPoolIo::<T>::mutate(region_begin, |r| {
			r.total.saturating_accrue(total_pooled);
			r.system.saturating_accrue(total_pooled);
		});
		InstaPoolIo::<T>::mutate(region_end, |r| {
			r.total.saturating_reduce(total_pooled);
			r.system.saturating_reduce(total_pooled);
		});

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
					completion: Complete(schedule),
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

	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account_truncating()
	}

	pub(crate) fn do_check_revenue() -> Result<bool, DispatchError> {
		if let Some((until, amount)) = T::Coretime::check_notify_revenue_info() {
			let timeslice: Timeslice = (until / T::TimeslicePeriod::get()).saturated_into();
			let mut amount = T::ConvertBalance::convert_back(amount);
			if amount.is_zero() {
				InstaPoolHistory::<T>::remove(timeslice);
				return Ok(true)
			}
			let mut pool_record = InstaPoolHistory::<T>::get(timeslice).unwrap_or_default();
			ensure!(pool_record.maybe_payout.is_none(), Error::<T>::RevenueAlreadyKnown);
			ensure!(pool_record.total_contributions >= pool_record.system_contributions, Error::<T>::InvalidContributions);
			ensure!(pool_record.total_contributions > 0, Error::<T>::InvalidContributions);

			// Payout system InstaPool Cores.
			let system_payout = amount.saturating_mul(pool_record.system_contributions.into())
				/ pool_record.total_contributions.into();
			let _ = Self::charge(&Self::account_id(), system_payout);
			pool_record.total_contributions.saturating_reduce(pool_record.system_contributions);
			pool_record.system_contributions = 0;
			amount.saturating_reduce(system_payout);

			if !amount.is_zero() && pool_record.total_contributions > 0 {
				pool_record.maybe_payout = Some(amount);
				InstaPoolHistory::<T>::insert(timeslice, &pool_record);
			} else {
				InstaPoolHistory::<T>::remove(timeslice);
			}
			return Ok(true)
		}
		Ok(false)
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

	pub(crate) fn process_timeslice(timeslice: Timeslice, status: &mut StatusRecord, config: &ConfigRecordOf<T>) {
		Self::process_pool(timeslice, status);
		let rc_begin = RelayBlockNumberOf::<T>::from(timeslice) * T::TimeslicePeriod::get();
		for core in 0..config.core_count {
			Self::process_core_schedule(timeslice, rc_begin, core);
		}
	}

	fn process_pool(timeslice: Timeslice, status: &mut StatusRecord) {
		let pool_io = InstaPoolIo::<T>::take(timeslice);
		status.pool_size = (status.pool_size as i32).saturating_add(pool_io.total) as u32;
		status.system_pool_size = (status.system_pool_size as i32).saturating_add(pool_io.system) as u32;
		let record = InstaPoolHistoryRecord {
			total_contributions: status.pool_size,
			system_contributions: status.system_pool_size,
			maybe_payout: None,
		};
		InstaPoolHistory::<T>::insert(timeslice, record);
	}

	/// Schedule cores for the given `timeslice`.
	fn process_core_schedule(
		timeslice: Timeslice,
		rc_begin: RelayBlockNumberOf<T>,
		core: CoreIndex,
	) {
		let workplan = match Workplan::<T>::take((timeslice, core)) {
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
		let record = AllowedRenewals::<T>::get(core).ok_or(Error::<T>::NotAllowed)?;
		let mut sale = SaleInfo::<T>::get().ok_or(Error::<T>::NoSales)?;
		let workload = record.completion.complete().ok_or(Error::<T>::IncompleteAssignment)?;

		ensure!(record.begin == sale.region_begin, Error::<T>::WrongTime);
		ensure!(sale.first_core < config.core_count, Error::<T>::Unavailable);
		ensure!(sale.cores_sold < sale.cores_offered, Error::<T>::SoldOut);

		Self::charge(who, record.price)?;

		let core = sale.first_core + sale.cores_sold;
		sale.cores_sold.saturating_inc();

		Workplan::<T>::insert((record.begin, core), workload);

		let begin = sale.region_end;
		let price = record.price + record.price / 100u32.into() * 2u32.into();
		let new_record = AllowedRenewalRecord { begin, price, .. record };
		AllowedRenewals::<T>::insert(core, new_record);
		SaleInfo::<T>::put(&sale);
		Ok(())
	}

	pub(crate) fn do_purchase(who: T::AccountId, price_limit: BalanceOf<T>) -> DispatchResult {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
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
		region_id.part = antipivot;
		Regions::<T>::insert(&region_id, &region);

		Self::deposit_event(Event::Interlaced { region_id, pivot });

		Ok(())
	}

	pub(crate) fn utilize(
		mut region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<Option<(RegionId, RegionRecordOf<T>)>, Error<T>> {
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

		if let Some(check_owner) = maybe_check_owner {
			ensure!(check_owner == region.owner, Error::<T>::NotOwner);
		}

		let last_commit_timeslice = status.last_timeslice + config.advance_notice;
		if region_id.begin <= last_commit_timeslice {
			region_id.begin = last_commit_timeslice + 1;
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
}