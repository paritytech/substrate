use super::*;
use frame_support::{
	pallet_prelude::{DispatchResult, *},
	traits::{
		fungible::Balanced,
		tokens::{Fortitude::Polite, Precision::Exact, Preservation::Expendable},
		OnUnbalanced, Defensive,
	},
};
use sp_arithmetic::{
	traits::{SaturatedConversion, Saturating, Zero},
	FixedPointNumber,
};
use sp_runtime::traits::{AccountIdConversion, ConvertBack};
use CompletionStatus::Complete;

impl<T: Config> Pallet<T> {
	pub fn current_timeslice() -> Timeslice {
		let latest = T::Coretime::latest();
		let timeslice_period = T::TimeslicePeriod::get();
		(latest / timeslice_period).saturated_into()
	}

	pub fn latest_timeslice_ready_to_commit(config: &ConfigRecordOf<T>) -> Timeslice {
		let latest = T::Coretime::latest();
		let advanced = latest.saturating_add(config.advance_notice);
		let timeslice_period = T::TimeslicePeriod::get();
		(advanced / timeslice_period).saturated_into()
	}

	pub fn next_timeslice_to_commit(config: &ConfigRecordOf<T>, status: &StatusRecord) -> Option<Timeslice> {
		if status.last_committed_timeslice < Self::latest_timeslice_ready_to_commit(config) {
			Some(status.last_committed_timeslice + 1)
		} else {
			None
		}
	}

	/// Attempt to tick things along. Will only do anything if the `Status.last_timeslice` is
	/// less than `Self::current_timeslice`.
	pub(crate) fn do_tick() -> DispatchResult {
		let mut status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let config = Configuration::<T>::get().ok_or(Error::<T>::Uninitialized)?;

		Self::process_core_count();
		let _ = Self::process_revenue().defensive();

		if let Some(commit_timeslice) = Self::next_timeslice_to_commit(&config, &status) {
			status.last_committed_timeslice = commit_timeslice;
			if let Some(sale) = SaleInfo::<T>::get() {
				if commit_timeslice >= sale.region_begin {
					// Sale can be rotated.
					Self::rotate_sale(sale, &config, &status);
				}
			}

			Self::process_pool(commit_timeslice, &mut status);

			let timeslice_period = T::TimeslicePeriod::get();
			let rc_begin = RelayBlockNumberOf::<T>::from(commit_timeslice) * timeslice_period;
			for core in 0..status.core_count {
				Self::process_core_schedule(commit_timeslice, rc_begin, core);
			}
		}

		let current_timeslice = Self::current_timeslice();
		if status.last_timeslice < current_timeslice {
			let rc_block = T::TimeslicePeriod::get() * current_timeslice.into();
			T::Coretime::request_revenue_info_at(rc_block);
			status.last_timeslice.saturating_inc();
		}

		Status::<T>::put(&status);

		Ok(())
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
			ScheduleItem { assignment: CoreAssignment::Pool, part: CoreMask::complete() };
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
			let old_price = old_sale.sellout_price.unwrap_or(old_sale.reserve_price);
			if sold <= offered && offered > 0 {
				T::PriceAdapter::adapt_price(sold, ideal, offered).saturating_mul_int(old_price)
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
			let parts: u32 = schedule
				.iter()
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
		// Can morph to a renewable as long as it's >=begin and <end.
		leases.retain(|&LeaseRecordItem { until, task }| {
			let part = CoreMask::complete();
			let assignment = CoreAssignment::Task(task);
			let schedule = BoundedVec::truncate_from(vec![ScheduleItem { part, assignment }]);
			Workplan::<T>::insert((region_begin, first_core), &schedule);
			let expiring = until >= region_begin && until < region_end;
			if expiring {
				// last time for this one - make it renewable.
				let record = AllowedRenewalRecord {
					begin: region_end,
					price: reserve_price,
					completion: Complete(schedule),
				};
				AllowedRenewals::<T>::insert(first_core, &record);
				Self::deposit_event(Event::Renewable {
					core: first_core,
					price: reserve_price,
					begin: region_end,
					workload: record.completion.drain_complete().unwrap_or_default(),
				});
			}
			first_core.saturating_inc();
			!expiring
		});
		Leases::<T>::put(&leases);

		let max_possible_sales = status.core_count.saturating_sub(first_core);
		let limit_cores_offered = config.limit_cores_offered.unwrap_or(CoreIndex::max_value());
		let cores_offered = limit_cores_offered.min(max_possible_sales);
		// Update SaleInfo
		let new_sale = SaleInfoRecord {
			sale_start: now.saturating_add(config.interlude_length),
			leadin_length: config.leadin_length,
			start_price,
			reserve_price,
			sellout_price: None,
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

	fn process_core_count() -> bool {
		if let Some(new_count) = T::Coretime::check_notify_core_count() {
			Status::<T>::mutate_extant(|c| c.core_count = new_count);
			return true
		}
		false
	}

	fn process_revenue() -> Result<bool, DispatchError> {
		if let Some((until, amount)) = T::Coretime::check_notify_revenue_info() {
			let timeslice: Timeslice = (until / T::TimeslicePeriod::get()).saturated_into();
			let mut amount = T::ConvertBalance::convert_back(amount);
			if amount.is_zero() {
				InstaPoolHistory::<T>::remove(timeslice);
				return Ok(true)
			}
			let mut pool_record = InstaPoolHistory::<T>::get(timeslice).unwrap_or_default();
			ensure!(pool_record.maybe_payout.is_none(), Error::<T>::RevenueAlreadyKnown);
			ensure!(
				pool_record.total_contributions >= pool_record.system_contributions,
				Error::<T>::InvalidContributions,
			);
			ensure!(pool_record.total_contributions > 0, Error::<T>::InvalidContributions);

			// Payout system InstaPool Cores.
			let system_payout = amount.saturating_mul(pool_record.system_contributions.into()) /
				pool_record.total_contributions.into();
			let _ = Self::charge(&Self::account_id(), system_payout);
			pool_record
				.total_contributions
				.saturating_reduce(pool_record.system_contributions);
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

	pub fn sale_price(sale: &SaleInfoRecordOf<T>, now: T::BlockNumber) -> BalanceOf<T> {
		lerp(now, sale.sale_start, sale.leadin_length, sale.start_price, sale.reserve_price)
			.unwrap_or(sale.start_price)
	}

	fn process_pool(timeslice: Timeslice, status: &mut StatusRecord) {
		let pool_io = InstaPoolIo::<T>::take(timeslice);
		status.pool_size = (status.pool_size as i32).saturating_add(pool_io.total) as u32;
		status.system_pool_size =
			(status.system_pool_size as i32).saturating_add(pool_io.system) as u32;
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
		let parts_used = workplan.iter().map(|i| i.part).fold(CoreMask::void(), |a, i| a | i);
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
		T::Coretime::assign_core(core, rc_begin, assignment, None);
	}

	pub(crate) fn charge(who: &T::AccountId, amount: BalanceOf<T>) -> DispatchResult {
		T::OnRevenue::on_unbalanced(T::Currency::withdraw(
			&who, amount, Exact, Expendable, Polite,
		)?);
		Ok(())
	}

	pub(crate) fn issue(
		core: CoreIndex,
		begin: Timeslice,
		end: Timeslice,
		owner: T::AccountId,
		paid: Option<BalanceOf<T>>,
	) -> RegionId {
		let id = RegionId { begin, core, part: CoreMask::complete() };
		let record = RegionRecord { end, owner, paid };
		Regions::<T>::insert(&id, &record);
		id
	}

	pub(crate) fn utilize(
		mut region_id: RegionId,
		maybe_check_owner: Option<T::AccountId>,
		finality: Finality,
	) -> Result<Option<(RegionId, RegionRecordOf<T>)>, Error<T>> {
		let status = Status::<T>::get().ok_or(Error::<T>::Uninitialized)?;
		let region = Regions::<T>::get(&region_id).ok_or(Error::<T>::UnknownRegion)?;

		if let Some(check_owner) = maybe_check_owner {
			ensure!(check_owner == region.owner, Error::<T>::NotOwner);
		}

		Regions::<T>::remove(&region_id);

		let last_committed_timeslice = status.last_committed_timeslice;
		if region_id.begin <= last_committed_timeslice {
			region_id.begin = last_committed_timeslice + 1;
			if region_id.begin >= region.end {
				let duration = region.end.saturating_sub(region_id.begin);
				Self::deposit_event(Event::Dropped { region_id, duration });
				return Ok(None)
			}
		} else {
			Workplan::<T>::mutate_extant((region_id.begin, region_id.core), |p| {
				p.retain(|i| (i.part & region_id.part).is_void())
			});
		}
		if finality == Finality::Provisional {
			Regions::<T>::insert(&region_id, &region);
		}

		Ok(Some((region_id, region)))
	}
}
