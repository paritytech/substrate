use super::*;
use frame_support::{
	pallet_prelude::{DispatchResult, *},
	traits::{
		fungible::Balanced,
		tokens::{Fortitude::Polite, Precision::Exact, Preservation::Expendable},
		OnUnbalanced,
	},
	weights::WeightMeter,
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

	pub fn next_timeslice_to_commit(
		config: &ConfigRecordOf<T>,
		status: &StatusRecord,
	) -> Option<Timeslice> {
		if status.last_committed_timeslice < Self::latest_timeslice_ready_to_commit(config) {
			Some(status.last_committed_timeslice + 1)
		} else {
			None
		}
	}

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

		if Self::process_core_count() {
			meter.consume(T::WeightInfo::process_core_count());
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
					meter.consume(T::WeightInfo::rotate_sale());
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
			let rc_block = T::TimeslicePeriod::get() * current_timeslice.into();
			T::Coretime::request_revenue_info_at(rc_block);
			meter.consume(T::WeightInfo::request_revenue_info_at());
			status.last_timeslice.saturating_inc();
		}

		Status::<T>::put(&status);

		meter.consumed
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
		let mut old_pooled: SignedPartCount = 0;
		for i in old_sale.cores_sold..old_sale.cores_offered {
			old_pooled.saturating_accrue(80);
			Workplan::<T>::insert((old_sale.region_begin, old_sale.first_core + i), &just_pool);
		}
		InstaPoolIo::<T>::mutate(old_sale.region_begin, |r| r.system.saturating_accrue(old_pooled));
		InstaPoolIo::<T>::mutate(old_sale.region_end, |r| r.system.saturating_reduce(old_pooled));

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
		InstaPoolIo::<T>::mutate(region_begin, |r| r.system.saturating_accrue(total_pooled));
		InstaPoolIo::<T>::mutate(region_end, |r| r.system.saturating_reduce(total_pooled));

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
		if let Some(core_count) = T::Coretime::check_notify_core_count() {
			Status::<T>::mutate_extant(|c| c.core_count = core_count);
			Self::deposit_event(Event::<T>::CoreCountChanged { core_count });
			return true
		}
		false
	}

	fn process_revenue() -> bool {
		let (until, amount) = match T::Coretime::check_notify_revenue_info() {
			Some(x) => x,
			None => return false,
		};
		let when: Timeslice = (until / T::TimeslicePeriod::get()).saturated_into();
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
		let system_payout = revenue.saturating_mul(r.system_contributions.into()) /
			total_contrib.into();
		let _ = Self::charge(&Self::account_id(), system_payout);
		revenue.saturating_reduce(system_payout);

		if !revenue.is_zero() && r.private_contributions > 0 {
			r.maybe_payout = Some(revenue);
			InstaPoolHistory::<T>::insert(when, &r);
			Self::deposit_event(Event::<T>::ClaimsReady {
				when,
				system_payout,
				private_payout: revenue,
				private_contributions: r.private_contributions,
			});
		} else {
			InstaPoolHistory::<T>::remove(when);
			Self::deposit_event(Event::<T>::HistoryDropped { when, revenue });
		}
		true
	}

	pub fn sale_price(sale: &SaleInfoRecordOf<T>, now: T::BlockNumber) -> BalanceOf<T> {
		lerp(now, sale.sale_start, sale.leadin_length, sale.start_price, sale.reserve_price)
			.unwrap_or(sale.start_price)
	}

	fn process_pool(timeslice: Timeslice, status: &mut StatusRecord) {
		let pool_io = InstaPoolIo::<T>::take(timeslice);
		status.private_pool_size = (status.private_pool_size as SignedPartCount)
			.saturating_add(pool_io.private) as PartCount;
		status.system_pool_size = (status.system_pool_size as SignedPartCount)
			.saturating_add(pool_io.system) as PartCount;
		let record = InstaPoolHistoryRecord {
			private_contributions: status.private_pool_size,
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
		T::Coretime::assign_core(core, rc_begin, assignment.clone(), None);
		Self::deposit_event(Event::<T>::CoreAssigned { core, when: rc_begin, assignment });
	}

	pub(crate) fn charge(who: &T::AccountId, amount: BalanceOf<T>) -> DispatchResult {
		let credit = T::Currency::withdraw(&who, amount, Exact, Expendable, Polite)?;
		T::OnRevenue::on_unbalanced(credit);
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
				Self::deposit_event(Event::RegionDropped { region_id, duration });
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
