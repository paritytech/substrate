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
	traits::{
		fungible::Balanced,
		tokens::{Fortitude::Polite, Precision::Exact, Preservation::Expendable},
		OnUnbalanced,
	},
};
use frame_system::pallet_prelude::BlockNumberFor;
use sp_arithmetic::{
	traits::{SaturatedConversion, Saturating},
	FixedPointNumber, FixedU64,
};
use sp_runtime::traits::AccountIdConversion;

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

	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account_truncating()
	}

	pub fn sale_price(sale: &SaleInfoRecordOf<T>, now: BlockNumberFor<T>) -> BalanceOf<T> {
		let num = now.saturating_sub(sale.sale_start).min(sale.leadin_length).saturated_into();
		let through = FixedU64::from_rational(num, sale.leadin_length.saturated_into());
		T::PriceAdapter::leadin_factor_at(through).saturating_mul_int(sale.price)
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
		let id = RegionId { begin, core, mask: CoreMask::complete() };
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
				p.retain(|i| (i.mask & region_id.mask).is_void())
			});
		}
		if finality == Finality::Provisional {
			Regions::<T>::insert(&region_id, &region);
		}

		Ok(Some((region_id, region)))
	}
}
