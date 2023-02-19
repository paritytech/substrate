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

//! bounties pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelisted_caller, BenchmarkError,
};
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded;

use crate::Pallet as Bounties;
use pallet_treasury::Pallet as Treasury;

const SEED: u32 = 0;

// Create bounties that are approved for use in `on_initialize`.
fn create_approved_bounties<T: Config<I>, I: 'static>(n: u32) -> Result<(), BenchmarkError> {
	for i in 0..n {
		let (caller, _curator, _fee, value, reason) =
			setup_bounty::<T, I>(i, T::MaximumReasonLength::get());
		Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin =
			T::SpendOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		Bounties::<T, I>::approve_bounty(approve_origin, bounty_id)?;
	}
	ensure!(BountyApprovals::<T, I>::get().len() == n as usize, "Not all bounty approved");
	Ok(())
}

// Create the pre-requisite information needed to create a treasury `propose_bounty`.
fn setup_bounty<T: Config<I>, I: 'static>(
	u: u32,
	d: u32,
) -> (T::AccountId, T::AccountId, BalanceOf<T, I>, BalanceOf<T, I>, Vec<u8>) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T, I> = T::BountyValueMinimum::get().saturating_mul(100u32.into());
	let fee = value / 2u32.into();
	let deposit = T::BountyDepositBase::get() +
		T::DataDepositPerByte::get() * T::MaximumReasonLength::get().into();
	let _ = T::Currency::make_free_balance_be(&caller, deposit);
	let curator = account("curator", u, SEED);
	let _ = T::Currency::make_free_balance_be(&curator, fee / 2u32.into());
	let reason = vec![0; d as usize];
	(caller, curator, fee, value, reason)
}

fn create_bounty<T: Config<I>, I: 'static>(
) -> Result<(AccountIdLookupOf<T>, BountyIndex), BenchmarkError> {
	let (caller, curator, fee, value, reason) =
		setup_bounty::<T, I>(0, T::MaximumReasonLength::get());
	let curator_lookup = T::Lookup::unlookup(curator.clone());
	Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
	let bounty_id = BountyCount::<T, I>::get() - 1;
	let approve_origin =
		T::SpendOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	Bounties::<T, I>::approve_bounty(approve_origin.clone(), bounty_id)?;
	Treasury::<T, I>::on_initialize(T::BlockNumber::zero());
	Bounties::<T, I>::propose_curator(approve_origin, bounty_id, curator_lookup.clone(), fee)?;
	Bounties::<T, I>::accept_curator(RawOrigin::Signed(curator).into(), bounty_id)?;
	Ok((curator_lookup, bounty_id))
}

fn setup_pot_account<T: Config<I>, I: 'static>() {
	let pot_account = Bounties::<T, I>::account_id();
	let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000u32.into());
	let _ = T::Currency::make_free_balance_be(&pot_account, value);
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

benchmarks_instance_pallet! {
	propose_bounty {
		let d in 0 .. T::MaximumReasonLength::get();

		let (caller, curator, fee, value, description) = setup_bounty::<T, I>(0, d);
	}: _(RawOrigin::Signed(caller), value, description)

	approve_bounty {
		let (caller, curator, fee, value, reason) = setup_bounty::<T, I>(0, T::MaximumReasonLength::get());
		Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin = T::SpendOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: _<T::RuntimeOrigin>(approve_origin, bounty_id)

	propose_curator {
		setup_pot_account::<T, I>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T, I>(0, T::MaximumReasonLength::get());
		let curator_lookup = T::Lookup::unlookup(curator);
		Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin = T::SpendOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		Bounties::<T, I>::approve_bounty(approve_origin.clone(), bounty_id)?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());
	}: _<T::RuntimeOrigin>(approve_origin, bounty_id, curator_lookup, fee)

	// Worst case when curator is inactive and any sender unassigns the curator.
	unassign_curator {
		setup_pot_account::<T, I>();
		let (curator_lookup, bounty_id) = create_bounty::<T, I>()?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());
		let bounty_id = BountyCount::<T, I>::get() - 1;
		frame_system::Pallet::<T>::set_block_number(T::BountyUpdatePeriod::get() + 2u32.into());
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), bounty_id)

	accept_curator {
		setup_pot_account::<T, I>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T, I>(0, T::MaximumReasonLength::get());
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin = T::SpendOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		Bounties::<T, I>::approve_bounty(approve_origin.clone(), bounty_id)?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());
		Bounties::<T, I>::propose_curator(approve_origin, bounty_id, curator_lookup, fee)?;
	}: _(RawOrigin::Signed(curator), bounty_id)

	award_bounty {
		setup_pot_account::<T, I>();
		let (curator_lookup, bounty_id) = create_bounty::<T, I>()?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::<T, I>::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup).map_err(<&str>::from)?;

		let beneficiary = T::Lookup::unlookup(account("beneficiary", 0, SEED));
	}: _(RawOrigin::Signed(curator), bounty_id, beneficiary)

	claim_bounty {
		setup_pot_account::<T, I>();
		let (curator_lookup, bounty_id) = create_bounty::<T, I>()?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::<T, I>::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup).map_err(<&str>::from)?;

		let beneficiary_account: T::AccountId = account("beneficiary", 0, SEED);
		let beneficiary = T::Lookup::unlookup(beneficiary_account.clone());
		Bounties::<T, I>::award_bounty(RawOrigin::Signed(curator.clone()).into(), bounty_id, beneficiary)?;

		frame_system::Pallet::<T>::set_block_number(T::BountyDepositPayoutDelay::get() + 1u32.into());
		ensure!(T::Currency::free_balance(&beneficiary_account).is_zero(), "Beneficiary already has balance");

	}: _(RawOrigin::Signed(curator), bounty_id)
	verify {
		ensure!(!T::Currency::free_balance(&beneficiary_account).is_zero(), "Beneficiary didn't get paid");
	}

	close_bounty_proposed {
		setup_pot_account::<T, I>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T, I>(0, 0);
		Bounties::<T, I>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin =
			T::ApproveOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: close_bounty<T::RuntimeOrigin>(approve_origin, bounty_id)

	close_bounty_active {
		setup_pot_account::<T, I>();
		let (curator_lookup, bounty_id) = create_bounty::<T, I>()?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());
		let bounty_id = BountyCount::<T, I>::get() - 1;
		let approve_origin =
			T::ApproveOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: close_bounty<T::RuntimeOrigin>(approve_origin, bounty_id)
	verify {
		assert_last_event::<T, I>(Event::BountyCanceled { index: bounty_id }.into())
	}

	extend_bounty_expiry {
		setup_pot_account::<T, I>();
		let (curator_lookup, bounty_id) = create_bounty::<T, I>()?;
		Treasury::<T, I>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::<T, I>::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup).map_err(<&str>::from)?;
	}: _(RawOrigin::Signed(curator), bounty_id, Vec::new())
	verify {
		assert_last_event::<T, I>(Event::BountyExtended { index: bounty_id }.into())
	}

	spend_funds {
		let b in 0 .. 100;
		setup_pot_account::<T, I>();
		create_approved_bounties::<T, I>(b)?;

		let mut budget_remaining = BalanceOf::<T, I>::max_value();
		let mut imbalance = PositiveImbalanceOf::<T, I>::zero();
		let mut total_weight = Weight::zero();
		let mut missed_any = false;
	}: {
		<Bounties<T, I> as pallet_treasury::SpendFunds<T, I>>::spend_funds(
			&mut budget_remaining,
			&mut imbalance,
			&mut total_weight,
			&mut missed_any,
		);
	}
	verify {
		ensure!(missed_any == false, "Missed some");
		if b > 0 {
			ensure!(budget_remaining < BalanceOf::<T, I>::max_value(), "Budget not used");
			assert_last_event::<T, I>(Event::BountyBecameActive { index: b - 1 }.into())
		} else {
			ensure!(budget_remaining == BalanceOf::<T, I>::max_value(), "Budget used");
		}
	}

	impl_benchmark_test_suite!(Bounties, crate::tests::new_test_ext(), crate::tests::Test)
}
