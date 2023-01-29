// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Treasury pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::{Pallet as Treasury, *};

use frame_benchmarking::v1::{account, benchmarks_instance_pallet, BenchmarkError};
use frame_support::{
	dispatch::UnfilteredDispatchable,
	ensure,
	traits::{EnsureOrigin, OnInitialize},
};
use frame_system::RawOrigin;

const SEED: u32 = 0;

// Create the pre-requisite information needed to create a treasury `propose_spend`.
fn setup_proposal<T: Config<I>, I: 'static>(
	u: u32,
) -> (T::AccountId, BalanceOf<T, I>, AccountIdLookupOf<T>) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T, I> = T::ProposalBondMinimum::get().saturating_mul(100u32.into());
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let beneficiary = account("beneficiary", u, SEED);
	let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	(caller, value, beneficiary_lookup)
}

// Create proposals that are approved for use in `on_initialize`.
fn create_approved_proposals<T: Config<I>, I: 'static>(n: u32) -> Result<(), &'static str> {
	for i in 0..n {
		let (caller, value, lookup) = setup_proposal::<T, I>(i);
		Treasury::<T, I>::propose_spend(RawOrigin::Signed(caller).into(), value, lookup)?;
		let proposal_id = <ProposalCount<T, I>>::get() - 1;
		Treasury::<T, I>::approve_proposal(RawOrigin::Root.into(), proposal_id)?;
	}
	ensure!(<Approvals<T, I>>::get().len() == n as usize, "Not all approved");
	Ok(())
}

fn setup_pot_account<T: Config<I>, I: 'static>() {
	let pot_account = Treasury::<T, I>::account_id();
	let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000u32.into());
	let _ = T::Currency::make_free_balance_be(&pot_account, value);
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

benchmarks_instance_pallet! {
	// This benchmark is short-circuited if `SpendOrigin` cannot provide
	// a successful origin, in which case `spend` is un-callable and can use weight=0.
	spend {
		let (_, value, beneficiary_lookup) = setup_proposal::<T, _>(SEED);
		let origin = T::SpendOrigin::try_successful_origin();
		let beneficiary = T::Lookup::lookup(beneficiary_lookup.clone()).unwrap();
		let call = Call::<T, I>::spend { amount: value, beneficiary: beneficiary_lookup };
	}: {
		if let Ok(origin) = origin.clone() {
			call.dispatch_bypass_filter(origin)?;
		}
	}
	verify {
		if origin.is_ok() {
			assert_last_event::<T, I>(Event::SpendApproved { proposal_index: 0, amount: value, beneficiary }.into())
		}
	}

	propose_spend {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(SEED);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)

	reject_proposal {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(SEED);
		Treasury::<T, _>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = Treasury::<T, _>::proposal_count() - 1;
		let reject_origin =
			T::RejectOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: _<T::RuntimeOrigin>(reject_origin, proposal_id)

	approve_proposal {
		let p in 0 .. T::MaxApprovals::get() - 1;
		create_approved_proposals::<T, _>(p)?;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(SEED);
		Treasury::<T, _>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = Treasury::<T, _>::proposal_count() - 1;
		let approve_origin =
			T::ApproveOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: _<T::RuntimeOrigin>(approve_origin, proposal_id)

	remove_approval {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(SEED);
		Treasury::<T, _>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = Treasury::<T, _>::proposal_count() - 1;
		Treasury::<T, I>::approve_proposal(RawOrigin::Root.into(), proposal_id)?;
		let reject_origin =
			T::RejectOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
	}: _<T::RuntimeOrigin>(reject_origin, proposal_id)

	on_initialize_proposals {
		let p in 0 .. T::MaxApprovals::get();
		setup_pot_account::<T, _>();
		create_approved_proposals::<T, _>(p)?;
	}: {
		Treasury::<T, _>::on_initialize(T::BlockNumber::zero());
	}

	impl_benchmark_test_suite!(Treasury, crate::tests::new_test_ext(), crate::tests::Test);
}
