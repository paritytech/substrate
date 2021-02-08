// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use sp_runtime::traits::Bounded;
use frame_system::{EventRecord, RawOrigin};
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use frame_support::traits::OnInitialize;

use crate::Module as Bounties;
use pallet_treasury::Module as Treasury;

const SEED: u32 = 0;

// Create bounties that are approved for use in `on_initialize`.
fn create_approved_bounties<T: Config>(n: u32) -> Result<(), &'static str> {
	for i in 0 .. n {
		let (caller, _curator, _fee, value, reason) = setup_bounty::<T>(i, MAX_BYTES);
		Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Bounties::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
	}
	ensure!(BountyApprovals::get().len() == n as usize, "Not all bounty approved");
	Ok(())
}

// Create the pre-requisite information needed to create a treasury `propose_bounty`.
fn setup_bounty<T: Config>(u: u32, d: u32) -> (
	T::AccountId,
	T::AccountId,
	BalanceOf<T>,
	BalanceOf<T>,
	Vec<u8>,
) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T> = T::BountyValueMinimum::get().saturating_mul(100u32.into());
	let fee = value / 2u32.into();
	let deposit = T::BountyDepositBase::get() + T::DataDepositPerByte::get() * MAX_BYTES.into();
	let _ = T::Currency::make_free_balance_be(&caller, deposit);
	let curator = account("curator", u, SEED);
	let _ = T::Currency::make_free_balance_be(&curator, fee / 2u32.into());
	let reason = vec![0; d as usize];
	(caller, curator, fee, value, reason)
}

fn create_bounty<T: Config>() -> Result<(
	<T::Lookup as StaticLookup>::Source,
	BountyIndex,
), &'static str> {
	let (caller, curator, fee, value, reason) = setup_bounty::<T>(0, MAX_BYTES);
	let curator_lookup = T::Lookup::unlookup(curator.clone());
	Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
	let bounty_id = BountyCount::get() - 1;
	Bounties::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
	Treasury::<T>::on_initialize(T::BlockNumber::zero());
	Bounties::<T>::propose_curator(RawOrigin::Root.into(), bounty_id, curator_lookup.clone(), fee)?;
	Bounties::<T>::accept_curator(RawOrigin::Signed(curator).into(), bounty_id)?;
	Ok((curator_lookup, bounty_id))
}

fn setup_pot_account<T: Config>() {
	let pot_account = Bounties::<T>::account_id();
	let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000u32.into());
	let _ = T::Currency::make_free_balance_be(&pot_account, value);
}

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

#[derive(Clone)]
struct BmSubbountyCfg<T: Config> {
	/// Bounty ID.
	bounty_id: BountyIndex,
	/// SubBounty ID.
	subbounty_id: BountyIndex,
	/// The account proposing it.
	caller: T::AccountId,
	/// The master curator account.
	curator: T::AccountId,
	/// The subcurator account.
	subcurator: T::AccountId,
	/// The (total) amount that should be paid if the bounty is rewarded.
	value: BalanceOf<T>,
	/// The curator fee. Included in value.
	fee: BalanceOf<T>,
	/// The (total) amount that should be paid if the subbounty is rewarded.
	subbounty_value: BalanceOf<T>,
	/// The curator fee. Included in value.
	subbounty_fee: BalanceOf<T>,
	/// Bounty description.
	reason: Vec<u8>,
}

fn setup_subbounty<T: Config>(u: u32, d: u32) -> BmSubbountyCfg::<T> {
	let (caller, curator, fee, value, reason) = setup_bounty::<T>(u, d);
	let subcurator = account("subcurator", u, SEED);
	let _ = T::Currency::make_free_balance_be(&subcurator, fee / 2u32.into());
	// let subbounty_value = (value - fee) / 4u32.into();
	let subbounty_value = 2u32.into();
	let subbounty_fee = subbounty_value / 2u32.into();

	BmSubbountyCfg::<T> {
		bounty_id: 0,
		subbounty_id: 0,
		caller: caller,
		curator: curator,
		subcurator: subcurator,
		value: value,
		fee: fee,
		subbounty_value: subbounty_value,
		subbounty_fee: subbounty_fee,
		reason: reason,
	}
}

fn create_subbounty_bounty<T: Config>() -> Result<
	BmSubbountyCfg::<T>,
	&'static str
> {
	let mut bm_setup = setup_subbounty::<T>(0, MAX_BYTES);
	let curator_lookup = T::Lookup::unlookup(bm_setup.curator.clone());
	Bounties::<T>::propose_bounty(
		RawOrigin::Signed(bm_setup.caller.clone()).into(),
		bm_setup.value,
		bm_setup.reason.clone()
	)?;
	bm_setup.bounty_id = BountyCount::get() - 1;
	Bounties::<T>::approve_bounty(
		RawOrigin::Root.into(),
		bm_setup.bounty_id,
	)?;
	Treasury::<T>::on_initialize(T::BlockNumber::zero());
	Bounties::<T>::propose_curator(
		RawOrigin::Root.into(),
		bm_setup.bounty_id,
		curator_lookup.clone(),
		bm_setup.fee,
	)?;
	Bounties::<T>::accept_curator(
		RawOrigin::Signed(bm_setup.curator.clone()).into(),
		bm_setup.bounty_id,
	)?;

	Ok(bm_setup)
}

fn create_subbounty<T: Config>() -> Result<
	BmSubbountyCfg::<T>,
	&'static str
> {
	let mut bm_setup = create_subbounty_bounty::<T>()?;

	let subcurator_lookup = T::Lookup::unlookup(
		bm_setup.subcurator.clone()
	);

	Bounties::<T>::add_subbounty(
		RawOrigin::Signed(bm_setup.curator.clone()).into(),
		bm_setup.bounty_id,
		bm_setup.subbounty_value,
		bm_setup.reason.clone(),
	)?;

	bm_setup.subbounty_id = BountyCount::get() - 1;

	Bounties::<T>::propose_subcurator(
		RawOrigin::Signed(bm_setup.curator.clone()).into(),
		bm_setup.bounty_id,
		bm_setup.subbounty_id,
		subcurator_lookup.clone(),
		bm_setup.subbounty_fee,
	)?;

	Bounties::<T>::accept_subcurator(
		RawOrigin::Signed(bm_setup.subcurator.clone()).into(),
		bm_setup.bounty_id,
		bm_setup.subbounty_id,
	)?;

	Ok(bm_setup)
}

const MAX_BYTES: u32 = 16384;

benchmarks! {
	propose_bounty {
		let d in 0 .. MAX_BYTES;

		let (caller, curator, fee, value, description) = setup_bounty::<T>(0, d);
	}: _(RawOrigin::Signed(caller), value, description)

	approve_bounty {
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(0, MAX_BYTES);
		Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
	}: _(RawOrigin::Root, bounty_id)

	propose_curator {
		setup_pot_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(0, MAX_BYTES);
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Bounties::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());
	}: _(RawOrigin::Root, bounty_id, curator_lookup, fee)

	// Worst case when curator is inactive and any sender unassigns the curator.
	unassign_curator {
		setup_pot_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());
		let bounty_id = BountyCount::get() - 1;
		frame_system::Module::<T>::set_block_number(T::BountyUpdatePeriod::get() + 1u32.into());
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), bounty_id)

	accept_curator {
		setup_pot_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(0, MAX_BYTES);
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Bounties::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());
		Bounties::<T>::propose_curator(RawOrigin::Root.into(), bounty_id, curator_lookup, fee)?;
	}: _(RawOrigin::Signed(curator), bounty_id)

	award_bounty {
		setup_pot_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;
		let beneficiary = T::Lookup::unlookup(account("beneficiary", 0, SEED));
	}: _(RawOrigin::Signed(curator), bounty_id, beneficiary)

	claim_bounty {
		setup_pot_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;

		let beneficiary_account: T::AccountId = account("beneficiary", 0, SEED);
		let beneficiary = T::Lookup::unlookup(beneficiary_account.clone());
		Bounties::<T>::award_bounty(RawOrigin::Signed(curator.clone()).into(), bounty_id, beneficiary)?;

		frame_system::Module::<T>::set_block_number(T::BountyDepositPayoutDelay::get());
		ensure!(T::Currency::free_balance(&beneficiary_account).is_zero(), "Beneficiary already has balance");

	}: _(RawOrigin::Signed(curator), bounty_id)
	verify {
		ensure!(!T::Currency::free_balance(&beneficiary_account).is_zero(), "Beneficiary didn't get paid");
	}

	close_bounty_proposed {
		setup_pot_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(0, 0);
		Bounties::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
	}: close_bounty(RawOrigin::Root, bounty_id)

	close_bounty_active {
		setup_pot_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());
		let bounty_id = BountyCount::get() - 1;
	}: close_bounty(RawOrigin::Root, bounty_id)
	verify {
		assert_last_event::<T>(RawEvent::BountyCanceled(bounty_id).into())
	}

	extend_bounty_expiry {
		setup_pot_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;
	}: _(RawOrigin::Signed(curator), bounty_id, Vec::new())
	verify {
		assert_last_event::<T>(RawEvent::BountyExtended(bounty_id).into())
	}

	spend_funds {
		let b in 1 .. 100;
		setup_pot_account::<T>();
		create_approved_bounties::<T>(b)?;

		let mut budget_remaining = BalanceOf::<T>::max_value();
		let mut imbalance = PositiveImbalanceOf::<T>::zero();
		let mut total_weight = Weight::zero();
		let mut missed_any = false;
	}: {
		<Bounties<T> as pallet_treasury::SpendFunds<T>>::spend_funds(
			&mut budget_remaining,
			&mut imbalance,
			&mut total_weight,
			&mut missed_any,
		);
	}
	verify {
		ensure!(budget_remaining < BalanceOf::<T>::max_value(), "Budget not used");
		ensure!(missed_any == false, "Missed some");
		assert_last_event::<T>(RawEvent::BountyBecameActive(b - 1).into())
	}

	add_subbounty {
		setup_pot_account::<T>();
		let bm_setup = create_subbounty_bounty::<T>()?;
	}: _(RawOrigin::Signed(bm_setup.curator), bm_setup.bounty_id, bm_setup.subbounty_value, bm_setup.reason)

	propose_subcurator {
		setup_pot_account::<T>();
		let mut bm_setup = create_subbounty_bounty::<T>()?;

		let subcurator_lookup = T::Lookup::unlookup(bm_setup.subcurator.clone());
		Bounties::<T>::add_subbounty(
			RawOrigin::Signed(bm_setup.curator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_value,
			bm_setup.reason.clone(),
		)?;
		bm_setup.subbounty_id = BountyCount::get() - 1;
	}: _(RawOrigin::Signed(bm_setup.curator), bm_setup.bounty_id, bm_setup.subbounty_id, subcurator_lookup, bm_setup.subbounty_fee)

	unassign_subcurator {
		setup_pot_account::<T>();
		let bm_setup = create_subbounty::<T>()?;
		Bounties::<T>::on_initialize(T::BlockNumber::zero());
		frame_system::Module::<T>::set_block_number(T::BountyUpdatePeriod::get() + 1u32.into());
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), bm_setup.bounty_id, bm_setup.subbounty_id)

	accept_subcurator {
		setup_pot_account::<T>();
		let mut bm_setup = create_subbounty_bounty::<T>()?;

		let subcurator_lookup = T::Lookup::unlookup(bm_setup.subcurator.clone());

		Bounties::<T>::add_subbounty(
			RawOrigin::Signed(bm_setup.curator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_value,
			bm_setup.reason.clone(),
		)?;

		bm_setup.subbounty_id = BountyCount::get() - 1;

		Bounties::<T>::propose_subcurator(
			RawOrigin::Signed(bm_setup.curator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_id,
			subcurator_lookup,
			bm_setup.subbounty_fee,
		)?;
	}: _(RawOrigin::Signed(bm_setup.subcurator), bm_setup.bounty_id, bm_setup.subbounty_id)

	award_subbounty {
		setup_pot_account::<T>();
		let bm_setup = create_subbounty::<T>()?;
		let beneficiary = T::Lookup::unlookup(account("beneficiary", 0, SEED));
	}: _(RawOrigin::Signed(bm_setup.subcurator), bm_setup.bounty_id, bm_setup.subbounty_id, beneficiary)

	claim_subbounty {
		setup_pot_account::<T>();
		let bm_setup = create_subbounty::<T>()?;

		let beneficiary_account: T::AccountId = account("beneficiary", 0, SEED);
		let beneficiary = T::Lookup::unlookup(beneficiary_account.clone());

		Bounties::<T>::award_subbounty(
			RawOrigin::Signed(bm_setup.subcurator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_id,
			beneficiary,
		)?;

		frame_system::Module::<T>::set_block_number(T::BountyDepositPayoutDelay::get());
		ensure!(
			T::Currency::free_balance(&beneficiary_account).is_zero(),
			"Beneficiary already has balance"
		);
	}: _(RawOrigin::Signed(bm_setup.curator), bm_setup.bounty_id, bm_setup.subbounty_id)
	verify {
		ensure!(
			!T::Currency::free_balance(&beneficiary_account).is_zero(),
			"Beneficiary didn't get paid"
		);
	}

	close_subbounty_proposed {
		setup_pot_account::<T>();
		let mut bm_setup = create_subbounty_bounty::<T>()?;
		let subcurator_lookup = T::Lookup::unlookup(bm_setup.subcurator.clone());
		Bounties::<T>::add_subbounty(
			RawOrigin::Signed(bm_setup.curator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_value,
			bm_setup.reason.clone(),
		)?;
		bm_setup.subbounty_id = BountyCount::get() - 1;
		Bounties::<T>::propose_subcurator(
			RawOrigin::Signed(bm_setup.curator.clone()).into(),
			bm_setup.bounty_id,
			bm_setup.subbounty_id,
			subcurator_lookup,
			bm_setup.subbounty_fee,
		)?;
	}: close_subbounty(RawOrigin::Signed(bm_setup.curator), bm_setup.bounty_id, bm_setup.subbounty_id)

	close_subbounty_active {
		setup_pot_account::<T>();
		let bm_setup = create_subbounty::<T>()?;

		Bounties::<T>::on_initialize(T::BlockNumber::zero());

	}: close_subbounty(RawOrigin::Root, bm_setup.bounty_id, bm_setup.subbounty_id)
	verify {
		assert_last_event::<T>(RawEvent::SubBountyCanceled(bm_setup.bounty_id, bm_setup.subbounty_id).into())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_propose_bounty::<Test>());
			assert_ok!(test_benchmark_approve_bounty::<Test>());
			assert_ok!(test_benchmark_propose_curator::<Test>());
			assert_ok!(test_benchmark_unassign_curator::<Test>());
			assert_ok!(test_benchmark_accept_curator::<Test>());
			assert_ok!(test_benchmark_award_bounty::<Test>());
			assert_ok!(test_benchmark_claim_bounty::<Test>());
			assert_ok!(test_benchmark_close_bounty_proposed::<Test>());
			assert_ok!(test_benchmark_close_bounty_active::<Test>());
			assert_ok!(test_benchmark_extend_bounty_expiry::<Test>());
			assert_ok!(test_benchmark_spend_funds::<Test>());
			assert_ok!(test_benchmark_add_subbounty::<Test>());
			assert_ok!(test_benchmark_propose_subcurator::<Test>());
			assert_ok!(test_benchmark_accept_subcurator::<Test>());
			assert_ok!(test_benchmark_unassign_subcurator::<Test>());
			assert_ok!(test_benchmark_award_subbounty::<Test>());
			assert_ok!(test_benchmark_claim_subbounty::<Test>());
			assert_ok!(test_benchmark_close_subbounty_proposed::<Test>());
			assert_ok!(test_benchmark_close_subbounty_active::<Test>());
		});
	}
}
