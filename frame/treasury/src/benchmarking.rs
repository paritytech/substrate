// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::OnInitialize;

use crate::Module as Treasury;

const SEED: u32 = 0;

// Create the pre-requisite information needed to create a treasury `propose_spend`.
fn setup_proposal<T: Trait>(u: u32) -> (
	T::AccountId,
	BalanceOf<T>,
	<T::Lookup as StaticLookup>::Source,
) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T> = T::ProposalBondMinimum::get().saturating_mul(100.into());
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let beneficiary = account("beneficiary", u, SEED);
	let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	(caller, value, beneficiary_lookup)
}

// Create the pre-requisite information needed to create a `report_awesome`.
fn setup_awesome<T: Trait>(length: u32) -> (T::AccountId, Vec<u8>, T::AccountId) {
	let caller = account("caller", 0, SEED);
	let value = T::TipReportDepositBase::get()
		+ T::DataDepositPerByte::get() * length.into()
		+ T::Currency::minimum_balance();
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let reason = vec![0; length as usize];
	let awesome_person = account("awesome", 0, SEED);
	(caller, reason, awesome_person)
}

// Create the pre-requisite information needed to call `tip_new`.
fn setup_tip<T: Trait>(r: u32, t: u32) ->
	Result<(T::AccountId, Vec<u8>, T::AccountId, BalanceOf<T>), &'static str>
{
	let tippers_count = T::Tippers::count();

	for i in 0 .. t {
		let member = account("member", i, SEED);
		T::Tippers::add(&member);
		ensure!(T::Tippers::contains(&member), "failed to add tipper");
	}

	ensure!(T::Tippers::count() == tippers_count + t as usize, "problem creating tippers");
	let caller = account("member", t - 1, SEED);
	let reason = vec![0; r as usize];
	let beneficiary = account("beneficiary", t, SEED);
	let value = T::Currency::minimum_balance().saturating_mul(100.into());
	Ok((caller, reason, beneficiary, value))
}

// Create `t` new tips for the tip proposal with `hash`.
// This function automatically makes the tip able to close.
fn create_tips<T: Trait>(t: u32, hash: T::Hash, value: BalanceOf<T>) -> Result<(), &'static str> {
	for i in 0 .. t {
		let caller = account("member", i, SEED);
		ensure!(T::Tippers::contains(&caller), "caller is not a tipper");
		Treasury::<T>::tip(RawOrigin::Signed(caller).into(), hash, value)?;
	}
	Tips::<T>::mutate(hash, |maybe_tip| {
		if let Some(open_tip) = maybe_tip {
			open_tip.closes = Some(T::BlockNumber::zero());
		}
	});
	Ok(())
}

// Create proposals that are approved for use in `on_initialize`.
fn create_approved_proposals<T: Trait>(n: u32) -> Result<(), &'static str> {
	for _ in 0 .. n {
		let (caller, value, lookup) = setup_proposal::<T>(0);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
		Treasury::<T>::approve_proposal(RawOrigin::Root.into(), proposal_id)?;
	}
	ensure!(Approvals::get().len() == n as usize, "Not all approved");
	Ok(())
}

// Create bounties that are approved for use in `on_initialize`.
fn create_approved_bounties<T: Trait>(n: u32) -> Result<(), &'static str> {
	for _ in 0 .. n {
		let (caller, _curator, _fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Treasury::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
	}
	ensure!(BountyApprovals::get().len() == n as usize, "Not all bounty approved");
	Ok(())
}

// Create the pre-requisite information needed to create a treasury `propose_bounty`.
fn setup_bounty<T: Trait>(d: u32) -> (
	T::AccountId,
	T::AccountId,
	BalanceOf<T>,
	BalanceOf<T>,
	Vec<u8>,
) {
	let caller = account("caller", 0, SEED);
	let value: BalanceOf<T> = T::Currency::minimum_balance().saturating_mul(100.into());
	let fee = T::Currency::minimum_balance().saturating_mul(2.into());
	let deposit = T::BountyDepositBase::get() + T::DataDepositPerByte::get() * MAX_BYTES.into();
	let _ = T::Currency::make_free_balance_be(&caller, deposit);
	let curator = account("curator", 0, SEED);
	let _ = T::Currency::make_free_balance_be(&curator, fee / 2.into());
	let reason = vec![0; d as usize];
	(caller, curator, fee, value, reason)
}

fn create_bounty<T: Trait>() -> Result<(
	<T::Lookup as StaticLookup>::Source,
	BountyIndex,
), &'static str> {
	let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
	let curator_lookup = T::Lookup::unlookup(curator.clone());
	Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
	let bounty_id = BountyCount::get() - 1;
	Treasury::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
	Treasury::<T>::on_initialize(T::BlockNumber::zero());
	Treasury::<T>::assign_curator(RawOrigin::Root.into(), bounty_id, curator_lookup.clone(), fee)?;
	Treasury::<T>::accept_curator(RawOrigin::Signed(curator).into(), bounty_id)?;
	Ok((curator_lookup, bounty_id))
}

fn setup_pod_account<T: Trait>() {
	let pot_account = Treasury::<T>::account_id();
	let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
	let _ = T::Currency::make_free_balance_be(&pot_account, value);
}

const MAX_BYTES: u32 = 16384;
const MAX_TIPPERS: u32 = 100;

benchmarks! {
	_ { }

	propose_spend {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(0);
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)

	reject_proposal {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(1);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
	}: _(RawOrigin::Root, proposal_id)

	approve_proposal {
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(0);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
	}: _(RawOrigin::Root, proposal_id)

	report_awesome {
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
	}: _(RawOrigin::Signed(caller), reason, awesome_person)

	retract_tip {
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
		Treasury::<T>::report_awesome(
			RawOrigin::Signed(caller.clone()).into(),
			reason.clone(),
			awesome_person.clone()
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &awesome_person));
	}: _(RawOrigin::Signed(caller), hash)

	tip_new {
		let r in 0 .. MAX_BYTES;
		let t in 1 .. MAX_TIPPERS;

		let (caller, reason, beneficiary, value) = setup_tip::<T>(r, t)?;
	}: _(RawOrigin::Signed(caller), reason, beneficiary, value)

	tip {
		let t in 1 .. MAX_TIPPERS;
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T>::contains_key(hash), "tip does not exist");
		create_tips::<T>(t - 1, hash.clone(), value)?;
		let caller = account("member", t - 1, SEED);
	}: _(RawOrigin::Signed(caller), hash, value)

	close_tip {
		let t in 1 .. MAX_TIPPERS;

		// Make sure pot is funded
		setup_pod_account::<T>();

		// Set up a new tip proposal
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;

		// Create a bunch of tips
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T>::contains_key(hash), "tip does not exist");
		create_tips::<T>(t, hash.clone(), value)?;

		let caller = account("caller", t, SEED);
	}: _(RawOrigin::Signed(caller), hash)

	propose_bounty {
		let d in 0 .. MAX_BYTES;

		let (caller, curator, fee, value, description) = setup_bounty::<T>(d);
	}: _(RawOrigin::Signed(caller), value, description)

	reject_bounty {
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
	}: _(RawOrigin::Root, bounty_id)

	approve_bounty {
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
	}: _(RawOrigin::Root, bounty_id)

	assign_curator {
		setup_pod_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Treasury::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
	}: _(RawOrigin::Root, bounty_id, curator_lookup, fee)

	unassign_curator {
		setup_pod_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Treasury::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
		Treasury::<T>::assign_curator(RawOrigin::Root.into(), bounty_id, curator_lookup, fee)?;
	}: _(RawOrigin::Root, bounty_id)

	accept_curator {
		setup_pod_account::<T>();
		let (caller, curator, fee, value, reason) = setup_bounty::<T>(MAX_BYTES);
		let curator_lookup = T::Lookup::unlookup(curator.clone());
		Treasury::<T>::propose_bounty(RawOrigin::Signed(caller).into(), value, reason)?;
		let bounty_id = BountyCount::get() - 1;
		Treasury::<T>::approve_bounty(RawOrigin::Root.into(), bounty_id)?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
		Treasury::<T>::assign_curator(RawOrigin::Root.into(), bounty_id, curator_lookup, fee)?;
	}: _(RawOrigin::Signed(curator), bounty_id)

	award_bounty {
		setup_pod_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;
		let beneficiary = T::Lookup::unlookup(account("beneficiary", 0, SEED));
	}: _(RawOrigin::Signed(curator), bounty_id, beneficiary)

	claim_bounty {
		setup_pod_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;

		let beneficiary = T::Lookup::unlookup(account("beneficiary", 0, SEED));
		Treasury::<T>::award_bounty(RawOrigin::Signed(curator.clone()).into(), bounty_id, beneficiary)?;

		frame_system::Module::<T>::set_block_number(T::BountyDepositPayoutDelay::get());

	}: _(RawOrigin::Signed(curator), bounty_id)

	cancel_bounty {
		setup_pod_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;
	}: _(RawOrigin::Signed(curator), bounty_id)

	extend_bounty_expiry {
		setup_pod_account::<T>();
		let (curator_lookup, bounty_id) = create_bounty::<T>()?;
		Treasury::<T>::on_initialize(T::BlockNumber::zero());

		let bounty_id = BountyCount::get() - 1;
		let curator = T::Lookup::lookup(curator_lookup)?;
	}: _(RawOrigin::Signed(curator), bounty_id, Vec::new())

	update_bounty_value_minimum {
		let minimum_balance = T::Currency::minimum_balance();
	}: _(RawOrigin::Root, minimum_balance.into())

	on_initialize_proposals {
		let p in 0 .. 100;
		setup_pod_account::<T>();
		create_approved_proposals::<T>(p)?;
	}: {
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
	}

	on_initialize_bounties {
		let b in 0 .. 100;
		setup_pod_account::<T>();
		create_approved_bounties::<T>(b)?;
	}: {
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
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
			assert_ok!(test_benchmark_propose_spend::<Test>());
			assert_ok!(test_benchmark_reject_proposal::<Test>());
			assert_ok!(test_benchmark_approve_proposal::<Test>());
			assert_ok!(test_benchmark_report_awesome::<Test>());
			assert_ok!(test_benchmark_retract_tip::<Test>());
			assert_ok!(test_benchmark_tip_new::<Test>());
			assert_ok!(test_benchmark_tip::<Test>());
			assert_ok!(test_benchmark_close_tip::<Test>());
			assert_ok!(test_benchmark_propose_bounty::<Test>());
			assert_ok!(test_benchmark_approve_bounty::<Test>());
			assert_ok!(test_benchmark_reject_bounty::<Test>());
			assert_ok!(test_benchmark_assign_curator::<Test>());
			assert_ok!(test_benchmark_unassign_curator::<Test>());
			assert_ok!(test_benchmark_accept_curator::<Test>());
			assert_ok!(test_benchmark_award_bounty::<Test>());
			assert_ok!(test_benchmark_claim_bounty::<Test>());
			assert_ok!(test_benchmark_cancel_bounty::<Test>());
			assert_ok!(test_benchmark_extend_bounty_expiry::<Test>());
			assert_ok!(test_benchmark_update_bounty_value_minimum::<Test>());
			assert_ok!(test_benchmark_on_initialize_proposals::<Test>());
			assert_ok!(test_benchmark_on_initialize_bounties::<Test>());
		});
	}
}
