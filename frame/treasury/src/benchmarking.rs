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
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use frame_support::traits::OnInitialize;

use crate::Module as Treasury;

const SEED: u32 = 0;

// Create the pre-requisite information needed to create a treasury `propose_spend`.
fn setup_proposal<T: Trait<I>, I: Instance>(u: u32) -> (
	T::AccountId,
	BalanceOf<T, I>,
	<T::Lookup as StaticLookup>::Source,
) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T, I> = T::ProposalBondMinimum::get().saturating_mul(100.into());
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let beneficiary = account("beneficiary", u, SEED);
	let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	(caller, value, beneficiary_lookup)
}

// Create the pre-requisite information needed to create a `report_awesome`.
fn setup_awesome<T: Trait<I>, I: Instance>(length: u32) -> (T::AccountId, Vec<u8>, T::AccountId) {
	let caller = whitelisted_caller();
	let value = T::TipReportDepositBase::get()
		+ T::TipReportDepositPerByte::get() * length.into()
		+ T::Currency::minimum_balance();
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let reason = vec![0; length as usize];
	let awesome_person = account("awesome", 0, SEED);
	(caller, reason, awesome_person)
}

// Create the pre-requisite information needed to call `tip_new`.
fn setup_tip<T: Trait<I>, I: Instance>(r: u32, t: u32) ->
	Result<(T::AccountId, Vec<u8>, T::AccountId, BalanceOf<T, I>), &'static str>
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
fn create_tips<T: Trait<I>, I: Instance>(t: u32, hash: T::Hash, value: BalanceOf<T, I>) -> Result<(), &'static str> {
	for i in 0 .. t {
		let caller = account("member", i, SEED);
		ensure!(T::Tippers::contains(&caller), "caller is not a tipper");
		Treasury::<T, I>::tip(RawOrigin::Signed(caller).into(), hash, value)?;
	}
	Tips::<T, I>::mutate(hash, |maybe_tip| {
		if let Some(open_tip) = maybe_tip {
			open_tip.closes = Some(T::BlockNumber::zero());
		}
	});
	Ok(())
}

// Create proposals that are approved for use in `on_initialize`.
fn create_approved_proposals<T: Trait<I>, I: Instance>(n: u32) -> Result<(), &'static str> {
	for i in 0 .. n {
		let (caller, value, lookup) = setup_proposal::<T, I>(i);
		Treasury::<T, I>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			lookup
		)?;
		let proposal_id = <ProposalCount<I>>::get() - 1;
		Treasury::<T, I>::approve_proposal(RawOrigin::Root.into(), proposal_id)?;
	}
	ensure!(<Approvals<I>>::get().len() == n as usize, "Not all approved");
	Ok(())
}

const MAX_BYTES: u32 = 16384;
const MAX_TIPPERS: u32 = 100;

benchmarks! {
	_ { }

	propose_spend {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(u);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)

	reject_proposal {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(u);
		Treasury::<T, _>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = Treasury::<T, _>::proposal_count() - 1;
	}: _(RawOrigin::Root, proposal_id)

	approve_proposal {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T, _>(u);
		Treasury::<T, _>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = Treasury::<T, _>::proposal_count() - 1;
	}: _(RawOrigin::Root, proposal_id)

	report_awesome {
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T, _>(r);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), reason, awesome_person)

	retract_tip {
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T, _>(r);
		Treasury::<T, _>::report_awesome(
			RawOrigin::Signed(caller.clone()).into(),
			reason.clone(),
			awesome_person.clone()
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &awesome_person));
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), hash)

	tip_new {
		let r in 0 .. MAX_BYTES;
		let t in 1 .. MAX_TIPPERS;

		let (caller, reason, beneficiary, value) = setup_tip::<T, _>(r, t)?;
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), reason, beneficiary, value)

	tip {
		let t in 1 .. MAX_TIPPERS;
		let (member, reason, beneficiary, value) = setup_tip::<T, _>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T, _>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T, _>::contains_key(hash), "tip does not exist");
		create_tips::<T, _>(t - 1, hash.clone(), value)?;
		let caller = account("member", t - 1, SEED);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), hash, value)

	close_tip {
		let t in 1 .. MAX_TIPPERS;

		// Make sure pot is funded
		let pot_account = Treasury::<T, _>::account_id();
		let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
		let _ = T::Currency::make_free_balance_be(&pot_account, value);

		// Set up a new tip proposal
		let (member, reason, beneficiary, value) = setup_tip::<T, _>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T, _>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;

		// Create a bunch of tips
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T, _>::contains_key(hash), "tip does not exist");
		create_tips::<T, _>(t, hash.clone(), value)?;

		let caller = account("caller", t, SEED);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), hash)

	on_initialize {
		let p in 0 .. 100;
		let pot_account = Treasury::<T, _>::account_id();
		let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
		let _ = T::Currency::make_free_balance_be(&pot_account, value);
		create_approved_proposals::<T, _>(p)?;
	}: {
		Treasury::<T, _>::on_initialize(T::BlockNumber::zero());
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
			assert_ok!(test_benchmark_on_initialize::<Test>());
		});
	}
}
