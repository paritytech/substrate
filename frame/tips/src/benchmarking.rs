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

//! Treasury tips benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use frame_benchmarking::{account, benchmarks, impl_benchmark_test_suite, whitelisted_caller};
use frame_support::ensure;
use frame_system::RawOrigin;
use sp_runtime::traits::Saturating;

use super::*;
use crate::Pallet as TipsMod;

const SEED: u32 = 0;

// Create the pre-requisite information needed to create a `report_awesome`.
fn setup_awesome<T: Config>(length: u32) -> (T::AccountId, Vec<u8>, T::AccountId) {
	let caller = whitelisted_caller();
	let value = T::TipReportDepositBase::get() +
		T::DataDepositPerByte::get() * length.into() +
		T::Currency::minimum_balance();
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let reason = vec![0; length as usize];
	let awesome_person = account("awesome", 0, SEED);
	(caller, reason, awesome_person)
}

// Create the pre-requisite information needed to call `tip_new`.
fn setup_tip<T: Config>(
	r: u32,
	t: u32,
) -> Result<(T::AccountId, Vec<u8>, T::AccountId, BalanceOf<T>), &'static str> {
	let tippers_count = T::Tippers::count();

	for i in 0..t {
		let member = account("member", i, SEED);
		T::Tippers::add(&member);
		ensure!(T::Tippers::contains(&member), "failed to add tipper");
	}

	ensure!(T::Tippers::count() == tippers_count + t as usize, "problem creating tippers");
	let caller = account("member", t - 1, SEED);
	let reason = vec![0; r as usize];
	let beneficiary = account("beneficiary", t, SEED);
	let value = T::Currency::minimum_balance().saturating_mul(100u32.into());
	Ok((caller, reason, beneficiary, value))
}

// Create `t` new tips for the tip proposal with `hash`.
// This function automatically makes the tip able to close.
fn create_tips<T: Config>(t: u32, hash: T::Hash, value: BalanceOf<T>) -> Result<(), &'static str> {
	for i in 0..t {
		let caller = account("member", i, SEED);
		ensure!(T::Tippers::contains(&caller), "caller is not a tipper");
		TipsMod::<T>::tip(RawOrigin::Signed(caller).into(), hash, value)?;
	}
	Tips::<T>::mutate(hash, |maybe_tip| {
		if let Some(open_tip) = maybe_tip {
			open_tip.closes = Some(T::BlockNumber::zero());
		}
	});
	Ok(())
}

fn setup_pot_account<T: Config>() {
	let pot_account = TipsMod::<T>::account_id();
	let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000u32.into());
	let _ = T::Currency::make_free_balance_be(&pot_account, value);
}

const MAX_BYTES: u32 = 16384;
const MAX_TIPPERS: u32 = 100;

benchmarks! {
	report_awesome {
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), reason, awesome_person)

	retract_tip {
		let r = MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
		TipsMod::<T>::report_awesome(
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

		let (caller, reason, beneficiary, value) = setup_tip::<T>(r, t)?;
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), reason, beneficiary, value)

	tip {
		let t in 1 .. MAX_TIPPERS;
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100u32.into());
		TipsMod::<T>::tip_new(
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
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), hash, value)

	close_tip {
		let t in 1 .. MAX_TIPPERS;

		// Make sure pot is funded
		setup_pot_account::<T>();

		// Set up a new tip proposal
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100u32.into());
		TipsMod::<T>::tip_new(
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
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), hash)

	slash_tip {
		let t in 1 .. MAX_TIPPERS;

		// Make sure pot is funded
		setup_pot_account::<T>();

		// Set up a new tip proposal
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100u32.into());
		TipsMod::<T>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;

		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T>::contains_key(hash), "tip does not exist");
	}: _(RawOrigin::Root, hash)
}

impl_benchmark_test_suite!(TipsMod, crate::tests::new_test_ext(), crate::tests::Test);
