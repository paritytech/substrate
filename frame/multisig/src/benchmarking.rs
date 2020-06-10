// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Multisig Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::Saturating;

use crate::Module as Multisig;

const SEED: u32 = 0;

fn setup_multi<T: Trait>(s: u32, z: u32)
	-> Result<(Vec<T::AccountId>, Box<<T as Trait>::Call>), &'static str>
{
	let mut signatories: Vec<T::AccountId> = Vec::new();
	for i in 0 .. s {
		let signatory = account("signatory", i, SEED);
		// Give them some balance for a possible deposit
		let deposit = T::DepositBase::get() + T::DepositFactor::get() * s.into();
		let balance = T::Currency::minimum_balance().saturating_mul(100.into()) + deposit;
		T::Currency::make_free_balance_be(&signatory, balance);
		signatories.push(signatory);
	}
	signatories.sort();
	let call: Box<<T as Trait>::Call> = Box::new(frame_system::Call::remark(vec![0; z as usize]).into());
	return Ok((signatories, call))
}

benchmarks! {
	_ { }

	as_multi_create {
		// Signatories, need at least 2 total people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
	}: as_multi(RawOrigin::Signed(caller), s as u16, signatories, None, call)

	as_multi_approve {
		// Signatories, need at least 2 people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let mut signatories2 = signatories.clone();
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
		// before the call, get the timepoint
		let timepoint = Multisig::<T>::timepoint();
		// Create the multi
		Multisig::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
		let caller2 = signatories2.remove(0);
	}: as_multi(RawOrigin::Signed(caller2), s as u16, signatories2, Some(timepoint), call)

	as_multi_complete {
		// Signatories, need at least 2 people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let mut signatories2 = signatories.clone();
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
		// before the call, get the timepoint
		let timepoint = Multisig::<T>::timepoint();
		// Create the multi
		Multisig::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
		// Everyone except the first person approves
		for i in 1 .. s - 1 {
			let mut signatories_loop = signatories2.clone();
			let caller_loop = signatories_loop.remove(i as usize);
			let o = RawOrigin::Signed(caller_loop).into();
			Multisig::<T>::as_multi(o, s as u16, signatories_loop, Some(timepoint), call.clone())?;
		}
		let caller2 = signatories2.remove(0);
	}: as_multi(RawOrigin::Signed(caller2), s as u16, signatories2, Some(timepoint), call)

	approve_as_multi_create {
		// Signatories, need at least 2 people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
		let call_hash = call.using_encoded(blake2_256);
		// Create the multi
	}: approve_as_multi(RawOrigin::Signed(caller), s as u16, signatories, None, call_hash)

	approve_as_multi_approve {
		// Signatories, need at least 2 people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let mut signatories2 = signatories.clone();
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
		let call_hash = call.using_encoded(blake2_256);
		// before the call, get the timepoint
		let timepoint = Multisig::<T>::timepoint();
		// Create the multi
		Multisig::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
		let caller2 = signatories2.remove(0);
	}: approve_as_multi(RawOrigin::Signed(caller2), s as u16, signatories2, Some(timepoint), call_hash)

	cancel_as_multi {
		// Signatories, need at least 2 people
		let s in 2 .. T::MaxSignatories::get() as u32;
		// Transaction Length
		let z in 0 .. 10_000;
		let (mut signatories, call) = setup_multi::<T>(s, z)?;
		let caller = signatories.pop().ok_or("signatories should have len 2 or more")?;
		let call_hash = call.using_encoded(blake2_256);
		let timepoint = Multisig::<T>::timepoint();
		// Create the multi
		let o = RawOrigin::Signed(caller.clone()).into();
		Multisig::<T>::as_multi(o, s as u16, signatories.clone(), None, call.clone())?;
	}: _(RawOrigin::Signed(caller), s as u16, signatories, timepoint, call_hash)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_as_multi_create::<Test>());
			assert_ok!(test_benchmark_as_multi_approve::<Test>());
			assert_ok!(test_benchmark_as_multi_complete::<Test>());
			assert_ok!(test_benchmark_approve_as_multi_create::<Test>());
			assert_ok!(test_benchmark_approve_as_multi_approve::<Test>());
			assert_ok!(test_benchmark_cancel_as_multi::<Test>());
		});
	}
}
