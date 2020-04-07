// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// Benchmarks for Utility Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::Saturating;

use crate::Module as Utility;

const SEED: u32 = 0;

fn setup_multi<T: Trait>(s: u32, z: u32) -> Result<(Vec<T::AccountId>, Box<<T as Trait>::Call>), &'static str>{
	let mut signatories: Vec<T::AccountId> = Vec::new();
	for i in 0 .. s {
		let signatory = account("signatory", i, SEED);
		// Give them some balance for a possible deposit
		let deposit = T::MultisigDepositBase::get() + T::MultisigDepositFactor::get() * s.into();
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

	batch {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Trait>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark(vec![]).into();
			calls.push(call);
		}
		let caller = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), calls)

	as_sub {
		let u in 0 .. 1000;
		let caller = account("caller", u, SEED);
		let call = Box::new(frame_system::Call::remark(vec![]).into());
	}: _(RawOrigin::Signed(caller), u as u16, call)

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
		let timepoint = Utility::<T>::timepoint();
		// Create the multi
		Utility::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
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
		let timepoint = Utility::<T>::timepoint();
		// Create the multi
		Utility::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
		// Everyone except the first person approves
		for i in 1 .. s - 1 {
			let mut signatories_loop = signatories2.clone();
			let caller_loop = signatories_loop.remove(i as usize);
			Utility::<T>::as_multi(RawOrigin::Signed(caller_loop).into(), s as u16, signatories_loop, Some(timepoint), call.clone())?;
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
		let timepoint = Utility::<T>::timepoint();
		// Create the multi
		Utility::<T>::as_multi(RawOrigin::Signed(caller).into(), s as u16, signatories, None, call.clone())?;
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
		let timepoint = Utility::<T>::timepoint();
		// Create the multi
		Utility::<T>::as_multi(RawOrigin::Signed(caller.clone()).into(), s as u16, signatories.clone(), None, call.clone())?;
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
			assert_ok!(test_benchmark_batch::<Test>());
			assert_ok!(test_benchmark_as_sub::<Test>());
			assert_ok!(test_benchmark_as_multi_create::<Test>());
			assert_ok!(test_benchmark_as_multi_approve::<Test>());
			assert_ok!(test_benchmark_as_multi_complete::<Test>());
			assert_ok!(test_benchmark_approve_as_multi_create::<Test>());
			assert_ok!(test_benchmark_approve_as_multi_approve::<Test>());
			assert_ok!(test_benchmark_cancel_as_multi::<Test>());
		});
	}
}
