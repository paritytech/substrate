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

//! Salary pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as Salary;

use frame_benchmarking::v2::*;
use frame_system::{Pallet as System, RawOrigin};
use sp_core::Get;

const SEED: u32 = 0;

fn ensure_member_with_salary<T: Config<I>, I: 'static>(who: &T::AccountId) {
	// induct if not a member.
	if T::Members::rank_of(who).is_none() {
		T::Members::induct(who).unwrap();
	}
	// promote until they have a salary.
	for _ in 0..255 {
		let r = T::Members::rank_of(who).expect("prior guard ensures `who` is a member; qed");
		if !T::Salary::get_salary(r, &who).is_zero() {
			break
		}
		T::Members::promote(who).unwrap();
	}
}

#[instance_benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn init() {
		let caller: T::AccountId = whitelisted_caller();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		assert!(Salary::<T, I>::status().is_some());
	}

	#[benchmark]
	fn bump() {
		let caller: T::AccountId = whitelisted_caller();
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + Salary::<T, I>::cycle_period());

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		assert_eq!(Salary::<T, I>::status().unwrap().cycle_index, 1u32.into());
	}

	#[benchmark]
	fn induct() {
		let caller = whitelisted_caller();
		ensure_member_with_salary::<T, I>(&caller);
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		assert!(Salary::<T, I>::last_active(&caller).is_ok());
	}

	#[benchmark]
	fn register() {
		let caller = whitelisted_caller();
		ensure_member_with_salary::<T, I>(&caller);
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();
		Salary::<T, I>::induct(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + Salary::<T, I>::cycle_period());
		Salary::<T, I>::bump(RawOrigin::Signed(caller.clone()).into()).unwrap();

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		assert_eq!(Salary::<T, I>::last_active(&caller).unwrap(), 1u32.into());
	}

	#[benchmark]
	fn payout() {
		let caller = whitelisted_caller();
		ensure_member_with_salary::<T, I>(&caller);
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();
		Salary::<T, I>::induct(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + Salary::<T, I>::cycle_period());
		Salary::<T, I>::bump(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + T::RegistrationPeriod::get());

		let salary = T::Salary::get_salary(T::Members::rank_of(&caller).unwrap(), &caller);
		T::Paymaster::ensure_successful(&caller, (), salary);

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		match Claimant::<T, I>::get(&caller) {
			Some(ClaimantStatus { last_active, status: Attempted { id, .. } }) => {
				assert_eq!(last_active, 1u32.into());
				assert_ne!(T::Paymaster::check_payment(id), PaymentStatus::Failure);
			},
			_ => panic!("No claim made"),
		}
		assert!(Salary::<T, I>::payout(RawOrigin::Signed(caller.clone()).into()).is_err());
	}

	#[benchmark]
	fn payout_other() {
		let caller = whitelisted_caller();
		ensure_member_with_salary::<T, I>(&caller);
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();
		Salary::<T, I>::induct(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + Salary::<T, I>::cycle_period());
		Salary::<T, I>::bump(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + T::RegistrationPeriod::get());

		let salary = T::Salary::get_salary(T::Members::rank_of(&caller).unwrap(), &caller);
		let recipient: T::AccountId = account("recipient", 0, SEED);
		T::Paymaster::ensure_successful(&recipient, (), salary);

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()), recipient.clone());

		match Claimant::<T, I>::get(&caller) {
			Some(ClaimantStatus { last_active, status: Attempted { id, .. } }) => {
				assert_eq!(last_active, 1u32.into());
				assert_ne!(T::Paymaster::check_payment(id), PaymentStatus::Failure);
			},
			_ => panic!("No claim made"),
		}
		assert!(Salary::<T, I>::payout(RawOrigin::Signed(caller.clone()).into()).is_err());
	}

	#[benchmark]
	fn check_payment() {
		let caller = whitelisted_caller();
		ensure_member_with_salary::<T, I>(&caller);
		Salary::<T, I>::init(RawOrigin::Signed(caller.clone()).into()).unwrap();
		Salary::<T, I>::induct(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + Salary::<T, I>::cycle_period());
		Salary::<T, I>::bump(RawOrigin::Signed(caller.clone()).into()).unwrap();
		System::<T>::set_block_number(System::<T>::block_number() + T::RegistrationPeriod::get());

		let salary = T::Salary::get_salary(T::Members::rank_of(&caller).unwrap(), &caller);
		let recipient: T::AccountId = account("recipient", 0, SEED);
		T::Paymaster::ensure_successful(&recipient, (), salary);
		Salary::<T, I>::payout(RawOrigin::Signed(caller.clone()).into()).unwrap();
		let id = match Claimant::<T, I>::get(&caller).unwrap().status {
			Attempted { id, .. } => id,
			_ => panic!("No claim made"),
		};
		T::Paymaster::ensure_concluded(id);

		#[extrinsic_call]
		_(RawOrigin::Signed(caller.clone()));

		assert!(!matches!(Claimant::<T, I>::get(&caller).unwrap().status, Attempted { .. }));
	}

	impl_benchmark_test_suite! {
		Salary,
		crate::tests::new_test_ext(),
		crate::tests::Test,
	}
}
