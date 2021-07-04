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

//! Vesting pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::{RawOrigin, Pallet as System};
use frame_benchmarking::{benchmarks, account, whitelisted_caller, impl_benchmark_test_suite};
use sp_runtime::traits::Bounded;
use frame_support::assert_ok;

use crate::Pallet as Vesting;

const SEED: u32 = 0;
const ED: u32 = 256;

type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

fn add_locks<T: Config>(who: &T::AccountId, n: u8) {
	for id in 0 .. n {
		let lock_id = [id; 8];
		let locked = ED;

		let reasons = WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE;
		T::Currency::set_lock(lock_id, who, locked.into(), reasons);
	}
}

fn add_vesting_schedules<T: Config>(
	target: <T::Lookup as StaticLookup>::Source,
	n: u32,
) -> Result<BalanceOf<T>, &'static str> {
	let min_transfer = T::MinVestedTransfer::get();
	let per_block_duration_20 = min_transfer.checked_div(&20u32.into()).unwrap();

	let locked = min_transfer;
	let per_block = per_block_duration_20;
	let starting_block = 1u32;

	let source: T::AccountId = account("source", 0, SEED);
	let source_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(source.clone());
	T::Currency::make_free_balance_be(&source, BalanceOf::<T>::max_value());

	System::<T>::set_block_number(T::BlockNumber::zero());

	let mut total_locked: BalanceOf<T> = Zero::zero();
	for _ in 0 .. n {
		total_locked += locked;

		let schedule = VestingInfo::new::<T>(locked, per_block, starting_block.into());
		assert_ok!(Vesting::<T>::do_vested_transfer(
			source_lookup.clone(),
			target.clone(),
			schedule
		));
	}

	Ok(total_locked.into())
}

benchmarks! {
	vest_locked {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 1 .. T::MaxVestingSchedules::get();

		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value() / 2u32.into());
		add_locks::<T>(&caller, l as u8);
		let expected_balance = add_vesting_schedules::<T>(caller_lookup, s)?;

		// At block zero, everything is vested.
		assert_eq!(System::<T>::block_number(), T::BlockNumber::zero());
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance.into()),
			"Vesting schedule not added",
		);
	}: vest(RawOrigin::Signed(caller.clone()))
	verify {
		// Nothing happened since everything is still vested.
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance.into()),
			"Vesting schedule was removed",
		);
	}

	vest_unlocked {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 1 .. T::MaxVestingSchedules::get();

		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value() / 2u32.into());
		add_locks::<T>(&caller, l as u8);
		add_vesting_schedules::<T>(caller_lookup, s)?;

		// At block 21, everything is unvested.
		System::<T>::set_block_number(21u32.into());
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(BalanceOf::<T>::zero()),
			"Vesting schedule still active",
		);
	}: vest(RawOrigin::Signed(caller.clone()))
	verify {
		// Vesting schedule is removed!
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			None,
			"Vesting schedule was not removed",
		);
	}

	vest_other_locked {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 1 .. T::MaxVestingSchedules::get();

		let other: T::AccountId = account("other", 0, SEED);
		let other_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(other.clone());
		T::Currency::make_free_balance_be(&other, BalanceOf::<T>::max_value() / 2u32.into());
		add_locks::<T>(&other, l as u8);
		let expected_balance = add_vesting_schedules::<T>(other_lookup.clone(), s)?;

		// At block zero, everything is vested.
		assert_eq!(System::<T>::block_number(), T::BlockNumber::zero());
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(expected_balance),
			"Vesting schedule not added",
		);

		let caller: T::AccountId = whitelisted_caller();
	}: vest_other(RawOrigin::Signed(caller.clone()), other_lookup)
	verify {
		// Nothing happened since everything is still vested.
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(expected_balance.into()),
			"Vesting schedule was removed",
		);
	}

	vest_other_unlocked {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 1 .. T::MaxVestingSchedules::get();

		let other: T::AccountId = account("other", 0, SEED);
		let other_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(other.clone());
		T::Currency::make_free_balance_be(&other, BalanceOf::<T>::max_value() / 2u32.into());

		add_locks::<T>(&other, l as u8);
		add_vesting_schedules::<T>(other_lookup.clone(), s)?;
		// At block 21, everything is unvested.
		System::<T>::set_block_number(21u32.into());
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(BalanceOf::<T>::zero()),
			"Vesting schedule still active",
		);

		let caller: T::AccountId = whitelisted_caller();
	}: vest_other(RawOrigin::Signed(caller.clone()), other_lookup)
	verify {
		// Vesting schedule is removed!
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			None,
			"Vesting schedule was not removed",
		);
	}

	last_vested_transfer {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 0 .. T::MaxVestingSchedules::get() - 1;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		// Give target existing locks
		add_locks::<T>(&target, l as u8);
		// Add one less than max vesting schedules
		let mut expected_balance = add_vesting_schedules::<T>(target_lookup.clone(), s)?;

		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();
		expected_balance += transfer_amount;

		let vesting_schedule = VestingInfo::new::<T>(
			transfer_amount,
			per_block_duration_20,
			1u32.into(),
		);
	}: vested_transfer(RawOrigin::Signed(caller), target_lookup, vesting_schedule)
	verify {
		assert_eq!(
			expected_balance,
			T::Currency::free_balance(&target),
			"Transfer didn't happen",
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&target),
			Some(expected_balance),
			"Lock not correctly updated",
		);
	}

	first_vested_transfer {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		// Give target existing locks
		add_locks::<T>(&target, l as u8);

		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();

		let vesting_schedule = VestingInfo::new::<T>(
			transfer_amount,
			per_block_duration_20,
			1u32.into(),
		);

	}:  vested_transfer(RawOrigin::Signed(caller), target_lookup, vesting_schedule)
	verify {
		assert_eq!(
			transfer_amount,
			T::Currency::free_balance(&target),
			"Transfer didn't happen",
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&target),
			Some(transfer_amount),
			"Lock not created",
		);
	}

	first_force_vested_transfer {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;

		let source: T::AccountId = account("source", 0, SEED);
		let source_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(source.clone());
		T::Currency::make_free_balance_be(&source, BalanceOf::<T>::max_value());

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		// Give target existing locks
		add_locks::<T>(&target, l as u8);

		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();

		let vesting_schedule = VestingInfo::new::<T>(
			transfer_amount,
			per_block_duration_20,
			1u32.into(),
		);
	}: force_vested_transfer(RawOrigin::Root, source_lookup, target_lookup, vesting_schedule)
	verify {
		assert_eq!(
			transfer_amount,
			T::Currency::free_balance(&target),
			"Transfer didn't happen",
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&target),
			Some(transfer_amount),
			"Lock not created",
		);
	}

	last_force_vested_transfer {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 0 .. T::MaxVestingSchedules::get() - 1;

		let source: T::AccountId = account("source", 0, SEED);
		let source_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(source.clone());
		T::Currency::make_free_balance_be(&source, BalanceOf::<T>::max_value());

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		// Give target existing locks
		add_locks::<T>(&target, l as u8);
		// Add one less than max vesting schedules
		let mut expected_balance = add_vesting_schedules::<T>(target_lookup.clone(), s)?;

		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();
		expected_balance += transfer_amount;

		let vesting_schedule = VestingInfo::new::<T>(
			transfer_amount,
			per_block_duration_20,
			1u32.into(),
		);
	}: force_vested_transfer(RawOrigin::Root, source_lookup, target_lookup, vesting_schedule)
	verify {
		assert_eq!(
			expected_balance,
			T::Currency::free_balance(&target),
			"Transfer didn't happen",
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&target),
			Some(expected_balance.into()),
				"Lock not correctly updated",
			);
		}

	not_unlocking_merge_schedules {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 2 .. T::MaxVestingSchedules::get();

		let caller: T::AccountId = account("caller", 0, SEED);
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		// Give target existing locks
		add_locks::<T>(&caller, l as u8);
		// Add max vesting schedules
		let expected_balance = add_vesting_schedules::<T>(caller_lookup.clone(), s)?;
		// Values of the schedules added by `add_vesting_schedules`.
		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();

		// Schedules are not vesting at block 0
		assert_eq!(System::<T>::block_number(), T::BlockNumber::zero());
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance),
			"Vesting balance should equal sum locked of all schedules",
		);
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap().len(),
			s as usize,
			"There should be exactly max vesting schedules"
		);
	}: merge_schedules(RawOrigin::Signed(caller.clone()), 0, s - 1)
	verify {
		let expected_schedule = VestingInfo::new::<T>(
			T::MinVestedTransfer::get() * 2u32.into(),
			per_block_duration_20 * 2u32.into(),
			1u32.into(),
		);
		let expected_index = (s - 2) as usize;
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap()[expected_index],
			expected_schedule
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance),
			"Vesting balance should equal total locked of all schedules",
		);
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap().len(),
			(s - 1) as usize,
			"Schedule count should reduce by 1"
		);
	}

	unlocking_merge_schedules {
		let l in 0 .. MaxLocksOf::<T>::get() - 1;
		let s in 2 .. T::MaxVestingSchedules::get();

		let caller: T::AccountId = account("caller", 0, SEED);
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		// Give target existing locks
		add_locks::<T>(&caller, l as u8);
		// Add max vesting schedules
		let mut expected_balance = add_vesting_schedules::<T>(caller_lookup.clone(), s)?;
		// Values of the schedules added by `add_vesting_schedules`.
		let transfer_amount = T::MinVestedTransfer::get();
		let per_block_duration_20 = transfer_amount.checked_div(&20u32.into()).unwrap();

		// Go to half way through all the schedules duration. (They all start at 1, and have a duration of 20).
		System::<T>::set_block_number(11u32.into());
		// We expect half the original locked balance
		expected_balance = expected_balance / 2u32.into();
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance),
			"Vesting balance should reflect that we are half way through all schedules duration",
		);
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap().len(),
			s as usize,
			"There should be exactly max vesting schedules"
		);
	}: merge_schedules(RawOrigin::Signed(caller.clone()), 0, s - 1)
	verify {
		let expected_schedule = VestingInfo::new::<T>(
			transfer_amount,
			per_block_duration_20 * 2u32.into(),
			11u32.into(),
		);
		let expected_index = (s - 2) as usize;
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap()[expected_index],
			expected_schedule,
			"New schedule is properly created and placed"
		);
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap()[expected_index],
			expected_schedule
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(expected_balance),
			"Vesting balance should equal half total locked of all schedules",
		);
		assert_eq!(
			Vesting::<T>::vesting(&caller).unwrap().len(),
			(s - 1) as usize,
			"Schedule count should reduce by 1"
		);
	}
}

impl_benchmark_test_suite!(
	Vesting,
	crate::mock::ExtBuilder::default().existential_deposit(256).build(),
	crate::mock::Test,
);
