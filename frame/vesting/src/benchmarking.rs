// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Vesting pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::{RawOrigin, Module as System};
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::Bounded;

use crate::Module as Vesting;

const SEED: u32 = 0;
const MAX_LOCKS: u32 = 20;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

fn add_locks<T: Trait>(who: &T::AccountId, n: u8) {
	for id in 0..n {
		let lock_id = [id; 8];
		let locked = 100;
		let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
		T::Currency::set_lock(lock_id, who, locked.into(), reasons);
	}
}

fn add_vesting_schedule<T: Trait>(who: &T::AccountId) -> Result<(), &'static str> {
	let locked = 100;
	let per_block = 10;
	let starting_block = 1;

	System::<T>::set_block_number(0.into());

	// Add schedule to avoid `NotVesting` error.
	Vesting::<T>::add_vesting_schedule(
		&who,
		locked.into(),
		per_block.into(),
		starting_block.into(),
	)?;
	Ok(())
}

benchmarks! {
	_ { }

	vest_locked {
		let l in 0 .. MAX_LOCKS;

		let caller = account("caller", 0, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		add_locks::<T>(&caller, l as u8);
		add_vesting_schedule::<T>(&caller)?;
		// At block zero, everything is vested.
		System::<T>::set_block_number(T::BlockNumber::zero());
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(100.into()),
			"Vesting schedule not added",
		);
	}: vest(RawOrigin::Signed(caller.clone()))
	verify {
		// Nothing happened since everything is still vested.
		assert_eq!(
			Vesting::<T>::vesting_balance(&caller),
			Some(100.into()),
			"Vesting schedule was removed",
		);
	}

	vest_unlocked {
		let l in 0 .. MAX_LOCKS;

		let caller = account("caller", 0, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		add_locks::<T>(&caller, l as u8);
		add_vesting_schedule::<T>(&caller)?;
		// At block 20, everything is unvested.
		System::<T>::set_block_number(20.into());
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
		let l in 0 .. MAX_LOCKS;

		let other: T::AccountId = account("other", 0, SEED);
		let other_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(other.clone());
		T::Currency::make_free_balance_be(&other, BalanceOf::<T>::max_value());
		add_locks::<T>(&other, l as u8);
		add_vesting_schedule::<T>(&other)?;
		// At block zero, everything is vested.
		System::<T>::set_block_number(T::BlockNumber::zero());
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(100.into()),
			"Vesting schedule not added",
		);

		let caller: T::AccountId = account("caller", 0, SEED);
	}: vest_other(RawOrigin::Signed(caller.clone()), other_lookup)
	verify {
		// Nothing happened since everything is still vested.
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(100.into()),
			"Vesting schedule was removed",
		);
	}

	vest_other_unlocked {
		let l in 0 .. MAX_LOCKS;

		let other: T::AccountId = account("other", 0, SEED);
		let other_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(other.clone());
		T::Currency::make_free_balance_be(&other, BalanceOf::<T>::max_value());
		add_locks::<T>(&other, l as u8);
		add_vesting_schedule::<T>(&other)?;
		// At block 20, everything is unvested.
		System::<T>::set_block_number(20.into());
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			Some(BalanceOf::<T>::zero()),
			"Vesting schedule still active",
		);

		let caller: T::AccountId = account("caller", 0, SEED);
	}: vest_other(RawOrigin::Signed(caller.clone()), other_lookup)
	verify {
		// Vesting schedule is removed!
		assert_eq!(
			Vesting::<T>::vesting_balance(&other),
			None,
			"Vesting schedule was not removed",
		);
	}

	vested_transfer {
		let l in 0 .. MAX_LOCKS;

		let caller: T::AccountId = account("caller", 0, SEED);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		// Give target existing locks
		add_locks::<T>(&target, l as u8);

		let transfer_amount = T::MinVestedTransfer::get();

		let vesting_schedule = VestingInfo {
			locked: transfer_amount,
			per_block: 10.into(),
			starting_block: 1.into(),
		};
	}: _(RawOrigin::Signed(caller), target_lookup, vesting_schedule)
	verify {
		assert_eq!(
			T::MinVestedTransfer::get(),
			T::Currency::free_balance(&target),
			"Transfer didn't happen",
		);
		assert_eq!(
			Vesting::<T>::vesting_balance(&target),
			Some(T::MinVestedTransfer::get()),
			"Lock not created",
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		ExtBuilder::default().existential_deposit(256).build().execute_with(|| {
			assert_ok!(test_benchmark_vest_locked::<Test>());
			assert_ok!(test_benchmark_vest_unlocked::<Test>());
			assert_ok!(test_benchmark_vest_other_locked::<Test>());
			assert_ok!(test_benchmark_vest_other_unlocked::<Test>());
			assert_ok!(test_benchmark_vested_transfer::<Test>());
		});
	}
}
