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

use super::*;

use frame_system::{RawOrigin, Module as System};
use sp_io::hashing::blake2_256;
use frame_benchmarking::{benchmarks, account};

use crate::Module as Vesting;

const SEED: u32 = 0;
const MAX_LOCKS: u32 = 20;

fn add_locks<T: Trait>(l: u32) {
	for id in 0..l {
		let lock_id = <[u8; 8]>::decode(&mut &id.using_encoded(blake2_256)[..])
			.unwrap_or_default();
		let locker = account("locker", 0, SEED);
		let locked = 1;
		let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
		T::Currency::set_lock(lock_id, &locker, locked.into(), reasons);
	}
}

fn setup<T: Trait>(b: u32) -> T::AccountId {
		let locked = 1;
		let per_block = 1;
		let starting_block = 0;

		let caller = account("caller", 0, SEED);

		// Add schedule to avoid `NotVesting` error.
		let _ = Vesting::<T>::add_vesting_schedule(
			&caller,
			locked.into(),
			per_block.into(),
			starting_block.into(),
		);

		// Set lock and block number to take different code paths.
		let reasons = WithdrawReason::Transfer | WithdrawReason::Reserve;
		T::Currency::set_lock(VESTING_ID, &caller, locked.into(), reasons);
		System::<T>::set_block_number(b.into());

		caller
}

benchmarks! {
	_ {
		// Current block. It allows to hit different paths of `update_lock`.
		// It doesn't seems to influence the timings which branch is taken.
		let b in 0 .. 1 => ();
		// Number of previous locks.
		// It doesn't seems to influence the timings for lower values.
		let l in 0 .. MAX_LOCKS => add_locks::<T>(l);
	}

	vest {
		let b in ...;
		let l in ...;

		let caller = setup::<T>(b);

	}: _(RawOrigin::Signed(caller))

	vest_other {
		let b in ...;
		let l in ...;

		let other: T::AccountId = setup::<T>(b);
		let other_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(other.clone());

		let caller = account("caller", 0, SEED);

	}: _(RawOrigin::Signed(caller), other_lookup)

	vested_transfer {
		let u in 0 .. 1000;

		let from = account("from", u, SEED);
		let to = account("to", u, SEED);
		let to_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(to);

		let transfer_amount = T::MinVestedTransfer::get();

		let vesting_schedule = VestingInfo {
			locked: transfer_amount,
			per_block: 1.into(),
			starting_block: 0.into(),
		};

		let _ = T::Currency::make_free_balance_be(&from, transfer_amount * 10.into());
		
	}: _(RawOrigin::Signed(from), to_lookup, vesting_schedule)
}
