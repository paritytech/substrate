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

//! Elections-Phragmen pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use codec::{Encode, Decode};
use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use frame_benchmarking::benchmarks;
use sp_runtime::traits::Bounded;

use crate::Module as Elections;

const SEED: u32 = 0;
const DEFAULT_STAKE: u32 = 1000;

fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let entropy = (name, index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

/// Add `c` new candidates.
fn submit_candidates<T: Trait>(c: u32) -> Result<Vec<T::AccountId>, &'static str> {
	(0..c).map(|i| {
		let account = account::<T>("candidate", i);
		let _ = T::Currency::make_free_balance_be(&account, BalanceOf::<T>::max_value());
		<Elections<T>>::submit_candidacy(RawOrigin::Signed(account).into())
			.map_err(|_| "failed to submit candidacy")?;
		Ok(account)
	}).collect::<Result<_, _>>()
}

benchmarks! {
	_ { }

	vote {
		// range of candidates to vote for.
		let x in 0 .. (MAXIMUM_VOTE as u32);

		// create a bunch of candidates.
		let all_candidates = submit_candidates::<T>(MAXIMUM_VOTE as u32)?;

		let caller = account::<T>("caller", SEED);
		let stake = BalanceOf::<T>::from(DEFAULT_STAKE);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		// vote first `x` ones.
		let votes = all_candidates.into_iter().take(x as usize).collect();
	}: _(RawOrigin::Signed(caller), votes, stake)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_vote::<Test>());
		});
	}
}

