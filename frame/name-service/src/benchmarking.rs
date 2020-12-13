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

// Benchmarks for Name Service Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use sp_core::blake2_256;

use crate::Module as NameService;

const SEED: u32 = 1;

benchmarks! {
	_ { }

	// Benchmark bid with the worst possible scenario
	// ie. When the bid is ongoing and new_bidder != current_bidder
	bid {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let current_bidder : T::AccountId = account("current_bidder", 0, SEED);
		let new_bidder : T::AccountId = whitelisted_caller();

		T::Currency::make_free_balance_be(&current_bidder, 5.into());
		T::Currency::make_free_balance_be(&new_bidder, 10.into());

		NameService::<T>::bid(RawOrigin::Signed(current_bidder.clone()).into(), name_hash, 5.into())?;
	}: bid(RawOrigin::Signed(new_bidder.clone()), name_hash, 10.into())
	verify {
		let stored_data = Registration::<T>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::Bidding {
			who: new_bidder.clone(),
			bid_end: 11.into(),
			amount: 10.into()
		});
		assert_eq!(T::Currency::free_balance(&current_bidder), 5.into());
		assert_eq!(T::Currency::free_balance(&new_bidder), 0.into());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn bid() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_bid::<Test>());
		});
	}
}
