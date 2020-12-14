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
use frame_system::{Module as System, RawOrigin};
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use sp_core::blake2_256;
use frame_support::{
	traits::{OnInitialize, OnFinalize},
};
use sp_runtime::traits::One;

use crate::Module as NameService;
const SEED: u32 = 1;

fn run_to_block<T : Config>(n: T::BlockNumber) {
	while System::<T>::block_number() < n {
		NameService::<T>::on_finalize(System::<T>::block_number());
		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		NameService::<T>::on_initialize(System::<T>::block_number());
	}
}

benchmarks! {
	_ { }

	// Benchmark bid with the worst possible scenario
	// ie. When the bid is ongoing and new_bidder != current_bidder
	bid {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let current_bidder : T::AccountId = account("current_bidder", 0, SEED);
		let new_bidder : T::AccountId = whitelisted_caller();
		let balance = T::Currency::minimum_balance().max(T::MinBid::get()).saturating_mul(100.into());
		T::Currency::make_free_balance_be(&current_bidder, balance);
		T::Currency::make_free_balance_be(&new_bidder, balance);
		// create first bid
		NameService::<T>::bid(RawOrigin::Signed(current_bidder.clone()).into(), name_hash, T::MinBid::get())?;
		let new_bid_amount = T::MinBid::get().saturating_mul(2u32.into());
	}: _(RawOrigin::Signed(new_bidder.clone()), name_hash, new_bid_amount)
	verify {
		let stored_data = Registration::<T>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::Bidding {
			who: new_bidder.clone(),
			bid_end: T::BiddingPeriod::get().saturating_add(1u32.into()),
			amount: new_bid_amount
		});
		assert_eq!(T::Currency::total_balance(&current_bidder), balance);
		assert_eq!(T::Currency::free_balance(&new_bidder), balance.saturating_sub(new_bid_amount));
	}

	// Benchmark claim with the worst possible scenario
	// ie. When a claim is valid and for (min+1) periods
	claim {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let current_bidder : T::AccountId = whitelisted_caller();
		let balance = T::Currency::minimum_balance().max(T::MinBid::get()).saturating_mul(100.into());
		T::Currency::make_free_balance_be(&current_bidder, balance);
		// create winning bid
		NameService::<T>::bid(RawOrigin::Signed(
			current_bidder.clone()).into(), 
			name_hash, 
			T::MinBid::get())?;
		run_to_block::<T>(T::BiddingPeriod::get());
	}: _(RawOrigin::Signed(current_bidder.clone()), name_hash, 2 as u32)
	verify {
		let stored_data = Registration::<T>::get(&name_hash);
		let expected_expiry = T::BiddingPeriod::get()
			.saturating_add(T::OwnershipPeriod::get()
			.saturating_mul(2u32.into()));
		assert_eq!(stored_data, NameStatus::Owned {
			who: current_bidder.clone(),
			expiration : Some(expected_expiry)
		});
		assert_eq!(T::Currency::free_balance(&current_bidder), 
					balance.saturating_sub(T::MinBid::get().saturating_mul(4.into())));
	}

	// Benchmark free with the worst possible scenario
	// ie. When a bid has expired and not claimed
	free {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let current_bidder : T::AccountId = whitelisted_caller();
		let balance = T::Currency::minimum_balance().max(T::MinBid::get()).saturating_mul(100.into());
		T::Currency::make_free_balance_be(&current_bidder, balance);
		// bid for the name
		NameService::<T>::bid(RawOrigin::Signed(current_bidder.clone()).into(), name_hash, T::MinBid::get())?;
		// expiry+bid+claim time
		let block_to_free = T::BiddingPeriod::get()
			.saturating_mul(2u32.into())
			.saturating_add(T::ClaimPeriod::get());
		run_to_block::<T>(block_to_free.saturating_add(1u32.into()));
	}: _(RawOrigin::Signed(current_bidder.clone()), name_hash)
	verify {
		let stored_data = Registration::<T>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::default());
		assert_eq!(T::Currency::total_balance(&current_bidder), balance.saturating_sub(T::MinBid::get()));
	}

	// Benchmark assign with the worst possible scenario
	// ie. When a name is Owned and target is being set
	assign {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let caller : T::AccountId = whitelisted_caller();
		// set caller as the owner of name
		let state = NameStatus::<T::AccountId, T::BlockNumber, BalanceOf<T>>::Owned{ 
			who : caller.clone(), 
			expiration : None 
		};
		Registration::<T>::insert(&name_hash, state);
	}: _(RawOrigin::Signed(caller.clone()), name_hash, Some(caller.clone()))
	verify {
		assert_eq!(Lookup::<T>::get(&name_hash), Some(caller.clone()));
	}

	// Benchmark unassign with the worst possible scenario
	// ie. When the caller is the target and can unassign
	unassign {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let caller : T::AccountId = whitelisted_caller();
		// set caller as the target of name
		Lookup::<T>::insert(&name_hash, caller.clone());
	}: _(RawOrigin::Signed(caller.clone()), name_hash)
	verify {
		assert_eq!(Lookup::<T>::get(&name_hash), None);
	}

	// Benchmark extend_ownership with the worst possible scenario
	// ie. When the name is Owned, has an expiration date and extension is enabled
	extend_ownership {
		// Test data
		let name_hash = blake2_256(b"shawntabrizi");
		let caller : T::AccountId = whitelisted_caller();
		let balance = T::Currency::minimum_balance()
					.max(T::MinBid::get())
					.saturating_mul(100.into());
		T::Currency::make_free_balance_be(&caller, balance);
		// set caller as the owner of name
		let state = NameStatus::<T::AccountId, T::BlockNumber, BalanceOf<T>>::Owned{ 
			who : caller.clone(), 
			expiration : Some(0.into()) 
		};
		Registration::<T>::insert(&name_hash, state);
	}: _(RawOrigin::Signed(caller.clone()), name_hash)
	verify {
		let stored_data = Registration::<T>::get(&name_hash);
		assert_eq!(stored_data, NameStatus::Owned {
			who: caller.clone(),
			expiration : Some(100.into())
		});
		assert_eq!(T::Currency::free_balance(&caller), 
			balance.saturating_sub(T::ExtensionConfig::get().extension_fee));
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

	#[test]
	fn claim() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_claim::<Test>());
		});
	}

	#[test]
	fn free() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_free::<Test>());
		});
	}

	#[test]
	fn assign() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_assign::<Test>());
		});
	}

	#[test]
	fn unassign() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_unassign::<Test>());
		});
	}

	#[test]
	fn extend_ownership() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_extend_ownership::<Test>());
		});
	}
}
