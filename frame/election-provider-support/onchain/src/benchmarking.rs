// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! election provider support onchain pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::{benchmarks, Vec};
use frame_support::log;

use crate::Pallet as ElectionProviderSupportOnchain;

// TODO: copied from multi phase
const SEED: u32 = 999;
fn set_up_data_provider<T: Config>(v: u32, t: u32) {
	T::DataProvider::clear();
	log::info!(
		"setting up with voters = {} [degree = {}], targets = {}",
		v,
		<T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get(),
		t
	);

	// fill targets.
	let mut targets = (0..t)
		.map(|i| {
			let target = frame_benchmarking::account::<T::AccountId>("Target", i, SEED);
			T::DataProvider::add_target(target.clone());
			target
		})
		.collect::<Vec<_>>();
	// we should always have enough voters to fill.
	assert!(
		targets.len() > <T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get() as usize
	);
	targets.truncate(<T::DataProvider as ElectionDataProvider>::MaxVotesPerVoter::get() as usize);

	// fill voters.
	(0..v).for_each(|i| {
		let voter = frame_benchmarking::account::<T::AccountId>("Voter", i, SEED);
		//let weight = T::Currency::minimum_balance().saturated_into::<u64>() * 1000;
		let weight = 1_000;
		T::DataProvider::add_voter(voter, weight, targets.clone().try_into().unwrap());
	});
}

benchmarks! {
	elect_with {
		// we don't directly need the data-provider to be populated, but it is just easy to use it.
		set_up_data_provider::<T>(T::BenchmarkingConfig::MAX_VOTERS, T::BenchmarkingConfig::MAX_TARGETS);
	}: {
		let solution = <ElectionProviderSupportOnchain<T>>::elect_with(None, None);
		assert!(solution.is_ok());
	} verify {
	}

	impl_benchmark_test_suite!(
		ElectionProviderSupportOnchain,
		sp_io::TestExternalities::new_empty(),
		crate::tests::Runtime,
	);
}
