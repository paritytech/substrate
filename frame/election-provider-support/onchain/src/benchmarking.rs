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

#[cfg(test)]
use crate::Pallet as ElectionProviderSupportOnchain;

// This is also used in `pallet_election_provider_multi_phase` benchmarking.
pub const SEED: u32 = 999;
pub fn set_up_data_provider<
	T: frame_system::Config,
	DataProvider: ElectionDataProvider<AccountId = T::AccountId, BlockNumber = T::BlockNumber>,
>(
	voters_len: u32,
	targets_len: u32,
	degree: u32,
	weight: u64,
) {
	DataProvider::clear();
	log::info!(
		"setting up with voters = {} [degree = {}], targets = {}",
		voters_len,
		degree,
		targets_len
	);

	// fill targets.
	let mut targets = (0..targets_len)
		.map(|i| {
			let target = frame_benchmarking::account::<T::AccountId>("Target", i, SEED);
			DataProvider::add_target(target.clone());
			target
		})
		.collect::<Vec<_>>();
	// we should always have enough voters to fill.
	assert!(targets.len() > degree as usize);
	targets.truncate(degree as usize);

	// fill voters.
	(0..voters_len).for_each(|i| {
		let voter = frame_benchmarking::account::<T::AccountId>("Voter", i, SEED);
		DataProvider::add_voter(voter, weight, targets.clone().try_into().unwrap());
	});
}

benchmarks! {
	phragmen {
		// number of votes in snapshot.
		let v in (T::BenchmarkingConfig::VOTERS[0]) .. T::BenchmarkingConfig::VOTERS[1];
		// number of targets in snapshot.
		let t in (T::BenchmarkingConfig::TARGETS[0]) .. T::BenchmarkingConfig::TARGETS[1];
		// number of votes per voter (ie the degree).
		let d in (T::BenchmarkingConfig::VOTES_PER_VOTER[0]) .. T::BenchmarkingConfig::VOTES_PER_VOTER[1];

		// we don't directly need the data-provider to be populated, but it is just easy to use it.
		// TODO: create a mock one and then we can remove `DataProvider` from the `Config`
		set_up_data_provider::<T, T::DataProvider>(v, t, d, 1_000u64);
	}: {
		assert!(OnChainPhragmen::<T>::elect().is_ok());
	} verify {
	}

	impl_benchmark_test_suite!(
		ElectionProviderSupportOnchain,
		sp_io::TestExternalities::new_empty(),
		crate::tests::Runtime,
	);
}
