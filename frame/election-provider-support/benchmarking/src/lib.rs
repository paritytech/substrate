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
// This is separated into its own crate to avoid bloating the size of the runtime.

#![cfg(feature = "runtime-benchmarks")]
#![cfg_attr(not(feature = "std"), no_std)]

use frame_benchmarking::{benchmarks, Vec};
use frame_election_provider_support::{onchain, ElectionDataProvider, ElectionProvider};
use frame_support::{log, pallet_prelude::ConstU32};
use sp_runtime::SaturatedConversion;

use pallet_staking::Pallet as Staking;

const MAX_ELECTING_VOTERS: u32 = 20_000;
const MAX_TARGETS: u32 = 2_000;

type OnChainPhragmen<T> = onchain::BoundedPhragmen<
	T,
	Staking<T>,
	ConstU32<MAX_ELECTING_VOTERS>,
	ConstU32<MAX_TARGETS>,
	sp_runtime::Perbill,
>;

type OnChainPhragMMS<T> = onchain::BoundedPhragMMS<
	T,
	Staking<T>,
	ConstU32<MAX_ELECTING_VOTERS>,
	ConstU32<MAX_TARGETS>,
	sp_runtime::Perbill,
>;

pub struct Pallet<T: Config>(frame_system::Pallet<T>);
pub trait Config: pallet_staking::Config + onchain::BenchmarkingConfig {}

// This is also used in `pallet_election_provider_multi_phase` benchmarking.
pub const SEED: u32 = 999;
pub fn set_up_data_provider<
	T: frame_system::Config,
	DataProvider: ElectionDataProvider<AccountId = T::AccountId, BlockNumber = T::BlockNumber>,
	Currency: frame_support::traits::Currency<T::AccountId>,
>(
	voters_len: u32,
	targets_len: u32,
	degree: u32,
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
		let weight = Currency::minimum_balance().saturated_into::<u64>() * 1000;
		DataProvider::add_voter(voter, weight, targets.clone().try_into().unwrap());
	});
}

fn set_up_data_provider_internal<T: Config>(voters_len: u32, targets_len: u32, degree: u32) {
	set_up_data_provider::<T, Staking<T>, <T as pallet_staking::Config>::Currency>(
		voters_len,
		targets_len,
		degree,
	);
}

benchmarks! {
	phragmen {
		// number of votes in snapshot.
		let v in (<T as onchain::BenchmarkingConfig>::VOTERS[0])
			.. <T as onchain::BenchmarkingConfig>::VOTERS[1];
		// number of targets in snapshot.
		let t in (<T as onchain::BenchmarkingConfig>::TARGETS[0])
			.. <T as onchain::BenchmarkingConfig>::TARGETS[1];
		// number of votes per voter (ie the degree).
		let d in (<T as onchain::BenchmarkingConfig>::VOTES_PER_VOTER[0])
			.. <T as onchain::BenchmarkingConfig>::VOTES_PER_VOTER[1];

		// we don't directly need the data-provider to be populated, but it is just easy to use it.
		set_up_data_provider_internal::<T>(v, t, d);
	}: {
		assert!(OnChainPhragmen::<T>::elect().is_ok());
	}

	phragmms {
		// number of votes in snapshot.
		let v in (<T as onchain::BenchmarkingConfig>::VOTERS[0])
			.. <T as onchain::BenchmarkingConfig>::VOTERS[1];
		// number of targets in snapshot.
		let t in (<T as onchain::BenchmarkingConfig>::TARGETS[0])
			.. <T as onchain::BenchmarkingConfig>::TARGETS[1];
		// number of votes per voter (ie the degree).
		let d in (<T as onchain::BenchmarkingConfig>::VOTES_PER_VOTER[0])
			.. <T as onchain::BenchmarkingConfig>::VOTES_PER_VOTER[1];

		// we don't directly need the data-provider to be populated, but it is just easy to use it.
		set_up_data_provider_internal::<T>(v, t, d);
	}: {
		assert!(OnChainPhragMMS::<T>::elect().is_ok());
	}
}
