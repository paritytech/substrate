// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! DataFeed pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::parameter_types;
use frame_system::RawOrigin;

use crate::Module as DataFeed;

parameter_types! {
	pub storage StorageArgument: DataType = DataType::U128(0);
}

fn add_tmp_provider<T: Trait>(provider: T::AccountId) {
	let provider_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(provider);
	let _ = DataFeed::<T>::add_provider(RawOrigin::Root.into(), provider_lookup.clone());
}

fn add_data_info<T: Trait>(key: StorageKey, provider: T::AccountId) {
	add_tmp_provider::<T>(provider.clone());
	let data_info = super::FeededDataInfo {
		key_str: "USD".as_bytes().to_vec(),
		number_type: NumberType::FixedU128,
		operation: Operations::Average,
		schedule: 2.into(),
	};
	let _ = DataFeed::<T>::register_storage_key(RawOrigin::Signed(provider).into(), key, data_info);
}

benchmarks! {
	_ {
		let l in 1 .. 64 => (); // we think key bytes length should not more than 64
		let n in 1 .. 2048 => (); // we think max url length should not more than 2048
	}

	register_storage_key {
		let l in ...;

		let provider: T::AccountId = whitelisted_caller();
		add_tmp_provider::<T>(provider.clone());

		let key = StorageArgument::key().to_vec();
		let data_info = super::FeededDataInfo {
			key_str: "USD".as_bytes().to_vec(),
			number_type: NumberType::FixedU128,
			operation: Operations::Average,
			schedule: 2.into(),
		};
	}: _(RawOrigin::Signed(provider.clone()), key.clone(), data_info.clone())
	verify {
		assert_eq!(DataFeed::<T>::data_infos(&key), Some(data_info));
	}

	remove_storage_key {
		let l in ...;
		let provider: T::AccountId = whitelisted_caller();
		let key = StorageArgument::key().to_vec();
		add_data_info::<T>(key.clone(), provider.clone());
		let _ = DataFeed::<T>::set_url(RawOrigin::Root.into(), key.clone(), b"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".to_vec());
	}: _(RawOrigin::Signed(provider.clone()), key.clone())
	verify {
		assert_eq!(DataFeed::<T>::data_infos(&key), None);
	}

	set_url {
		let l in ...;
		let n in ...;
		let provider: T::AccountId = whitelisted_caller();
		let key = StorageArgument::key().to_vec();
		add_data_info::<T>(key.clone(), provider.clone());
		let url = b"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".to_vec();
	}: _(RawOrigin::Signed(provider.clone()), key.clone(), url.clone())
	verify {
		assert_eq!(DataFeed::<T>::url(&key), Some(url));
	}

	set_offchain_period {
		let l in ...;
		let provider: T::AccountId = whitelisted_caller();
		let key = StorageArgument::key().to_vec();
		add_data_info::<T>(key.clone(), provider.clone());
		let _ = DataFeed::<T>::set_url(RawOrigin::Root.into(), key.clone(), b"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".to_vec());
		let period = Some(100.into());
	}: _(RawOrigin::Signed(provider.clone()), key.clone(), period)
	verify {
		assert_eq!(DataFeed::<T>::offchain_period(&key), period);
	}

	feed_data {
		let l in ...;
		let provider: T::AccountId = whitelisted_caller();
		let key = StorageArgument::key().to_vec();
		add_data_info::<T>(key.clone(), provider.clone());
		let value = DataType::FixedU128(1_u128.into());
	}: _(RawOrigin::Signed(provider.clone()), key.clone(), value.clone())
	verify {
		assert_eq!(DataFeed::<T>::feeded_data(&key, &provider), Some([value; RING_BUF_LEN]));
	}

	add_provider {
		let provider: T::AccountId = whitelisted_caller();
		let provider_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(provider.clone());
	}: _(RawOrigin::Root, provider_lookup)
	verify {
		assert!(DataFeed::<T>::all_providers().contains(&provider));
	}

	remove_provider {
		let provider: T::AccountId = whitelisted_caller();
		add_tmp_provider::<T>(provider.clone());
		let provider_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(provider.clone());
	}: _(RawOrigin::Root, provider_lookup)
	verify {
		assert!(!DataFeed::<T>::all_providers().contains(&provider));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn benchmark_register_storage_key() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_register_storage_key::<Test>());
		});
	}
	#[test]
	fn benchmark_remove_storage_key() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_remove_storage_key::<Test>());
		});
	}
	#[test]
	fn benchmark_set_url() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_set_url::<Test>());
		});
	}
	#[test]
	fn benchmark_set_offchain_period() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_set_offchain_period::<Test>());
		});
	}
	#[test]
	fn benchmark_feed_data() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_feed_data::<Test>());
		});
	}
	#[test]
	fn benchmark_add_provider() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_add_provider::<Test>());
		});
	}
	#[test]
	fn benchmark_remove_provider() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_remove_provider::<Test>());
		});
	}
}
