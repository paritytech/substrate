// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

// Benchmarks for Utility Pallet

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use frame_benchmarking::{benchmarks, impl_benchmark_test_suite, whitelisted_caller};
use frame_support::{storage, traits::Get, weights::DispatchClass};
use frame_system::{Call, DigestItemOf, Pallet as System, RawOrigin};
use sp_core::{storage::well_known_keys, ChangesTrieConfiguration};
use sp_runtime::traits::Hash;
use sp_std::{prelude::*, vec};

mod mock;

pub struct Pallet<T: Config>(System<T>);
pub trait Config: frame_system::Config {}

benchmarks! {
	remark {
		let b in 0 .. *T::BlockLength::get().max.get(DispatchClass::Normal) as u32;
		let remark_message = vec![1; b as usize];
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), remark_message)

	remark_with_event {
		let b in 0 .. *T::BlockLength::get().max.get(DispatchClass::Normal) as u32;
		let remark_message = vec![1; b as usize];
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), remark_message)

	set_heap_pages {
	}: _(RawOrigin::Root, Default::default())

	// `set_code` was not benchmarked because it is pretty hard to come up with a real
	// Wasm runtime to test the upgrade with. But this is okay because we will make
	// `set_code` take a full block anyway.

	#[extra]
	set_code_without_checks {
		// Assume Wasm ~4MB
		let code = vec![1; 4_000_000 as usize];
	}: _(RawOrigin::Root, code)
	verify {
		let current_code = storage::unhashed::get_raw(well_known_keys::CODE).ok_or("Code not stored.")?;
		assert_eq!(current_code.len(), 4_000_000 as usize);
	}

	set_changes_trie_config {
		let d = 1000;

		let digest_item = DigestItemOf::<T>::Other(vec![]);

		for i in 0 .. d {
			System::<T>::deposit_log(digest_item.clone());
		}
		let changes_trie_config = ChangesTrieConfiguration {
			digest_interval: d,
			digest_levels: d,
		};
	}: _(RawOrigin::Root, Some(changes_trie_config))
	verify {
		assert_eq!(System::<T>::digest().logs.len(), (d + 1) as usize)
	}

	set_storage {
		let i in 1 .. 1000;

		// Set up i items to add
		let mut items = Vec::new();
		for j in 0 .. i {
			let hash = (i, j).using_encoded(T::Hashing::hash).as_ref().to_vec();
			items.push((hash.clone(), hash.clone()));
		}
	}: _(RawOrigin::Root, items)
	verify {
		let last_hash = (i, i - 1).using_encoded(T::Hashing::hash);
		let value = storage::unhashed::get_raw(last_hash.as_ref()).ok_or("No value stored")?;
		assert_eq!(value, last_hash.as_ref().to_vec());
	}

	kill_storage {
		let i in 1 .. 1000;

		// Add i items to storage
		let mut items = Vec::new();
		for j in 0 .. i {
			let hash = (i, j).using_encoded(T::Hashing::hash).as_ref().to_vec();
			storage::unhashed::put_raw(&hash, &hash);
			items.push(hash);
		}

		// We will verify this value is removed
		let last_hash = (i, i - 1).using_encoded(T::Hashing::hash);
		let value = storage::unhashed::get_raw(last_hash.as_ref()).ok_or("No value stored")?;
		assert_eq!(value, last_hash.as_ref().to_vec());

	}: _(RawOrigin::Root, items)
	verify {
		assert_eq!(storage::unhashed::get_raw(last_hash.as_ref()), None);
	}

	kill_prefix {
		let p in 1 .. 1000;

		let prefix = p.using_encoded(T::Hashing::hash).as_ref().to_vec();
		// add p items that share a prefix
		for i in 0 .. p {
			let hash = (p, i).using_encoded(T::Hashing::hash).as_ref().to_vec();
			let key = [&prefix[..], &hash[..]].concat();
			storage::unhashed::put_raw(&key, &key);
		}

		// We will verify this value is removed
		let last_hash = (p, p - 1).using_encoded(T::Hashing::hash).as_ref().to_vec();
		let last_key = [&prefix[..], &last_hash[..]].concat();
		let value = storage::unhashed::get_raw(&last_key).ok_or("No value stored")?;
		assert_eq!(value, last_key);

	}: _(RawOrigin::Root, prefix, p)
	verify {
		assert_eq!(storage::unhashed::get_raw(&last_key), None);
	}
}

impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test,);
