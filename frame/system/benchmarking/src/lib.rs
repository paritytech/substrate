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

// Benchmarks for Utility Pallet

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use sp_std::vec;
use sp_std::prelude::*;
use sp_core::{ChangesTrieConfiguration, storage::well_known_keys};
use sp_runtime::traits::Hash;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Get;
use frame_support::storage::{self, StorageMap};
use frame_system::{Module as System, Call, RawOrigin, DigestItemOf, AccountInfo};

mod mock;

pub struct Module<T: Trait>(System<T>);
pub trait Trait: frame_system::Trait {}

benchmarks! {
	_ { }

	remark {
		let b in 0 .. T::MaximumBlockLength::get();
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
		let d in 0 .. 1000;

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

	suicide {
		let caller: T::AccountId = whitelisted_caller();
		let account_info = AccountInfo::<T::Index, T::AccountData> {
			nonce: 1337u32.into(),
			refcount: 0,
			data: T::AccountData::default()
		};
		frame_system::Account::<T>::insert(&caller, account_info);
		let new_account_info = System::<T>::account(caller.clone());
		assert_eq!(new_account_info.nonce, 1337u32.into());
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		let account_info = System::<T>::account(&caller);
		assert_eq!(account_info.nonce, 0u32.into());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_remark::<Test>());
			assert_ok!(test_benchmark_set_heap_pages::<Test>());
			assert_ok!(test_benchmark_set_code_without_checks::<Test>());
			assert_ok!(test_benchmark_set_changes_trie_config::<Test>());
			assert_ok!(test_benchmark_set_storage::<Test>());
			assert_ok!(test_benchmark_kill_storage::<Test>());
			assert_ok!(test_benchmark_kill_prefix::<Test>());
			assert_ok!(test_benchmark_suicide::<Test>());
		});
	}
}
