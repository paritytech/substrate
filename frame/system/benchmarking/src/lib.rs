// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Utility Pallet

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
use sp_std::vec;
use sp_std::prelude::*;
use sp_core::{ChangesTrieConfiguration, storage::well_known_keys};
use sp_runtime::traits::Hash;
use frame_benchmarking::{benchmarks, account};
use frame_support::storage::{self, StorageMap};
use frame_system::{Module as System, Call, RawOrigin, DigestItemOf, AccountInfo};

mod mock;

const SEED: u32 = 0;

pub struct Module<T: Trait>(System<T>);
pub trait Trait: frame_system::Trait {}

benchmarks! {
	_ { }

	remark {
		// # of Bytes
		let b in 0 .. 16_384;
		let remark_message = vec![1; b as usize];
		let caller = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), remark_message)

	set_heap_pages {
		// Heap page size
		let i in 0 .. u32::max_value();
	}: _(RawOrigin::Root, i.into())

	// `set_code` was not benchmarked because it is pretty hard to come up with a real
	// Wasm runtime to test the upgrade with. But this is okay because we will make
	// `set_code` take a full block anyway.

	set_code_without_checks {
		// Version number
		let b in 0 .. 16_384;
		let code = vec![1; b as usize];
	}: _(RawOrigin::Root, code)
	verify {
		let current_code = storage::unhashed::get_raw(well_known_keys::CODE).ok_or("Code not stored.")?;
		assert_eq!(current_code.len(), b as usize);
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

	}: _(RawOrigin::Root, prefix)
	verify {
		assert_eq!(storage::unhashed::get_raw(&last_key), None);
	}

	suicide {
		let n in 1 .. 1000;
		let caller: T::AccountId = account("caller", 0, SEED);
		let account_info = AccountInfo::<T::Index, T::AccountData> {
			nonce: n.into(),
			refcount: 0,
			data: T::AccountData::default()
		};
		frame_system::Account::<T>::insert(&caller, account_info);
		let new_account_info = System::<T>::account(caller.clone());
		assert_eq!(new_account_info.nonce, n.into());
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		let account_info = System::<T>::account(&caller);
		assert_eq!(account_info.nonce, 0.into());
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
