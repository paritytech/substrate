// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use frame_benchmarking::{
	v1::{benchmarks, whitelisted_caller},
	BenchmarkError,
};
use frame_support::{dispatch::DispatchClass, storage, traits::Get};
use frame_system::{Call, Pallet as System, RawOrigin};
use sp_core::storage::well_known_keys;
use sp_runtime::traits::Hash;
use sp_std::{prelude::*, vec};

mod mock;

pub struct Pallet<T: Config>(System<T>);
pub trait Config: frame_system::Config {
	/// Adds ability to the Runtime to test against their sample code.
	///
	/// Default is `../res/kitchensink_runtime.compact.compressed.wasm`.
	fn prepare_set_code_data() -> Vec<u8> {
		include_bytes!("../res/kitchensink_runtime.compact.compressed.wasm").to_vec()
	}

	/// Adds ability to the Runtime to prepare/initialize before running benchmark `set_code`.
	fn setup_set_code_requirements(_code: &Vec<u8>) -> Result<(), BenchmarkError> {
		Ok(())
	}

	/// Adds ability to the Runtime to do custom validation after benchmark.
	///
	/// Default is checking for `CodeUpdated` event .
	fn verify_set_code() {
		System::<Self>::assert_last_event(frame_system::Event::<Self>::CodeUpdated.into());
	}
}

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

	set_code {
		let runtime_blob = T::prepare_set_code_data();
		T::setup_set_code_requirements(&runtime_blob)?;
	}: _(RawOrigin::Root, runtime_blob)
	verify {
		T::verify_set_code()
	}

	#[extra]
	set_code_without_checks {
		// Assume Wasm ~4MB
		let code = vec![1; 4_000_000 as usize];
		T::setup_set_code_requirements(&code)?;
	}: _(RawOrigin::Root, code)
	verify {
		let current_code = storage::unhashed::get_raw(well_known_keys::CODE).ok_or("Code not stored.")?;
		assert_eq!(current_code.len(), 4_000_000 as usize);
	}

	#[skip_meta]
	set_storage {
		let i in 0 .. 1000;

		// Set up i items to add
		let mut items = Vec::new();
		for j in 0 .. i {
			let hash = (i, j).using_encoded(T::Hashing::hash).as_ref().to_vec();
			items.push((hash.clone(), hash.clone()));
		}

		let items_to_verify = items.clone();
	}: _(RawOrigin::Root, items)
	verify {
		// Verify that they're actually in the storage.
		for (item, _) in items_to_verify {
			let value = storage::unhashed::get_raw(&item).ok_or("No value stored")?;
			assert_eq!(value, *item);
		}
	}

	#[skip_meta]
	kill_storage {
		let i in 0 .. 1000;

		// Add i items to storage
		let mut items = Vec::with_capacity(i as usize);
		for j in 0 .. i {
			let hash = (i, j).using_encoded(T::Hashing::hash).as_ref().to_vec();
			storage::unhashed::put_raw(&hash, &hash);
			items.push(hash);
		}

		// Verify that they're actually in the storage.
		for item in &items {
			let value = storage::unhashed::get_raw(item).ok_or("No value stored")?;
			assert_eq!(value, *item);
		}

		let items_to_verify = items.clone();
	}: _(RawOrigin::Root, items)
	verify {
		// Verify that they're not in the storage anymore.
		for item in items_to_verify {
			assert!(storage::unhashed::get_raw(&item).is_none());
		}
	}

	#[skip_meta]
	kill_prefix {
		let p in 0 .. 1000;

		let prefix = p.using_encoded(T::Hashing::hash).as_ref().to_vec();
		let mut items = Vec::with_capacity(p as usize);
		// add p items that share a prefix
		for i in 0 .. p {
			let hash = (p, i).using_encoded(T::Hashing::hash).as_ref().to_vec();
			let key = [&prefix[..], &hash[..]].concat();
			storage::unhashed::put_raw(&key, &key);
			items.push(key);
		}

		// Verify that they're actually in the storage.
		for item in &items {
			let value = storage::unhashed::get_raw(item).ok_or("No value stored")?;
			assert_eq!(value, *item);
		}
	}: _(RawOrigin::Root, prefix, p)
	verify {
		// Verify that they're not in the storage anymore.
		for item in items {
			assert!(storage::unhashed::get_raw(&item).is_none());
		}
	}

	impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test);
}
