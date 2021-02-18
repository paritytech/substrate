// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use frame_support::{
	assert_ok, assert_noop, transactional, StorageMap, StorageValue,
	dispatch::{DispatchError, DispatchResult}, storage::{with_transaction, TransactionOutcome::*},
};
use sp_io::TestExternalities;
use sp_std::result;

pub trait Config: frame_support_test::Config {}

frame_support::decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {
		#[weight = 0]
		#[transactional]
		fn value_commits(_origin, v: u32) {
			Value::set(v);
		}

		#[weight = 0]
		#[transactional]
		fn value_rollbacks(_origin, v: u32) -> DispatchResult {
			Value::set(v);
			Err(DispatchError::Other("nah"))
		}
	}
}

frame_support::decl_storage!{
	trait Store for Module<T: Config> as StorageTransactions {
		pub Value: u32;
		pub Map: map hasher(twox_64_concat) String => u32;
	}
}

struct Runtime;

impl frame_support_test::Config for Runtime {
	type Origin = u32;
	type BlockNumber = u32;
	type PalletInfo = frame_support_test::PanicPalletInfo;
	type DbWeight = ();
}

impl Config for Runtime {}

#[test]
fn storage_transaction_basic_commit() {
	TestExternalities::default().execute_with(|| {

		assert_eq!(Value::get(), 0);
		assert!(!Map::contains_key("val0"));

		with_transaction(|| {
			Value::set(99);
			Map::insert("val0", 99);
			assert_eq!(Value::get(), 99);
			assert_eq!(Map::get("val0"), 99);
			Commit(())
		});

		assert_eq!(Value::get(), 99);
		assert_eq!(Map::get("val0"), 99);
	});
}

#[test]
fn storage_transaction_basic_rollback() {
	TestExternalities::default().execute_with(|| {

		assert_eq!(Value::get(), 0);
		assert_eq!(Map::get("val0"), 0);

		with_transaction(|| {
			Value::set(99);
			Map::insert("val0", 99);
			assert_eq!(Value::get(), 99);
			assert_eq!(Map::get("val0"), 99);
			Rollback(())
		});

		assert_eq!(Value::get(), 0);
		assert_eq!(Map::get("val0"), 0);
	});
}

#[test]
fn storage_transaction_rollback_then_commit() {
	TestExternalities::default().execute_with(|| {
		Value::set(1);
		Map::insert("val1", 1);

		with_transaction(|| {
			Value::set(2);
			Map::insert("val1", 2);
			Map::insert("val2", 2);

			with_transaction(|| {
				Value::set(3);
				Map::insert("val1", 3);
				Map::insert("val2", 3);
				Map::insert("val3", 3);

				assert_eq!(Value::get(), 3);
				assert_eq!(Map::get("val1"), 3);
				assert_eq!(Map::get("val2"), 3);
				assert_eq!(Map::get("val3"), 3);

				Rollback(())
			});

			assert_eq!(Value::get(), 2);
			assert_eq!(Map::get("val1"), 2);
			assert_eq!(Map::get("val2"), 2);
			assert_eq!(Map::get("val3"), 0);

			Commit(())
		});

		assert_eq!(Value::get(), 2);
		assert_eq!(Map::get("val1"), 2);
		assert_eq!(Map::get("val2"), 2);
		assert_eq!(Map::get("val3"), 0);
	});
}

#[test]
fn storage_transaction_commit_then_rollback() {
	TestExternalities::default().execute_with(|| {
		Value::set(1);
		Map::insert("val1", 1);

		with_transaction(|| {
			Value::set(2);
			Map::insert("val1", 2);
			Map::insert("val2", 2);

			with_transaction(|| {
				Value::set(3);
				Map::insert("val1", 3);
				Map::insert("val2", 3);
				Map::insert("val3", 3);

				assert_eq!(Value::get(), 3);
				assert_eq!(Map::get("val1"), 3);
				assert_eq!(Map::get("val2"), 3);
				assert_eq!(Map::get("val3"), 3);

				Commit(())
			});

			assert_eq!(Value::get(), 3);
			assert_eq!(Map::get("val1"), 3);
			assert_eq!(Map::get("val2"), 3);
			assert_eq!(Map::get("val3"), 3);

			Rollback(())
		});

		assert_eq!(Value::get(), 1);
		assert_eq!(Map::get("val1"), 1);
		assert_eq!(Map::get("val2"), 0);
		assert_eq!(Map::get("val3"), 0);
	});
}

#[test]
fn transactional_annotation() {
	fn set_value(v: u32) -> DispatchResult {
		Value::set(v);
		Ok(())
	}

	#[transactional]
	fn value_commits(v: u32) -> result::Result<u32, &'static str> {
		set_value(v)?;
		Ok(v)
	}

	#[transactional]
	fn value_rollbacks(v: u32) -> result::Result<u32, &'static str> {
		set_value(v)?;
		Err("nah")?;
		Ok(v)
	}

	TestExternalities::default().execute_with(|| {
		assert_ok!(value_commits(2), 2);
		assert_eq!(Value::get(), 2);

		assert_noop!(value_rollbacks(3), "nah");
	});
}

#[test]
fn transactional_annotation_in_decl_module() {
	TestExternalities::default().execute_with(|| {
		let origin = 0;
		assert_ok!(<Module<Runtime>>::value_commits(origin, 2));
		assert_eq!(Value::get(), 2);

		assert_noop!(<Module<Runtime>>::value_rollbacks(origin, 3), "nah");
	});
}
