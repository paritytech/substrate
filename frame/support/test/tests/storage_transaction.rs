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

use codec::{Encode, Decode, EncodeLike};
use frame_support::{
	StorageMap, StorageValue, storage::{with_transaction, TransactionOutcome::*},
};
use sp_io::TestExternalities;

pub trait Trait {
	type Origin;
	type BlockNumber: Encode + Decode + EncodeLike + Default + Clone;
}

frame_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

frame_support::decl_storage!{
	trait Store for Module<T: Trait> as StorageTransactions {
		pub Value: u32;
		pub Map: map hasher(twox_64_concat) String => u32;
	}
}


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
