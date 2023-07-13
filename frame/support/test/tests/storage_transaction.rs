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

// Disable warnings for #\[transactional\] being deprecated.
#![allow(deprecated)]

use frame_support::{
	assert_noop, assert_ok, assert_storage_noop, derive_impl,
	dispatch::DispatchResult,
	storage::{with_transaction, TransactionOutcome::*},
	transactional,
};
use sp_core::{sr25519, ConstU32};
use sp_io::TestExternalities;
use sp_runtime::{
	generic,
	traits::{BlakeTwo256, Verify},
	TransactionOutcome,
};

pub use self::pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub (super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		#[transactional]
		pub fn value_commits(_origin: OriginFor<T>, v: u32) -> DispatchResult {
			<Value<T>>::set(v);
			Ok(())
		}

		#[pallet::weight(0)]
		#[transactional]
		pub fn value_rollbacks(_origin: OriginFor<T>, v: u32) -> DispatchResult {
			<Value<T>>::set(v);
			Err(DispatchError::Other("nah"))
		}
	}

	#[pallet::storage]
	pub type Value<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::unbounded]
	pub type Map<T: Config> = StorageMap<_, Twox64Concat, String, u32, ValueQuery>;
}

pub type BlockNumber = u32;
pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;

frame_support::construct_runtime!(
	pub enum Runtime

	{
		System: frame_system,
		MyPallet: pallet,
	}
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type Block = Block;
	type BlockHashCount = ConstU32<10>;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();
}

impl Config for Runtime {}

#[test]
fn storage_transaction_basic_commit() {
	TestExternalities::default().execute_with(|| {
		type Value = pallet::Value<Runtime>;
		type Map = pallet::Map<Runtime>;

		assert_eq!(Value::get(), 0);
		assert!(!Map::contains_key("val0"));

		assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
			Value::set(99);
			Map::insert("val0", 99);
			assert_eq!(Value::get(), 99);
			assert_eq!(Map::get("val0"), 99);
			Commit(Ok(()))
		}));

		assert_eq!(Value::get(), 99);
		assert_eq!(Map::get("val0"), 99);
	});
}

#[test]
fn storage_transaction_basic_rollback() {
	TestExternalities::default().execute_with(|| {
		type Value = pallet::Value<Runtime>;
		type Map = pallet::Map<Runtime>;

		assert_eq!(Value::get(), 0);
		assert_eq!(Map::get("val0"), 0);

		assert_noop!(
			with_transaction(|| -> TransactionOutcome<DispatchResult> {
				Value::set(99);
				Map::insert("val0", 99);
				assert_eq!(Value::get(), 99);
				assert_eq!(Map::get("val0"), 99);
				Rollback(Err("revert".into()))
			}),
			"revert"
		);

		assert_storage_noop!(assert_ok!(with_transaction(
			|| -> TransactionOutcome<DispatchResult> {
				Value::set(99);
				Map::insert("val0", 99);
				assert_eq!(Value::get(), 99);
				assert_eq!(Map::get("val0"), 99);
				Rollback(Ok(()))
			}
		)));

		assert_eq!(Value::get(), 0);
		assert_eq!(Map::get("val0"), 0);
	});
}

#[test]
fn storage_transaction_rollback_then_commit() {
	TestExternalities::default().execute_with(|| {
		type Value = pallet::Value<Runtime>;
		type Map = pallet::Map<Runtime>;

		Value::set(1);
		Map::insert("val1", 1);

		assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
			Value::set(2);
			Map::insert("val1", 2);
			Map::insert("val2", 2);

			assert_noop!(
				with_transaction(|| -> TransactionOutcome<DispatchResult> {
					Value::set(3);
					Map::insert("val1", 3);
					Map::insert("val2", 3);
					Map::insert("val3", 3);

					assert_eq!(Value::get(), 3);
					assert_eq!(Map::get("val1"), 3);
					assert_eq!(Map::get("val2"), 3);
					assert_eq!(Map::get("val3"), 3);

					Rollback(Err("revert".into()))
				}),
				"revert"
			);

			assert_eq!(Value::get(), 2);
			assert_eq!(Map::get("val1"), 2);
			assert_eq!(Map::get("val2"), 2);
			assert_eq!(Map::get("val3"), 0);

			Commit(Ok(()))
		}));

		assert_eq!(Value::get(), 2);
		assert_eq!(Map::get("val1"), 2);
		assert_eq!(Map::get("val2"), 2);
		assert_eq!(Map::get("val3"), 0);
	});
}

#[test]
fn storage_transaction_commit_then_rollback() {
	TestExternalities::default().execute_with(|| {
		type Value = pallet::Value<Runtime>;
		type Map = pallet::Map<Runtime>;

		Value::set(1);
		Map::insert("val1", 1);

		assert_noop!(
			with_transaction(|| -> TransactionOutcome<DispatchResult> {
				Value::set(2);
				Map::insert("val1", 2);
				Map::insert("val2", 2);

				assert_ok!(with_transaction(|| -> TransactionOutcome<DispatchResult> {
					Value::set(3);
					Map::insert("val1", 3);
					Map::insert("val2", 3);
					Map::insert("val3", 3);

					assert_eq!(Value::get(), 3);
					assert_eq!(Map::get("val1"), 3);
					assert_eq!(Map::get("val2"), 3);
					assert_eq!(Map::get("val3"), 3);

					Commit(Ok(()))
				}));

				assert_eq!(Value::get(), 3);
				assert_eq!(Map::get("val1"), 3);
				assert_eq!(Map::get("val2"), 3);
				assert_eq!(Map::get("val3"), 3);

				Rollback(Err("revert".into()))
			}),
			"revert"
		);

		assert_eq!(Value::get(), 1);
		assert_eq!(Map::get("val1"), 1);
		assert_eq!(Map::get("val2"), 0);
		assert_eq!(Map::get("val3"), 0);
	});
}

#[test]
fn transactional_annotation() {
	type Value = pallet::Value<Runtime>;

	fn set_value(v: u32) -> DispatchResult {
		Value::set(v);
		Ok(())
	}

	#[transactional]
	fn value_commits(v: u32) -> Result<u32, &'static str> {
		set_value(v)?;
		Ok(v)
	}

	#[transactional]
	fn value_rollbacks(v: u32) -> Result<u32, &'static str> {
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
