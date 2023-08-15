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

use sp_core::Get;

use super::{new_test_ext, BlockNumberFor, Config, Pallet, Runtime};
use crate::{
	assert_noop, assert_ok, parameter_types, storage::generator::StorageValue, Blake2_128Concat,
};

#[test]
fn storage_alias_works() {
	new_test_ext().execute_with(|| {
		#[crate::storage_alias]
		type GenericData2<T> =
			StorageMap<System, Blake2_128Concat, BlockNumberFor<T>, BlockNumberFor<T>>;

		assert_eq!(Pallet::<Runtime>::generic_data2(5), None);
		GenericData2::<Runtime>::insert(5, 5);
		assert_eq!(Pallet::<Runtime>::generic_data2(5), Some(5));

		/// Some random docs that ensure that docs are accepted
		#[crate::storage_alias]
		pub type GenericData<T> =
			StorageMap<Test2, Blake2_128Concat, BlockNumberFor<T>, BlockNumberFor<T>>;

		#[crate::storage_alias]
		pub type GenericDataPallet<T: Config> =
			StorageMap<Pallet<T>, Blake2_128Concat, BlockNumberFor<T>, BlockNumberFor<T>>;
	});
}

#[test]
fn storage_value_mutate_exists_should_work() {
	new_test_ext().execute_with(|| {
		#[crate::storage_alias]
		pub type Value = StorageValue<Test, u32>;

		assert!(!Value::exists());

		Value::mutate_exists(|v| *v = Some(1));
		assert!(Value::exists());
		assert_eq!(Value::get(), Some(1));

		// removed if mutated to `None`
		Value::mutate_exists(|v| *v = None);
		assert!(!Value::exists());
	});
}

#[test]
fn storage_value_try_mutate_exists_should_work() {
	new_test_ext().execute_with(|| {
		#[crate::storage_alias]
		pub type Value = StorageValue<Test, u32>;

		type TestResult = std::result::Result<(), &'static str>;

		assert!(!Value::exists());

		// mutated if `Ok`
		assert_ok!(Value::try_mutate_exists(|v| -> TestResult {
			*v = Some(1);
			Ok(())
		}));
		assert!(Value::exists());
		assert_eq!(Value::get(), Some(1));

		// no-op if `Err`
		assert_noop!(
			Value::try_mutate_exists(|v| -> TestResult {
				*v = Some(2);
				Err("nah")
			}),
			"nah"
		);
		assert_eq!(Value::get(), Some(1));

		// removed if mutated to`None`
		assert_ok!(Value::try_mutate_exists(|v| -> TestResult {
			*v = None;
			Ok(())
		}));
		assert!(!Value::exists());
	});
}

#[docify::export]
#[test]
fn verbatim_attribute() {
	new_test_ext().execute_with(|| {
		// Declare the alias that will use the verbatim identifier as prefix.
		#[crate::storage_alias(verbatim)]
		pub type Value = StorageValue<Test, u32>;

		// Check that it works as expected.
		Value::put(1);
		assert_eq!(1, Value::get().unwrap());

		// The prefix is the one we declared above.
		assert_eq!(&b"Test"[..], Value::module_prefix());
	});
}

#[docify::export]
#[test]
fn pallet_name_attribute() {
	new_test_ext().execute_with(|| {
		// Declare the alias that will use the pallet name as prefix.
		#[crate::storage_alias(pallet_name)]
		pub type Value<T: Config> = StorageValue<Pallet<T>, u32>;

		// Check that it works as expected.
		Value::<Runtime>::put(1);
		assert_eq!(1, Value::<Runtime>::get().unwrap());

		// The prefix is the pallet name. In this case the pallet name is `System` as declared in
		// `construct_runtime!`.
		assert_eq!(&b"System"[..], Value::<Runtime>::module_prefix());
	});
}

#[docify::export]
#[test]
fn dynamic_attribute() {
	new_test_ext().execute_with(|| {
		// First let's declare our prefix.
		//
		// It could be any type that, as long as it implements `Get<&'static str>`.
		parameter_types! {
			pub Prefix: &'static str = "Hello";
		}

		// Declare the alias that will use the dynamic `Get` as prefix.
		#[crate::storage_alias(dynamic)]
		pub type Value<T: Get<&'static str>> = StorageValue<T, u32>;

		// Check that it works as expected.
		Value::<Prefix>::put(1);
		assert_eq!(1, Value::<Prefix>::get().unwrap());

		// The prefix is the one we declared above.
		assert_eq!(&b"Hello"[..], Value::<Prefix>::module_prefix());
	});
}

#[docify::export]
#[test]
fn storage_alias_guess() {
	new_test_ext().execute_with(|| {
		// The macro will use `Test` as prefix.
		#[crate::storage_alias]
		pub type Value = StorageValue<Test, u32>;

		assert_eq!(&b"Test"[..], Value::module_prefix());

		// The macro will use the pallet name as prefix.
		#[crate::storage_alias]
		pub type PalletValue<T: Config> = StorageValue<Pallet<T>, u32>;

		assert_eq!(&b"System"[..], PalletValue::<Runtime>::module_prefix());
	});
}

#[test]
fn dynamic_attribute_without_generics_works() {
	new_test_ext().execute_with(|| {
		parameter_types! {
			pub Prefix: &'static str = "Hello";
		}

		#[crate::storage_alias(dynamic)]
		pub type Value = StorageValue<Prefix, u32>;

		Value::put(1);
		assert_eq!(1, Value::get().unwrap())
	});
}
