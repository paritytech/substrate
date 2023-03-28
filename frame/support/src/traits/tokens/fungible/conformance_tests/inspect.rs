// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
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

//! Conformance tests checking functionality of the `fungible` Inspect trait.
//!
//! TODO: Feels like these can be just rolled up into Mutable trait tests, cannot test Inspect
//! without Mutate being avaliable, and cannot think of a realistic scenario a pallet would
//! implement Inspect without Mutate.

#[macro_export]
macro_rules! inspect_conformance_tests {
	($ext_builder:ident, $pallet:ident) => {
		use super::*;
		use frame_support::traits::tokens::{
			Fortitude::{Force, Polite},
			Preservation::{Expendable, Preserve, Protect},
		};
		use fungible::{Inspect, Mutate, MutateFreeze};

		#[test]
		fn total_issuance_works() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_eq!($pallet::total_issuance(), 0);
				$pallet::set_balance(&1, 100);
				assert_eq!($pallet::total_issuance(), 100);
				$pallet::set_balance(&2, 100);
				assert_eq!($pallet::total_issuance(), 200);
				$pallet::set_balance(&2, 101);
				assert_eq!($pallet::total_issuance(), 201);
			});
		}

		#[test]
		fn active_issuance_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				// TODO: Is there an official definition for what it means for issuance to be
				// 'controlled by the system'? If there is no offical definition, then I think it
				// cannot be tested in a generic way and we should remove this test.
				assert!(true);
			});
		}

		#[test]
		fn minimum_balance_works() {
			$ext_builder::default().existential_deposit(5).build_and_execute_with(|| {
				assert_eq!($pallet::minimum_balance(), 5);
			});
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_eq!($pallet::minimum_balance(), 10);
			});
		}

		#[test]
		fn total_balance_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_eq!($pallet::total_balance(&1), 0);
				$pallet::set_balance(&1, 100);
				assert_eq!($pallet::total_balance(&1), 100);
				$pallet::set_balance(&2, 100);
				assert_eq!($pallet::total_balance(&2), 100);
				$pallet::set_balance(&2, 101);
				assert_eq!($pallet::total_balance(&2), 101);
			});
		}

		// TODO: Properly understand Preservation and Fortitude enums, and ensure every permutation
		// is thoroughly tested.
		#[test]
		fn reducible_balance_basic_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				$pallet::set_balance(&1, 100);
				assert_eq!($pallet::reducible_balance(&1, Expendable, Polite), 100);
				assert_eq!($pallet::reducible_balance(&1, Protect, Polite), 90);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Polite), 90);
				assert_eq!($pallet::reducible_balance(&1, Expendable, Force), 100);
				assert_eq!($pallet::reducible_balance(&1, Protect, Force), 90);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Force), 90);
			});
		}

		#[test]
		fn reducible_balance_other_provide_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				$pallet::set_balance(&1, 100);
				System::inc_providers(&1);
				assert_eq!($pallet::reducible_balance(&1, Expendable, Polite), 100);
				assert_eq!($pallet::reducible_balance(&1, Protect, Polite), 100);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Polite), 90);
				assert_eq!($pallet::reducible_balance(&1, Expendable, Force), 100);
				assert_eq!($pallet::reducible_balance(&1, Protect, Force), 100);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Force), 90);
			});
		}

		#[test]
		fn reducible_balance_frozen_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				$pallet::set_balance(&1, 100);
				assert_ok!($pallet::set_freeze(&TestId::Foo, &1, 50));
				assert_eq!($pallet::reducible_balance(&1, Expendable, Polite), 50);
				assert_eq!($pallet::reducible_balance(&1, Protect, Polite), 50);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Polite), 50);
				assert_eq!($pallet::reducible_balance(&1, Expendable, Force), 90);
				assert_eq!($pallet::reducible_balance(&1, Protect, Force), 90);
				assert_eq!($pallet::reducible_balance(&1, Preserve, Force), 90);
			});
		}

		#[test]
		fn can_deposit_works() {
			$ext_builder::default().build_and_execute_with(|| {
				// TODO
				assert!(true);
			});
		}

		#[test]
		fn can_deposit_withdraw_works() {
			$ext_builder::default().build_and_execute_with(|| {
				// TODO
				assert!(true);
			});
		}
	};
}
