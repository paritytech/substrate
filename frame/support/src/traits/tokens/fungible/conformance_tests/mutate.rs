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

//! Conformance tests regarding the functionality of the `fungible` Mutate trait.
//!
//! TODO: Decouple these tests from balances and abstract them into a macro so that they can be
//! used by any pallet that implements the `fungible` Mutate trait.

// TODO: is making an assumption about existential deposits valid for the `fungible` trait?
// It is referenced in passing in some comments, but there are no default implementations
// that make use of it.

#[macro_export]
macro_rules! mutate_conformance_tests {
	($ext_builder:ident, $pallet:ident) => {
		use super::*;
		use frame_support::traits::tokens::{
			Fortitude::{self},
			Precision,
			Preservation::{self},
		};

		#[test]
		// TODO: Is this test required? We already have a test for `total_issuance` in the inspect
		// tests.
		fn mint_into_increases_total_issuance() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_eq!($pallet::total_issuance(), 0);
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!($pallet::total_issuance(), 100);
				assert_ok!($pallet::mint_into(&2, 100));
				assert_eq!($pallet::total_issuance(), 200);
				assert_ok!($pallet::mint_into(&2, 1));
				assert_eq!($pallet::total_issuance(), 201);
			});
		}

		#[test]
		fn mint_into_increases_account_balance() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_eq!($pallet::free_balance(&1), 0);
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!($pallet::free_balance(&1), 100);
				assert_ok!($pallet::mint_into(&2, 100));
				assert_eq!($pallet::free_balance(&2), 100);
				assert_ok!($pallet::mint_into(&2, 1));
				assert_eq!($pallet::free_balance(&2), 101);
			});
		}

		#[test]
		fn mint_into_callback_works() {
			// TODO: What is the best way to test that `done_mint_into` is called with the correct
			// parameters?
		}

		#[test]
		fn mint_into_returns_actual() {
			$ext_builder::default().build_and_execute_with(|| {
				// TODO: Does this test make too many assumptions about the implementing pallet?
				// e.g. what if they have a minimum mint amount of 100? or 1_000_000? What if there
				// is a maximum minting amount? These tests would fail, even though the pallet is
				// still conforming.
				assert_eq!($pallet::mint_into(&1, 1).unwrap(), 1);
				assert_eq!($pallet::mint_into(&1, 100_000).unwrap(), 100_000);
				assert_eq!($pallet::mint_into(&1, 0).unwrap(), 0);
			});
		}

		// TODO: Is this test required? We already have a test for `total_issuance` in the inspect
		// tests.
		#[test]
		fn burn_from_reduces_total_issuance() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!($pallet::total_issuance(), 100);
				assert_ok!($pallet::burn_from(&1, 50, Precision::BestEffort, Fortitude::Polite));
				assert_eq!($pallet::total_issuance(), 50);
				assert_ok!($pallet::burn_from(&1, 50, Precision::BestEffort, Fortitude::Polite));
				assert_eq!($pallet::total_issuance(), 0);
			});
		}

		#[test]
		fn burn_from_reduces_account_balance() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!($pallet::free_balance(&1), 100);
				assert_ok!($pallet::burn_from(&1, 50, Precision::BestEffort, Fortitude::Polite));
				assert_eq!($pallet::free_balance(&1), 50);
				assert_ok!($pallet::burn_from(&1, 0, Precision::BestEffort, Fortitude::Polite));
				assert_eq!($pallet::free_balance(&1), 50);
				assert_ok!($pallet::burn_from(&1, 50, Precision::BestEffort, Fortitude::Polite));
				assert_eq!($pallet::free_balance(&1), 0);
			});
		}

		#[test]
		fn burn_from_returns_actual() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!(
					$pallet::burn_from(&1, 1, Precision::BestEffort, Fortitude::Polite).unwrap(),
					1
				);
				assert_eq!(
					$pallet::burn_from(&1, 0, Precision::BestEffort, Fortitude::Polite).unwrap(),
					0
				);
				assert_eq!(
					$pallet::burn_from(&1, 100_000, Precision::BestEffort, Fortitude::Polite)
						.unwrap(),
					99
				);
			});
		}

		#[test]
		fn burn_from_precision_best_effort_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_eq!(
					$pallet::burn_from(&1, 101, Precision::BestEffort, Fortitude::Polite),
					Ok(100)
				);
				assert_eq!($pallet::free_balance(&1), 0);
			});
		}

		#[test]
		fn burn_from_precision_exact_works() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_noop!(
					$pallet::burn_from(&1, 101, Precision::Exact, Fortitude::Polite),
					// TODO: Is it making too much of an assumption that the implementing pallet
					// should implement the same Dispatch errors as in the default implementation?
					DispatchError::Token(TokenError::FundsUnavailable)
				);
			});
		}

		// Note regarding the lack of Fortitude tests: I don't think we can test them in a general
		// way, because we cannot make assumptions about the inner workings of reducible_balance.

		#[test]
		fn burn_from_callback_works() {
			// TODO: What is the best way to test that `done_burn_from` is called with the
			// correct parameters?
		}

		// Note regarding shelve/restore tests: I'm unsure what `suspend`/`resume` refer to or
		// how these methods are different to calling mint_into/burn_from.

		#[test]
		fn transfer_fails_insufficient_funds() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_noop!(
					<$pallet as fungible::Mutate<_>>::transfer(&1, &2, 101, Preservation::Protect),
					DispatchError::Arithmetic(ArithmeticError::Underflow)
				);
			});
		}

		#[test]
		fn transfer_fails_existential_deposit_requirement() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_noop!(
					<$pallet as fungible::Mutate<_>>::transfer(&1, &2, 5, Preservation::Protect),
					DispatchError::Token(TokenError::BelowMinimum)
				);
			});
		}

		// TODO: Unclear exactly what the difference is between Protect and Preserve, or if they
		// make sense without making assumptions about the implementing pallet.

		#[test]
		fn transfer_fails_preservation_protect() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_noop!(
					<$pallet as fungible::Mutate<_>>::transfer(&1, &2, 95, Preservation::Protect),
					DispatchError::Token(TokenError::NotExpendable)
				);
			});
		}

		#[test]
		fn transfer_fails_preservation_preserve() {
			$ext_builder::default().existential_deposit(10).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_noop!(
					<$pallet as fungible::Mutate<_>>::transfer(&1, &2, 95, Preservation::Preserve),
					DispatchError::Token(TokenError::NotExpendable)
				);
			});
		}

		#[test]
		fn transfer_fails_balance_below_minimum() {
			$ext_builder::default().existential_deposit(100).build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 1000));
				assert_noop!(
					<$pallet as fungible::Mutate<_>>::transfer(
						&1,
						&2,
						50,
						Preservation::Expendable
					),
					DispatchError::Token(TokenError::BelowMinimum)
				);
			});
		}

		#[test]
		fn transfer_to_exisitng_account_updates_balances() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_ok!($pallet::mint_into(&2, 100));
				assert_ok!(<$pallet as fungible::Mutate<_>>::transfer(
					&1,
					&2,
					25,
					Preservation::Expendable
				));
				assert_eq!($pallet::free_balance(&1), 75);
				assert_eq!($pallet::free_balance(&2), 125);
			});
		}

		#[test]
		fn transfer_to_new_account_updates_balances() {
			$ext_builder::default().build_and_execute_with(|| {
				assert_ok!($pallet::mint_into(&1, 100));
				assert_ok!(<$pallet as fungible::Mutate<_>>::transfer(
					&1,
					&2,
					25,
					Preservation::Expendable
				));
				assert_eq!($pallet::free_balance(&1), 75);
				assert_eq!($pallet::free_balance(&2), 25);
			});
		}
	};
}
