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

use super::*;
use frame_support::traits::fungible::conformance_tests;

// TODO: Add a macro to the conformance tests to generate all of these tests

#[test]
fn mint_into_success() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::mint_into_success::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn mint_into_overflow() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::mint_into_overflow::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn mint_into_done_mint_into() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::mint_into_done_mint_into::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn burn_from_exact_success() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::burn_from_exact_success::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn burn_from_best_effort_success() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::burn_from_best_effort_success::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn burn_from_exact_insufficient_funds() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::burn_from_exact_insufficient_funds::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn restore_success() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::restore_success::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn restore_overflow() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::restore_overflow::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn restore_done_restore() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::restore_done_restore::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn shelve_success() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::shelve_success::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}

#[test]
fn shelve_insufficient_funds() {
	ExtBuilder::default().build_and_execute_with(|| {
		conformance_tests::mutate::shelve_insufficient_funds::<
			Balances,
			<Test as frame_system::Config>::AccountId,
			<Test as pallet_balances::Config>::Balance,
		>();
	});
}
