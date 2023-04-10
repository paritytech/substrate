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
use frame_support::traits::fungible::{conformance_tests, Inspect, Mutate};
use paste::paste;

macro_rules! generate_test {
    ($parent_module:tt :: $child_module:tt, $ext_deposit:expr, $dust_trap:expr, $name:ident) => {
		paste! {
			#[test]
			fn [< $name _ext_deposit_ $ext_deposit _dust_trap_ $dust_trap >]() {
				let (trap_account, builder) = match $dust_trap {
					"on" => {
						let trap_account = <Test as frame_system::Config>::AccountId::from(65174286u64);
						let builder = ExtBuilder::default().existential_deposit($ext_deposit).dust_trap(trap_account);
						(Some(trap_account), builder)
					},
					"off" => {
						let builder = ExtBuilder::default().existential_deposit($ext_deposit);
						(None, builder)
					},
					_ => panic!("dust_trap must be either \"on\" or \"off\"")
				};
				builder.build_and_execute_with(|| {
					// Initialise the trap account if it is being used
					if let Some(trap_account) = trap_account {
						Balances::set_balance(&trap_account, Balances::minimum_balance());
					};
					// Run the test
					$parent_module::$child_module::$name::<
						Balances,
						<Test as frame_system::Config>::AccountId,
						<Test as pallet_balances::Config>::Balance,
					>(trap_account);
				});
			}
		}
	}
}

macro_rules! run_tests {
	($parent_module:tt :: $child_module:tt, $ext_deposit:expr, $dust_trap:expr) => {
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, mint_into_success);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, mint_into_overflow);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			mint_into_below_minimum
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			mint_into_done_mint_into
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			burn_from_exact_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			burn_from_best_effort_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			burn_from_exact_insufficient_funds
		);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, restore_success);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, restore_overflow);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			restore_below_minimum
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			restore_done_restore
		);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, shelve_success);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			shelve_insufficient_funds
		);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, shelve_done_shelve);
		generate_test!($parent_module::$child_module, $ext_deposit, $dust_trap, transfer_success);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			transfer_expendable_all
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			transfer_expendable_dust
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			transfer_protect_preserve
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			transfer_done_transfer
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			set_balance_mint_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			set_balance_burn_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_deposit_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_deposit_below_minimum
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_deposit_overflow
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_withdraw_success
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_withdraw_reduced_to_zero
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			can_withdraw_balance_low
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			reducible_balance_expendable
		);
		generate_test!(
			$parent_module::$child_module,
			$ext_deposit,
			$dust_trap,
			reducible_balance_protect_preserve
		);
	};
}

run_tests!(conformance_tests::inspect_mutate, 1, "off");
run_tests!(conformance_tests::inspect_mutate, 1, "on");
run_tests!(conformance_tests::inspect_mutate, 2, "off");
run_tests!(conformance_tests::inspect_mutate, 2, "on");
run_tests!(conformance_tests::inspect_mutate, 5, "off");
run_tests!(conformance_tests::inspect_mutate, 5, "on");
run_tests!(conformance_tests::inspect_mutate, 1000, "off");
run_tests!(conformance_tests::inspect_mutate, 1000, "on");
