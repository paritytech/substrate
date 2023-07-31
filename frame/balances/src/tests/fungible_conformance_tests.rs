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

use super::*;
use frame_support::traits::fungible::{conformance_tests, Inspect, Mutate};
use paste::paste;

macro_rules! generate_tests {
	// Match for tests what require testing with a dust trap
    ($base_path:path, regular, mutate, $ext_deposit:expr, $($test_name:ident),*) => {
		$(
			paste! {
				#[test]
				fn [<regular_mutate_ $test_name _existential_deposit_ $ext_deposit _dust_trap_on >]() {
					// Some random trap account.
					let trap_account = <Test as frame_system::Config>::AccountId::from(65174286u64);
					let builder = ExtBuilder::default().existential_deposit($ext_deposit).dust_trap(trap_account);
					builder.build_and_execute_with(|| {
						Balances::set_balance(&trap_account, Balances::minimum_balance());
						$base_path::regular::mutate::$test_name::<
							Balances,
							<Test as frame_system::Config>::AccountId,
						>(Some(trap_account));
					});
				}

				#[test]
				fn [< regular_mutate_ $test_name _existential_deposit_ $ext_deposit _dust_trap_off >]() {
					let builder = ExtBuilder::default().existential_deposit($ext_deposit);
					builder.build_and_execute_with(|| {
						$base_path::regular::mutate::$test_name::<
							Balances,
							<Test as frame_system::Config>::AccountId,
						>(None);
					});
				}
			}
		)*
	};
	// All other tests don't need testing with a dust trap
    ($base_path:path, $scope:expr, $trait:ident, $ext_deposit:expr, $($test_name:ident),*) => {
		$(
			paste! {
				#[test]
				fn [< $trait _ $scope _ $test_name _existential_deposit_ $ext_deposit>]() {
					let builder = ExtBuilder::default().existential_deposit($ext_deposit);
					builder.build_and_execute_with(|| {
						$base_path::$scope::$trait::$test_name::<
							Balances,
							<Test as frame_system::Config>::AccountId,
						>();
					});
				}
			}
		)*
	};
	($base_path:path, $ext_deposit:expr) => {
		generate_tests!(
			$base_path,
			regular,
			mutate,
			$ext_deposit,
			mint_into_success,
			mint_into_overflow,
			mint_into_below_minimum,
			burn_from_exact_success,
			burn_from_best_effort_success,
			burn_from_exact_insufficient_funds,
			restore_success,
			restore_overflow,
			restore_below_minimum,
			shelve_success,
			shelve_insufficient_funds,
			transfer_success,
			transfer_expendable_all,
			transfer_expendable_dust,
			transfer_protect_preserve,
			set_balance_mint_success,
			set_balance_burn_success,
			can_deposit_success,
			can_deposit_below_minimum,
			can_deposit_overflow,
			can_withdraw_success,
			can_withdraw_reduced_to_zero,
			can_withdraw_balance_low,
			reducible_balance_expendable,
			reducible_balance_protect_preserve
		);
		generate_tests!(
			$base_path,
			regular,
			unbalanced,
			$ext_deposit,
			write_balance,
			decrease_balance_expendable,
			decrease_balance_preserve,
			increase_balance,
			set_total_issuance,
			deactivate_and_reactivate
		);
		generate_tests!(
			$base_path,
			regular,
			balanced,
			$ext_deposit,
			issue_and_resolve_credit,
			rescind_and_settle_debt,
			deposit,
			withdraw,
			pair
		);
	};
}

generate_tests!(conformance_tests, 1);
generate_tests!(conformance_tests, 5);
generate_tests!(conformance_tests, 1000);
