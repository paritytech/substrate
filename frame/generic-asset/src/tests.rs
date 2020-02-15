// Copyright 2019-2020
//     by  Centrality Investments Ltd.
//     and Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the module.

#![cfg(test)]

use super::*;
use crate::mock::{new_test_ext, ExtBuilder, GenericAsset, Origin, System, Test, TestEvent};
use frame_support::{assert_noop, assert_ok};

#[test]
fn issuing_asset_units_to_issuer_should_work() {
	let balance = 100;

	ExtBuilder::default().free_balance((16000, 1, 100)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};

		let expected_balance = balance;

		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: balance,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::free_balance(&16000, &1), expected_balance);
	});
}

#[test]
fn issuing_with_next_asset_id_overflow_should_not_work() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		NextAssetId::<Test>::put(u32::max_value());
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_noop!(
			GenericAsset::create(
				Origin::signed(1),
				AssetOptions {
					initial_issuance: 1,
					permissions: default_permission
				}
			),
			Error::<Test>::NoIdAvailable
		);
		assert_eq!(GenericAsset::next_asset_id(), u32::max_value());
	});
}

#[test]
fn querying_total_supply_should_work() {
	let asset_id = 1000;

	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: 100,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 100);
		assert_ok!(GenericAsset::transfer(Origin::signed(1), asset_id, 2, 50));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 50);
		assert_eq!(GenericAsset::free_balance(&asset_id, &2), 50);
		assert_ok!(GenericAsset::transfer(Origin::signed(2), asset_id, 3, 31));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 50);
		assert_eq!(GenericAsset::free_balance(&asset_id, &2), 19);
		assert_eq!(GenericAsset::free_balance(&asset_id, &3), 31);
		assert_ok!(GenericAsset::transfer(Origin::signed(1), asset_id, 1, 1));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 50);
	});
}

// Given
// - The next asset id as `asset_id` = 1000.
// - AssetOptions with all permissions.
// - GenesisStore has sufficient free balance.
//
// When
// - Create an asset from `origin` as 1.
// Then
// - free_balance of next asset id = 100.
//
// When
// - After transferring 40 from account 1 to account 2.
// Then
// - Origin account's `free_balance` = 60.
// - account 2's `free_balance` = 40.
#[test]
fn transferring_amount_should_work() {
	let asset_id = 1000;
	let free_balance = 100;
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: free_balance,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), free_balance);
		assert_ok!(GenericAsset::transfer(Origin::signed(1), asset_id, 2, 40));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 60);
		assert_eq!(GenericAsset::free_balance(&asset_id, &2), 40);
	});
}

// Given
// - The next asset id as `asset_id` = 1000.
// - AssetOptions with all permissions.
// - GenesisStore has sufficient free balance.
//
// When
// - Create an asset from `origin` as 1.
// Then
// - free_balance of next asset id = 100.
//
// When
// - After transferring 40 from account 1 to account 2.
// Then
// - Origin account's `free_balance` = 60.
// - account 2's `free_balance` = 40.
#[test]
fn transferring_amount_should_fail_when_transferring_more_than_free_balance() {
	let asset_id = 1000;
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: 100,
				permissions: default_permission
			}
		));
		assert_noop!(
			GenericAsset::transfer(Origin::signed(1), asset_id, 2, 2000),
			Error::<Test>::InsufficientBalance
		);
	});
}

#[test]
fn transferring_less_than_one_unit_should_not_work() {
	let asset_id = 1000;

	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: 100,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 100);
		assert_noop!(
			GenericAsset::transfer(Origin::signed(1), asset_id, 2, 0),
			Error::<Test>::ZeroAmount
		);
	});
}

// Given
// - Next asset id as `asset_id` = 1000.
// - Sufficient free balance.
// - initial balance = 100.
// When
// - After performing a self transfer from account 1 to 1.
// Then
// - Should not throw any errors.
// - Free balance after self transfer should equal to the free balance before self transfer.
#[test]
fn self_transfer_should_fail() {
	let asset_id = 1000;
	let balance = 100;

	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: balance,
				permissions: default_permission
			}
		));

		let initial_free_balance = GenericAsset::free_balance(&asset_id, &1);
		assert_ok!(GenericAsset::transfer(Origin::signed(1), asset_id, 1, 10));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), initial_free_balance);
	});
}

#[test]
fn transferring_more_units_than_total_supply_should_not_work() {
	let asset_id = 1000;
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: 100,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::free_balance(&asset_id, &1), 100);
		assert_noop!(
			GenericAsset::transfer(Origin::signed(1), asset_id, 2, 101),
			Error::<Test>::InsufficientBalance
		);
	});
}

// Ensures it uses fake money for staking asset id.
#[test]
fn staking_asset_id_should_return_0() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(GenericAsset::staking_asset_id(), 16000);
	});
}

// Ensures it uses fake money for spending asset id.
#[test]
fn spending_asset_id_should_return_10() {
	ExtBuilder::default().build().execute_with(|| {
		assert_eq!(GenericAsset::spending_asset_id(), 16001);
	});
}

// Given
// -Â Free balance is 0 and the reserved balance is 0.
// Then
// -Â total_balance should return 0
#[test]
fn total_balance_should_be_zero() {
	new_test_ext().execute_with(|| {
		assert_eq!(GenericAsset::total_balance(&0, &0), 0);
	});
}

// Given
// -Â Free balance is 0 and the reserved balance > 0.
// When
// - After calling total_balance.
// Then
// -Â total_balance should equals to reserved balance.
#[test]
fn total_balance_should_be_equal_to_account_balance() {
	let default_permission = PermissionLatest {
		update: Owner::Address(1),
		mint: Owner::Address(1),
		burn: Owner::Address(1),
	};
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		assert_ok!(GenericAsset::create(
			Origin::signed(1),
			AssetOptions {
				initial_issuance: 100,
				permissions: default_permission
			}
		));
		assert_eq!(GenericAsset::total_balance(&1000, &1), 100);
	});
}

// Given
// - An account presents with AccountId = 1
// -Â free_balance > 0.
// - reserved_balance = 50.
// When
// - After calling free_balance.
// Then
// -Â free_balance should return 50.
#[test]
fn free_balance_should_only_return_account_free_balance() {
	ExtBuilder::default().free_balance((1, 0, 50)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 70);
		assert_eq!(GenericAsset::free_balance(&1, &0), 50);
	});
}

// Given
// - An account presents with AccountId = 1.
// -Â Free balance > 0 and the reserved balance > 0.
// When
// - After calling total_balance.
// Then
// -Â total_balance should equals to account balance + free balance.
#[test]
fn total_balance_should_be_equal_to_sum_of_account_balance_and_free_balance() {
	ExtBuilder::default().free_balance((1, 0, 50)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 70);
		assert_eq!(GenericAsset::total_balance(&1, &0), 120);
	});
}

// Given
// -Â free_balance > 0.
// - reserved_balance = 70.
// When
// - After calling reserved_balance.
// Then
// - reserved_balance should return 70.
#[test]
fn reserved_balance_should_only_return_account_reserved_balance() {
	ExtBuilder::default().free_balance((1, 0, 50)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 70);
		assert_eq!(GenericAsset::reserved_balance(&1, &0), 70);
	});
}

// Given
// - A valid account presents.
// - Initial reserved_balance = 0
// When
// - After calls set_reserved_balance
// Then
// - Should persists the amount as reserved_balance.
// - reserved_balance = amount
#[test]
fn set_reserved_balance_should_add_balance_as_reserved() {
	ExtBuilder::default().build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 50);
		assert_eq!(GenericAsset::reserved_balance(&1, &0), 50);
	});
}

// Given
// - A valid account presents.
// - Initial free_balance = 100.
// When
// - After calling set_free_balance.
// Then
// - Should persists the amount as free_balance.
// - New free_balance should replace older free_balance.
#[test]
fn set_free_balance_should_add_amount_as_free_balance() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_free_balance(&1, &0, 50);
		assert_eq!(GenericAsset::free_balance(&1, &0), 50);
	});
}

// Given
// - free_balance is greater than the account balance.
// - free_balance = 100
// - reserved_balance = 0
// - reserve amount = 70
// When
// - After calling reserve
// Then
// - Funds should be removed from the account.
// - new free_balance = original free_balance - reserved amount
// - new reserved_balance = original free balance + reserved amount
#[test]
fn reserve_should_moves_amount_from_balance_to_reserved_balance() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		assert_ok!(GenericAsset::reserve(&1, &0, 70));
		assert_eq!(GenericAsset::free_balance(&1, &0), 30);
		assert_eq!(GenericAsset::reserved_balance(&1, &0), 70);
	});
}

// Given
// - Free balance is lower than the account balance.
// - free_balance = 100
// - reserved_balance = 0
// - reserve amount = 120
// When
// - After calling reverse function.
// Then
// - Funds should not be removed from the account.
// - Should throw an error.
#[test]
fn reserve_should_not_moves_amount_from_balance_to_reserved_balance() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		assert_noop!(GenericAsset::reserve(&1, &0, 120), Error::<Test>::InsufficientBalance);
		assert_eq!(GenericAsset::free_balance(&1, &0), 100);
		assert_eq!(GenericAsset::reserved_balance(&1, &0), 0);
	});
}

// Given
// - unreserved_amount > reserved_balance.
// - reserved_balance = 100.
// - free_balance = 100.
// - unreserved_amount = 120.
// When
// - After calling unreserve function.
// Then
// - unreserved should return 20.
#[test]
fn unreserve_should_return_subtracted_value_from_unreserved_amount_by_actual_account_balance() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::unreserve(&1, &0, 120), 20);
	});
}

// Given
// - unreserved_amount < reserved_balance.
// - reserved_balance = 100.
// - free_balance = 100.
// - unreserved_amount = 50.
// When
// - After calling unreserve function.
// Then
// - unreserved should return None.
#[test]
fn unreserve_should_return_none() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::unreserve(&1, &0, 50), 0);
	});
}

// Given
// - unreserved_amount > reserved_balance.
// - reserved_balance = 100.
// - free_balance = 100.
// - unreserved_amount = 120.
// When
// - After calling unreserve function.
// Then
// - free_balance should be 200.
#[test]
fn unreserve_should_increase_free_balance_by_reserved_balance() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		GenericAsset::unreserve(&1, &0, 120);
		assert_eq!(GenericAsset::free_balance(&1, &0), 200);
	});
}

// Given
// - unreserved_amount > reserved_balance.
// - reserved_balance = 100.
// - free_balance = 100.
// - unreserved_amount = 120.
// When
// - After calling unreserve function.
// Then
// - reserved_balance should be 0.
#[test]
fn unreserve_should_deduct_reserved_balance_by_reserved_amount() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_free_balance(&1, &0, 100);
		GenericAsset::unreserve(&1, &0, 120);
		assert_eq!(GenericAsset::reserved_balance(&1, &0), 0);
	});
}

// Given
// - slash amount < free_balance.
// - reserved_balance = 100.
// - free_balance = 100.
// - slash amount = 70.
// When
// - After calling slash function.
// Then
// - slash should return None.
#[test]
fn slash_should_return_slash_reserved_amount() {
	ExtBuilder::default().free_balance((1, 0, 100)).build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::slash(&1, &0, 70), None);
	});
}

// Given
// - slashed_amount > reserved_balance.
// When
// - After calling slashed_reverse function.
// Then
// - Should return slashed_reserved - reserved_balance.
#[test]
fn slash_reserved_should_deducts_up_to_amount_from_reserved_balance() {
	ExtBuilder::default().build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::slash_reserved(&1, &0, 150), Some(50));
	});
}

// Given
// - slashed_amount equals to reserved_amount.
// When
// - After calling slashed_reverse function.
// Then
// - Should return None.
#[test]
fn slash_reserved_should_return_none() {
	ExtBuilder::default().build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::slash_reserved(&1, &0, 100), None);
	});
}

// Given
// - reserved_balance = 100.
// - repatriate_reserved_amount > reserved_balance.
// When
// - After calling repatriate_reserved.
// Then
// - Should not return None.
#[test]
fn repatriate_reserved_return_amount_subtracted_by_slash_amount() {
	ExtBuilder::default().build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::repatriate_reserved(&1, &0, &1, 130, BalanceStatus::Free), 30);
	});
}

// Given
// - reserved_balance = 100.
// - repatriate_reserved_amount > reserved_balance.
// When
// - After calling repatriate_reserved.
// Then
// - Should return None.
#[test]
fn repatriate_reserved_return_none() {
	ExtBuilder::default().build().execute_with(|| {
		GenericAsset::set_reserved_balance(&1, &0, 100);
		assert_eq!(GenericAsset::repatriate_reserved(&1, &0, &1, 90, BalanceStatus::Free), 0);
	});
}

// Given
// - An asset with all permissions
// When
// - After calling `create_reserved` function.
// Then
// - Should create a new reserved asset.
#[test]
fn create_reserved_should_create_a_default_account_with_the_balance_given() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let default_permission = PermissionLatest {
			update: Owner::Address(1),
			mint: Owner::Address(1),
			burn: Owner::Address(1),
		};
		let options = AssetOptions {
			initial_issuance: 500,
			permissions: default_permission,
		};

		let expected_total_issuance = 500;
		let created_asset_id = 9;
		let created_account_id = 0;

		assert_ok!(GenericAsset::create_reserved(Origin::ROOT, created_asset_id, options));

		// Tests for side effects.
		assert_eq!(<TotalIssuance<Test>>::get(created_asset_id), expected_total_issuance);
		assert_eq!(
			<FreeBalance<Test>>::get(&created_asset_id, &created_account_id),
			expected_total_issuance
		);
	});
}

// Given
// - Origin is signed
// - Origin does not have minting permission
// When
// - After calling mint function
// Then
// - Should throw a permission error
#[test]
fn mint_should_throw_permission_error() {
	ExtBuilder::default().build().execute_with(|| {
		let origin = 1;
		let asset_id = 4;
		let to_account = 2;
		let amount = 100;

		assert_noop!(
			GenericAsset::mint(Origin::signed(origin), asset_id, to_account, amount),
			Error::<Test>::NoMintPermission,
		);
	});
}

// Given
// - Origin is signed.
// - Origin has permissions.
// When
// - After calling mint function
// Then
// - Should increase `to` free_balance.
// - Should not change `origins`  free_balance.
#[test]
fn mint_should_increase_asset() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let to_account = 2;
		let amount = 500;
		let initial_issuance = 100;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));

		assert_ok!(GenericAsset::mint(Origin::signed(origin), asset_id, to_account, amount));
		assert_eq!(GenericAsset::free_balance(&asset_id, &to_account), amount);

		// Origin's free_balance should not change.
		assert_eq!(GenericAsset::free_balance(&asset_id, &origin), initial_issuance);
	});
}

// Given
// - Origin is signed.
// - Origin does not have burning permission.
// When
// - After calling burn function.
// Then
// - Should throw a permission error.
#[test]
fn burn_should_throw_permission_error() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 4;
		let to_account = 2;
		let amount = 10;

		assert_noop!(
			GenericAsset::burn(Origin::signed(origin), asset_id, to_account, amount),
			Error::<Test>::NoBurnPermission,
		);
	});
}

// Given
// - Origin is signed.
// - Origin has permissions.
// When
// - After calling burn function
// Then
// - Should decrease `to`'s  free_balance.
// - Should not change `origin`'s  free_balance.
#[test]
fn burn_should_burn_an_asset() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let to_account = 2;
		let amount = 1000;
		let initial_issuance = 100;
		let burn_amount = 400;
		let expected_amount = 600;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));
		assert_ok!(GenericAsset::mint(Origin::signed(origin), asset_id, to_account, amount));

		assert_ok!(GenericAsset::burn(
			Origin::signed(origin),
			asset_id,
			to_account,
			burn_amount
		));
		assert_eq!(GenericAsset::free_balance(&asset_id, &to_account), expected_amount);
	});
}

// Given
// - `default_permission` with all privileges.
// - All permissions for origin.
// When
// - After executing create function and check_permission function.
// Then
// - The account origin should have burn, mint and update permissions.
#[test]
fn check_permission_should_return_correct_permission() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let initial_issuance = 100;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			},
		));

		assert!(GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Burn));
		assert!(GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Mint));
		assert!(GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Update));
	});
}

// Given
// - `default_permission` with no privileges.
// - No permissions for origin.
// When
// - After executing create function and check_permission function.
// Then
// - The account origin should not have burn, mint and update permissions.
#[test]
fn check_permission_should_return_false_for_no_permission() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let initial_issuance = 100;

		let default_permission = PermissionLatest {
			update: Owner::None,
			mint: Owner::None,
			burn: Owner::None,
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));

		assert!(!GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Burn));
		assert!(!GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Mint));
		assert!(!GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Update));
	});
}

// Given
// - `default_permission` only with update.
// When
// - After executing update_permission function.
// Then
// - The account origin should not have the burn permission.
// - The account origin should have update and mint permissions.
#[test]
fn update_permission_should_change_permission() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let initial_issuance = 100;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::None,
			burn: Owner::None,
		};

		let new_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::None,
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));

		assert_ok!(GenericAsset::update_permission(
			Origin::signed(origin),
			asset_id,
			new_permission,
		));
		assert!(GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Mint));
		assert!(!GenericAsset::check_permission(&asset_id, &origin, &PermissionType::Burn));
	});
}

// Given
// - `default_permission` without any permissions.
// When
// - After executing update_permission function.
// Then
// - Should throw an error stating "Origin does not have enough permission to update permissions."
#[test]
fn update_permission_should_throw_error_when_lack_of_permissions() {
	ExtBuilder::default().free_balance((16000, 1, 100000)).build().execute_with(|| {
		let origin = 1;
		let asset_id = 1000;
		let initial_issuance = 100;

		let default_permission = PermissionLatest {
			update: Owner::None,
			mint: Owner::None,
			burn: Owner::None,
		};

		let new_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::None,
		};

		assert_ok!(GenericAsset::create(
			Origin::signed(origin),
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			},
		));

		assert_noop!(
			GenericAsset::update_permission(Origin::signed(origin), asset_id, new_permission),
			Error::<Test>::NoUpdatePermission,
		);
	});
}

// Given
// - `asset_id` provided.
// - `from_account` is present.
// - All permissions for origin.
// When
// - After calling create_asset.
// Then
// - Should create a reserved token with provided id.
// - NextAssetId doesn't change.
// - TotalIssuance must equal to initial issuance.
// - FreeBalance must equal to initial issuance for the given account.
// - Permissions must have burn, mint and updatePermission for the given asset_id.
#[test]
fn create_asset_works_with_given_asset_id_and_from_account() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let origin = 1;
		let from_account: Option<<Test as frame_system::Trait>::AccountId> = Some(1);

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};
		let expected_permission = PermissionVersions::V1(default_permission.clone());
		let asset_id = 9;
		let initial_issuance = 100;

		assert_ok!(GenericAsset::create_asset(
			Some(asset_id),
			from_account,
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission.clone()
			}
		));

		// Test for side effects.
		assert_eq!(<NextAssetId<Test>>::get(), 10);
		assert_eq!(<TotalIssuance<Test>>::get(asset_id), initial_issuance);
		assert_eq!(<FreeBalance<Test>>::get(&asset_id, &origin), initial_issuance);
		assert_eq!(<Permissions<Test>>::get(&asset_id), expected_permission);
	});
}

// Given
// - `asset_id` is an id for user generated assets.
// - Whatever other params.
// Then
// - `create_asset` should not work.
#[test]
fn create_asset_with_non_reserved_asset_id_should_not_work() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let origin = 1;
		let from_account: Option<<Test as frame_system::Trait>::AccountId> = Some(1);

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		let asset_id = 11;
		let initial_issuance = 100;

		assert_noop!(
			GenericAsset::create_asset(
				Some(asset_id),
				from_account,
				AssetOptions {
					initial_issuance,
					permissions: default_permission.clone()
				}
			),
			Error::<Test>::IdUnavailable,
		);
	});
}

// Given
// - `asset_id` is for reserved assets, but already taken.
// - Whatever other params.
// Then
// - `create_asset` should not work.
#[test]
fn create_asset_with_a_taken_asset_id_should_not_work() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let origin = 1;
		let from_account: Option<<Test as frame_system::Trait>::AccountId> = Some(1);

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		let asset_id = 9;
		let initial_issuance = 100;

		assert_ok!(GenericAsset::create_asset(
			Some(asset_id),
			from_account,
			AssetOptions {
				initial_issuance,
				permissions: default_permission.clone()
			}
		));
		assert_noop!(
			GenericAsset::create_asset(
				Some(asset_id),
				from_account,
				AssetOptions {
					initial_issuance,
					permissions: default_permission.clone()
				}
			),
			Error::<Test>::IdAlreadyTaken,
		);
	});
}

// Given
// - `asset_id` provided.
// - `from_account` is None.
// - All permissions for origin.
// When
// - After calling create_asset.
// Then
// - Should create a reserved token.
#[test]
fn create_asset_should_create_a_reserved_asset_when_from_account_is_none() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let origin = 1;
		let from_account: Option<<Test as frame_system::Trait>::AccountId> = None;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		let created_account_id = 0;
		let asset_id = 9;
		let initial_issuance = 100;

		assert_ok!(GenericAsset::create_asset(
			Some(asset_id),
			from_account,
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));

		// Test for a side effect.
		assert_eq!(
			<FreeBalance<Test>>::get(&asset_id, &created_account_id),
			initial_issuance
		);
	});
}

// Given
// - `asset_id` not provided.
// - `from_account` is None.
// - All permissions for origin.
// When
// - After calling create_asset.
// Then
// - Should create a user token.
// - `NextAssetId`'s get should return a new value.
// - Should not create a `reserved_asset`.
#[test]
fn create_asset_should_create_a_user_asset() {
	ExtBuilder::default().next_asset_id(10).build().execute_with(|| {
		let origin = 1;
		let from_account: Option<<Test as frame_system::Trait>::AccountId> = None;

		let default_permission = PermissionLatest {
			update: Owner::Address(origin),
			mint: Owner::Address(origin),
			burn: Owner::Address(origin),
		};

		let created_account_id = 0;
		let reserved_asset_id = 100000;
		let initial_issuance = 100;
		let created_user_asset_id = 10;

		assert_ok!(GenericAsset::create_asset(
			None,
			from_account,
			AssetOptions {
				initial_issuance: initial_issuance,
				permissions: default_permission
			}
		));

		// Test for side effects.
		assert_eq!(<FreeBalance<Test>>::get(&reserved_asset_id, &created_account_id), 0);
		assert_eq!(
			<FreeBalance<Test>>::get(&created_user_asset_id, &created_account_id),
			initial_issuance
		);
		assert_eq!(<TotalIssuance<Test>>::get(created_user_asset_id), initial_issuance);
	});
}

#[test]
fn update_permission_should_raise_event() {
	// Arrange
	let staking_asset_id = 16000;
	let asset_id = 1000;
	let origin = 1;
	let initial_balance = 1000;
	let permissions = PermissionLatest {
		update: Owner::Address(origin),
		mint: Owner::Address(origin),
		burn: Owner::Address(origin),
	};

	ExtBuilder::default()
		.next_asset_id(asset_id)
		.free_balance((staking_asset_id, origin, initial_balance))
		.build()
		.execute_with(|| {
			assert_ok!(GenericAsset::create(
				Origin::signed(origin),
				AssetOptions {
					initial_issuance: 0,
					permissions: permissions.clone(),
				}
			));

			// Act
			assert_ok!(GenericAsset::update_permission(
				Origin::signed(origin),
				asset_id,
				permissions.clone()
			));

			let expected_event = TestEvent::generic_asset(
				RawEvent::PermissionUpdated(asset_id, permissions.clone()),
			);
			// Assert
			assert!(System::events().iter().any(|record| record.event == expected_event));
		},
	);
}

#[test]
fn mint_should_raise_event() {
	// Arrange
	let staking_asset_id = 16000;
	let asset_id = 1000;
	let origin = 1;
	let initial_balance = 1000;
	let permissions = PermissionLatest {
		update: Owner::Address(origin),
		mint: Owner::Address(origin),
		burn: Owner::Address(origin),
	};
	let to = 2;
	let amount = 100;

	ExtBuilder::default()
		.next_asset_id(asset_id)
		.free_balance((staking_asset_id, origin, initial_balance))
		.build()
		.execute_with(|| {
			assert_ok!(GenericAsset::create(
				Origin::signed(origin),
				AssetOptions {
					initial_issuance: 0,
					permissions: permissions.clone(),
				},
			));

			// Act
			assert_ok!(GenericAsset::mint(Origin::signed(origin), asset_id, to, amount));

			let expected_event = TestEvent::generic_asset(RawEvent::Minted(asset_id, to, amount));

			// Assert
			assert!(System::events().iter().any(|record| record.event == expected_event));
		},
	);
}

#[test]
fn burn_should_raise_event() {
	// Arrange
	let staking_asset_id = 16000;
	let asset_id = 1000;
	let origin = 1;
	let initial_balance = 1000;
	let permissions = PermissionLatest {
		update: Owner::Address(origin),
		mint: Owner::Address(origin),
		burn: Owner::Address(origin),
	};
	let amount = 100;

	ExtBuilder::default()
		.next_asset_id(asset_id)
		.free_balance((staking_asset_id, origin, initial_balance))
		.build()
		.execute_with(|| {
			assert_ok!(GenericAsset::create(
				Origin::signed(origin),
				AssetOptions {
					initial_issuance: amount,
					permissions: permissions.clone(),
				},
			));

			// Act
			assert_ok!(GenericAsset::burn(Origin::signed(origin), asset_id, origin, amount));

			let expected_event = TestEvent::generic_asset(RawEvent::Burned(asset_id, origin, amount));

			// Assert
			assert!(System::events().iter().any(|record| record.event == expected_event));
		},
	);
}
