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

//! The crate's tests.

use super::*;
use crate::pallet as pallet_asset_rate;
use frame_support::{assert_noop, assert_ok};
use mock::{new_test_ext, AssetRate, RuntimeOrigin, Test};
use sp_runtime::FixedU128;

const ASSET_ID: u32 = 42;

#[test]
fn create_works() {
	new_test_ext().execute_with(|| {
		assert!(pallet_asset_rate::ConversionRateToNative::<Test>::get(ASSET_ID).is_none());
		assert_ok!(AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.1)));

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<Test>::get(ASSET_ID),
			Some(FixedU128::from_float(0.1))
		);
	});
}

#[test]
fn create_existing_throws() {
	new_test_ext().execute_with(|| {
		assert!(pallet_asset_rate::ConversionRateToNative::<Test>::get(ASSET_ID).is_none());
		assert_ok!(AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.1)));

		assert_noop!(
			AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.1)),
			Error::<Test>::AlreadyExists
		);
	});
}

#[test]
fn remove_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.1)));

		assert_ok!(AssetRate::remove(RuntimeOrigin::root(), ASSET_ID,));
		assert!(pallet_asset_rate::ConversionRateToNative::<Test>::get(ASSET_ID).is_none());
	});
}

#[test]
fn remove_unknown_throws() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			AssetRate::remove(RuntimeOrigin::root(), ASSET_ID,),
			Error::<Test>::UnknownAssetId
		);
	});
}

#[test]
fn update_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.1)));
		assert_ok!(AssetRate::update(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.5)));

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<Test>::get(ASSET_ID),
			Some(FixedU128::from_float(0.5))
		);
	});
}

#[test]
fn update_unknown_throws() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			AssetRate::update(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(0.5)),
			Error::<Test>::UnknownAssetId
		);
	});
}

#[test]
fn convert_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(AssetRate::create(RuntimeOrigin::root(), ASSET_ID, FixedU128::from_float(2.51)));

		let conversion = <AssetRate as ConversionFromAssetBalance<
			BalanceOf<Test>,
			<Test as pallet_asset_rate::Config>::AssetId,
			BalanceOf<Test>,
		>>::from_asset_balance(10, ASSET_ID);
		assert_eq!(conversion.expect("Conversion rate exists for asset"), 25);
	});
}

#[test]
fn convert_unknown_throws() {
	new_test_ext().execute_with(|| {
		let conversion = <AssetRate as ConversionFromAssetBalance<
			BalanceOf<Test>,
			<Test as pallet_asset_rate::Config>::AssetId,
			BalanceOf<Test>,
		>>::from_asset_balance(10, ASSET_ID);
		assert!(conversion.is_err());
	});
}
