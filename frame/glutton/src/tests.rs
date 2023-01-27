// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Tests for the glutton pallet.

use super::*;
use mock::{new_test_ext, Glutton, RuntimeOrigin, System, Test};

use frame_support::{assert_noop, assert_ok, weights::constants::*};

#[test]
fn initialize_pallet_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(TrashData::<Test>::get(0), None);

		assert_noop!(
			Glutton::initialize_pallet(RuntimeOrigin::signed(1), 3),
			DispatchError::BadOrigin
		);
		assert_noop!(
			Glutton::initialize_pallet(RuntimeOrigin::none(), 3),
			DispatchError::BadOrigin
		);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 2));

		assert_eq!(TrashData::<Test>::get(0), Some(0));
		assert_eq!(TrashData::<Test>::get(1), Some(1));
		assert_eq!(TrashData::<Test>::get(2), None);
	});
}

#[test]
fn setting_compute_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Compute::<Test>::get(), Perbill::from_percent(50));

		assert_ok!(Glutton::set_compute(RuntimeOrigin::root(), Perbill::from_percent(70)));
		assert_eq!(Compute::<Test>::get(), Perbill::from_percent(70));
		System::assert_last_event(
			Event::ComputationLimitSet { compute: Perbill::from_percent(70) }.into(),
		);

		assert_noop!(
			Glutton::set_compute(RuntimeOrigin::signed(1), Perbill::from_percent(30)),
			DispatchError::BadOrigin
		);
		assert_noop!(
			Glutton::set_compute(RuntimeOrigin::none(), Perbill::from_percent(30)),
			DispatchError::BadOrigin
		);
	});
}

#[test]
fn setting_storage_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Storage::<Test>::get(), Perbill::from_percent(50));

		assert_ok!(Glutton::set_storage(RuntimeOrigin::root(), Perbill::from_percent(30)));
		assert_eq!(Storage::<Test>::get(), Perbill::from_percent(30));
		System::assert_last_event(
			Event::StorageLimitSet { storage: Perbill::from_percent(30) }.into(),
		);

		assert_noop!(
			Glutton::set_storage(RuntimeOrigin::signed(1), Perbill::from_percent(90)),
			DispatchError::BadOrigin
		);
		assert_noop!(
			Glutton::set_storage(RuntimeOrigin::none(), Perbill::from_percent(90)),
			DispatchError::BadOrigin
		);
	});
}

#[test]
fn on_idle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Glutton::set_compute(RuntimeOrigin::root(), Perbill::from_percent(100)));
		assert_ok!(Glutton::set_storage(RuntimeOrigin::root(), Perbill::from_percent(100)));

		Glutton::on_idle(1, Weight::from_ref_time(20_000_000));
	});
}

/// Check that the expected is close enough to the consumed weight.
#[test]
fn on_idle_weight_is_close_enough_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Glutton::set_compute(RuntimeOrigin::root(), Perbill::from_percent(100)));
		assert_ok!(Glutton::set_storage(RuntimeOrigin::root(), Perbill::from_percent(100)));

		let should = Weight::from_parts(WEIGHT_REF_TIME_PER_MILLIS * 20, WEIGHT_PROOF_SIZE_PER_MB);
		let got = Glutton::on_idle(1, should);
		assert!(got.all_lte(should), "Consumed too much weight");

		let ratio = Perbill::from_rational(got.proof_size(), should.proof_size());
		assert!(
			ratio >= Perbill::from_percent(95),
			"Too few proof size consumed, was only {:?} of expected",
			ratio
		);

		let ratio = Perbill::from_rational(got.ref_time(), should.ref_time());
		assert!(
			ratio >= Perbill::from_percent(95),
			"Too few ref time consumed, was only {:?} of expected",
			ratio
		);
	});
}
