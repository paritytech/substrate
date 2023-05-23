// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

use frame_support::{assert_err, assert_noop, assert_ok, weights::constants::*};

#[test]
fn initialize_pallet_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(TrashData::<Test>::get(0), None);

		assert_noop!(
			Glutton::initialize_pallet(RuntimeOrigin::signed(1), 3, None),
			DispatchError::BadOrigin
		);
		assert_noop!(
			Glutton::initialize_pallet(RuntimeOrigin::none(), 3, None),
			DispatchError::BadOrigin
		);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 2, None));
		System::assert_last_event(Event::PalletInitialized { reinit: false }.into());
		assert_err!(
			Glutton::initialize_pallet(RuntimeOrigin::root(), 2, None),
			Error::<Test>::AlreadyInitialized
		);

		assert_eq!(TrashData::<Test>::get(0), Some(Pallet::<Test>::gen_value(0)));
		assert_eq!(TrashData::<Test>::get(1), Some(Pallet::<Test>::gen_value(1)));
		assert_eq!(TrashData::<Test>::get(2), None);

		assert_eq!(TrashDataCount::<Test>::get(), 2);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 20, Some(2)));

		assert_eq!(TrashDataCount::<Test>::get(), 20);
		assert_eq!(TrashData::<Test>::iter_keys().count(), 20);
	});
}

#[test]
fn expand_and_shrink_trash_data_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(TrashDataCount::<Test>::get(), 0);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 5000, None));
		assert_eq!(TrashDataCount::<Test>::get(), 5000);
		assert_eq!(TrashData::<Test>::iter_keys().count(), 5000);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 8000, Some(5000)));
		assert_eq!(TrashDataCount::<Test>::get(), 8000);
		assert_eq!(TrashData::<Test>::iter_keys().count(), 8000);

		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 6000, Some(8000)));
		assert_eq!(TrashDataCount::<Test>::get(), 6000);
		assert_eq!(TrashData::<Test>::iter_keys().count(), 6000);

		assert_noop!(
			Glutton::initialize_pallet(RuntimeOrigin::root(), 0, None),
			Error::<Test>::AlreadyInitialized
		);
		assert_ok!(Glutton::initialize_pallet(RuntimeOrigin::root(), 0, Some(6000)));
		assert_eq!(TrashDataCount::<Test>::get(), 0);
		assert_eq!(TrashData::<Test>::iter_keys().count(), 0);
	});
}

#[test]
fn setting_compute_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Compute::<Test>::get(), Perbill::from_percent(0));

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
		assert_eq!(Storage::<Test>::get(), Perbill::from_percent(0));

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

		Glutton::on_idle(1, Weight::from_parts(20_000_000, 0));
	});
}

/// Check that the expected is close enough to the consumed weight.
#[test]
fn on_idle_weight_high_proof_is_close_enough_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Glutton::set_compute(RuntimeOrigin::root(), Perbill::from_percent(100)));
		assert_ok!(Glutton::set_storage(RuntimeOrigin::root(), Perbill::from_percent(100)));

		let should = Weight::from_parts(WEIGHT_REF_TIME_PER_SECOND, WEIGHT_PROOF_SIZE_PER_MB * 5);
		let got = Glutton::on_idle(1, should);
		assert!(got.all_lte(should), "Consumed too much weight");

		let ratio = Perbill::from_rational(got.proof_size(), should.proof_size());
		assert!(
			ratio >= Perbill::from_percent(99),
			"Too few proof size consumed, was only {:?} of expected",
			ratio
		);

		let ratio = Perbill::from_rational(got.ref_time(), should.ref_time());
		assert!(
			ratio >= Perbill::from_percent(99),
			"Too few ref time consumed, was only {:?} of expected",
			ratio
		);
	});
}

#[test]
fn on_idle_weight_low_proof_is_close_enough_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Glutton::set_compute(RuntimeOrigin::root(), Perbill::from_percent(100)));
		assert_ok!(Glutton::set_storage(RuntimeOrigin::root(), Perbill::from_percent(100)));

		let should = Weight::from_parts(WEIGHT_REF_TIME_PER_SECOND, WEIGHT_PROOF_SIZE_PER_KB * 20);
		let got = Glutton::on_idle(1, should);
		assert!(got.all_lte(should), "Consumed too much weight");

		let ratio = Perbill::from_rational(got.proof_size(), should.proof_size());
		// Just a sanity check here.
		assert!(
			ratio >= Perbill::from_percent(50),
			"Too few proof size consumed, was only {:?} of expected",
			ratio
		);

		let ratio = Perbill::from_rational(got.ref_time(), should.ref_time());
		assert!(
			ratio >= Perbill::from_percent(99),
			"Too few ref time consumed, was only {:?} of expected",
			ratio
		);
	});
}

#[test]
fn waste_at_most_ref_time_weight_close_enough() {
	new_test_ext().execute_with(|| {
		let mut meter =
			WeightMeter::from_limit(Weight::from_parts(WEIGHT_REF_TIME_PER_SECOND, u64::MAX));
		// Over-spending fails defensively.
		Glutton::waste_at_most_ref_time(&mut meter);

		// We require it to be under-spend by at most 1%.
		assert!(
			meter.consumed_ratio() >= Perbill::from_percent(99),
			"Consumed too few: {:?}",
			meter.consumed_ratio()
		);
	});
}

#[test]
fn waste_at_most_proof_size_weight_close_enough() {
	new_test_ext().execute_with(|| {
		let mut meter =
			WeightMeter::from_limit(Weight::from_parts(u64::MAX, WEIGHT_PROOF_SIZE_PER_MB * 5));
		// Over-spending fails defensively.
		Glutton::waste_at_most_proof_size(&mut meter);

		// We require it to be under-spend by at most 1%.
		assert!(
			meter.consumed_ratio() >= Perbill::from_percent(99),
			"Consumed too few: {:?}",
			meter.consumed_ratio()
		);
	});
}

#[test]
fn gen_value_works() {
	let g0 = Pallet::<Test>::gen_value(0);
	let g1 = Pallet::<Test>::gen_value(1);

	assert_eq!(g0.len(), VALUE_SIZE);
	assert_ne!(g0, g1, "Is distinct");
	assert_ne!(g0, [0; VALUE_SIZE], "Is not zero");
	assert_eq!(g0, Pallet::<Test>::gen_value(0), "Is deterministic");
}
