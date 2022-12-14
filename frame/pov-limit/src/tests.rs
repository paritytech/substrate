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

//! Tests for pov-limit pallet.

use super::*;

use frame_support::{assert_noop, assert_ok};
use mock::{new_test_ext, PovLimit, RuntimeOrigin, Test};

#[test]
fn setting_compute_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Compute::<Test>::get(), Perbill::from_percent(50));

		assert_ok!(PovLimit::set_compute(RuntimeOrigin::root(), Perbill::from_percent(70)));

		assert_eq!(Compute::<Test>::get(), Perbill::from_percent(70));

		assert_noop!(
			PovLimit::set_compute(RuntimeOrigin::signed(1), Perbill::from_percent(30)),
			DispatchError::BadOrigin
		);
		assert_noop!(
			PovLimit::set_compute(RuntimeOrigin::none(), Perbill::from_percent(30)),
			DispatchError::BadOrigin
		);
	});
}

#[test]
fn setting_storage_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Storage::<Test>::get(), 10000);

		assert_ok!(PovLimit::set_storage(RuntimeOrigin::root(), 5000));

		assert_eq!(Storage::<Test>::get(), 5000);

		assert_noop!(
			PovLimit::set_storage(RuntimeOrigin::signed(1), 15000),
			DispatchError::BadOrigin
		);
		assert_noop!(PovLimit::set_storage(RuntimeOrigin::none(), 15000), DispatchError::BadOrigin);
	});
}

#[test]
fn on_idle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(PovLimit::set_compute(RuntimeOrigin::root(), Perbill::from_percent(100)));
		assert_ok!(PovLimit::set_storage(RuntimeOrigin::root(), 5000));

		PovLimit::on_idle(1, Weight::from_ref_time(20_000_000));
	});
}
