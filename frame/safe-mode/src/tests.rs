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

//! Test utilities for the safe mode pallet.

use super::*;
use crate::mock::*;

use frame_support::{assert_err, assert_noop, assert_ok};

#[test]
fn disable_fails_if_not_enabled() {
	new_test_ext().execute_with(|| {
		assert_noop!(SafeMode::force_disable(Origin::root()), Error::<Test>::IsDisabled);
		// TODO add exhaustive checks for all calls. Good idea, but keep it simple for a first
		// version
	});
}

#[test]
fn root_can_force_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		); // TODO read mock::EnableDuration instead of hard coded? Yes please
		assert_noop!(SafeMode::force_enable(Origin::root()), Error::<Test>::IsEnabled);
	});
}

#[test]
fn root_can_force_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		);
		assert_ok!(SafeMode::force_extend(Origin::root()));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
		);
	});
}

#[test]
fn root_can_force_disable() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_err!(SafeMode::force_disable(Origin::root()), Error::<Test>::IsDisabled);
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_ok!(SafeMode::force_disable(Origin::root()));
	});
}

#[test]
fn signed_origin_can_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get()
		); // TODO read mock::EnableDuration instead of hard coded throughout this fn
		assert_noop!(SafeMode::enable(Origin::signed(1)), Error::<Test>::IsEnabled); // TODO check stake
		                                                                     // reserved along the
		                                                                     // way.
	});
}

#[test]
fn signed_origin_can_extend() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::enable(Origin::signed(1)));
		assert_ok!(SafeMode::extend(Origin::signed(2)));
		assert_eq!(
			SafeMode::enabled().unwrap(),
			System::block_number() + mock::EnableDuration::get() + mock::ExtendDuration::get()
		); // TODO read mock::EnableDuration instead of hard coded throughout this fn
	});
}

#[test]
fn extend_fails_if_not_enabled() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_noop!(SafeMode::extend(Origin::signed(2)), Error::<Test>::IsDisabled);
	});
}

#[test]
fn automatically_disable_after_timeout() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		run_to(mock::EnableDuration::get() + 2); // Enabled at block 1, so duration +1, and +1 additional block before hook will catch
		SafeMode::on_initialize(System::block_number());
		assert_eq!(SafeMode::enabled(), None);
	});
}
