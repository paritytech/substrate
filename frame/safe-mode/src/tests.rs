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
		// TODO add exhaustive checks for all calls. Good idea, but keep it simple for a first version
	});
}

#[test]
fn root_can_enable() {
	new_test_ext().execute_with(|| {
		assert_ok!(SafeMode::force_enable(Origin::root()));
		assert_eq!(SafeMode::enabled().unwrap(), System::block_number() + 1); // TODO read mock::EnableDuration instead of hard coded? Yes please
	});
}

#[test]
fn root_can_disable() {
	new_test_ext().execute_with(|| {
		assert_eq!(SafeMode::enabled(), None);
		assert_err!(SafeMode::force_disable(Origin::root()), Error::<Test>::IsDisabled);
	});
}
