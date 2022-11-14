// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Tests for the Timestamp module.

use crate::mock::*;
use frame_support::assert_ok;

#[test]
fn timestamp_works() {
	new_test_ext().execute_with(|| {
		Timestamp::set_timestamp(42);
		assert_ok!(Timestamp::set(Origin::none(), 69));
		assert_eq!(Timestamp::now(), 69);
		assert_eq!(Some(69), get_captured_moment());
	});
}

#[test]
#[should_panic(expected = "Timestamp must be updated only once in the block")]
fn double_timestamp_should_fail() {
	new_test_ext().execute_with(|| {
		Timestamp::set_timestamp(42);
		assert_ok!(Timestamp::set(Origin::none(), 69));
		let _ = Timestamp::set(Origin::none(), 70);
	});
}

#[test]
#[should_panic(
	expected = "Timestamp must increment by at least <MinimumPeriod> between sequential blocks"
)]
fn block_period_minimum_enforced() {
	new_test_ext().execute_with(|| {
		Timestamp::set_timestamp(42);
		let _ = Timestamp::set(Origin::none(), 46);
	});
}
