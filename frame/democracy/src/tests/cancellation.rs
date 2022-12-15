// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! The tests for cancelation functionality.

use super::*;

#[test]
fn cancel_referendum_should_work() {
	new_test_ext().execute_with(|| {
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal(2),
			VoteThreshold::SuperMajorityApprove,
			0,
		);
		assert_ok!(Democracy::vote(RuntimeOrigin::signed(1), r, aye(1)));
		assert_ok!(Democracy::cancel_referendum(RuntimeOrigin::root(), r.into()));
		assert_eq!(Democracy::lowest_unbaked(), 0);

		next_block();

		next_block();

		assert_eq!(Democracy::lowest_unbaked(), 1);
		assert_eq!(Democracy::lowest_unbaked(), Democracy::referendum_count());
		assert_eq!(Balances::free_balance(42), 0);
	});
}

#[test]
fn emergency_cancel_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal(2),
			VoteThreshold::SuperMajorityApprove,
			2,
		);
		assert!(Democracy::referendum_status(r).is_ok());

		assert_noop!(Democracy::emergency_cancel(RuntimeOrigin::signed(3), r), BadOrigin);
		assert_ok!(Democracy::emergency_cancel(RuntimeOrigin::signed(4), r));
		assert!(Democracy::referendum_info(r).is_none());

		// some time later...

		let r = Democracy::inject_referendum(
			2,
			set_balance_proposal(2),
			VoteThreshold::SuperMajorityApprove,
			2,
		);
		assert!(Democracy::referendum_status(r).is_ok());
		assert_noop!(
			Democracy::emergency_cancel(RuntimeOrigin::signed(4), r),
			Error::<Test>::AlreadyCanceled,
		);
	});
}
