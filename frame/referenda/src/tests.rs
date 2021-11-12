// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use codec::Decode;
use frame_support::{assert_ok, traits::Contains, dispatch::RawOrigin};
use super::*;
use crate::mock::*;

#[test]
fn params_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(ReferendumCount::<Test>::get(), 0);
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 210);
	});
}

#[test]
fn basic_lifecycle_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Referenda::submit(
			Origin::signed(1),
			RawOrigin::Root.into(),
			set_balance_proposal_hash(1),
			AtOrAfter::At(10),
		));
		assert_eq!(ReferendumCount::<Test>::get(), 1);
		assert_ok!(Referenda::place_decision_deposit(Origin::signed(2), 0));
		run_to(6);
		//  Vote should now be deciding.
		assert_eq!(DecidingCount::<Test>::get(0), 1);
		set_tally(0, 100, 0);
		// Vote should now be confirming.
		run_to(8);
		// Vote should now have ended.
		assert_ok!(Referenda::refund_decision_deposit(Origin::signed(2), 0));
	});
}

#[test]
fn set_balance_proposal_is_correctly_filtered_out() {
	for i in 0..10 {
		let call = crate::mock::Call::decode(&mut &set_balance_proposal(i)[..]).unwrap();
		assert!(!<Test as frame_system::Config>::BaseCallFilter::contains(&call));
	}
}
