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
use frame_support::traits::Contains;
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
fn set_balance_proposal_is_correctly_filtered_out() {
	for i in 0..10 {
		let call = crate::mock::Call::decode(&mut &set_balance_proposal(i)[..]).unwrap();
		assert!(!<Test as frame_system::Config>::BaseCallFilter::contains(&call));
	}
}
