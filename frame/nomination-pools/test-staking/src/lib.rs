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

#![cfg(test)]

mod mock;

use frame_support::{assert_ok, traits::Currency};
use mock::*;

#[test]
fn pool_lifecycle_e2e() {
	new_test_ext().execute_with(|| {
		Balances::make_free_balance_be(&10, 100);

		assert_ok!(Staking::set_staking_configs(
			Origin::root(),
			pallet_staking::ConfigOp::Set(10), // minimum nominator bond
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
			pallet_staking::ConfigOp::Noop,
		));

		assert_ok!(Pools::create(Origin::signed(10), 50, 10, 10, 10));
	})
}
