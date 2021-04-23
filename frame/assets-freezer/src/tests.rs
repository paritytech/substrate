// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for Assets Freezer pallet.

use super::*;
use crate::{Error, mock::*};
use sp_runtime::TokenError;
use frame_support::{assert_ok, assert_noop, traits::Currency};
use pallet_balances::Error as BalancesError;

fn last_event() -> mock::Event {
	frame_system::Pallet::<Test>::events().pop().expect("Event expected").event
}

#[test]
fn basic_minting_should_work() {
	new_test_ext().execute_with(|| {
		// assert_ok!(Assets::force_create(Origin::root(), 0, 1, true, 1));
		// assert_ok!(Assets::mint(Origin::signed(1), 0, 1, 100));
		// assert_eq!(Assets::balance(0, 1), 100);
		// assert_ok!(AssetsFreezer::set_total_issuance(Origin::signed(1), 0, 2, 100));
		// assert_eq!(AssetsFreezer::balance(0, 2), 100);
	});
}