// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Tests for Nft fractionalisation pallet.

use crate::{mock::*, Error};
use frame_support::{assert_noop, assert_ok, traits::Currency};

#[test]
fn address_is_set() {
	new_test_ext().execute_with(|| {
		// Dispatch a signed extrinsic.
		// assert_eq!(NftFractions::pallet_address(), None);
		// assert_ok!(NftFractions::set_pallet_address(RuntimeOrigin::signed(1)));
		// assert_eq!(NftFractions::pallet_address(), Some(1u64));
		// assert_eq!(
		// 	NftFractions::issuance(),
		// 	Some(<Balances as Currency<_>>::total_issuance())
		// )
	});
}
