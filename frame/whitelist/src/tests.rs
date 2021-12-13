// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

// Tests for Whitelist Pallet

use crate::mock::*;
use codec::Encode;
use frame_support::{assert_err, assert_ok, dispatch::GetDispatchInfo, traits::PreimageProvider};
use sp_runtime::{traits::Hash, DispatchError};

#[test]
fn test_whitelist_call_and_remove() {
	new_test_ext().execute_with(|| {
		let call = Call::System(frame_system::Call::remark { remark: vec![] });
		let encoded_call = call.encode();
		let call_hash = <Test as frame_system::Config>::Hashing::hash(&encoded_call[..]);

		assert_err!(
			Whitelist::remove_whitelisted_call(Origin::root(), call_hash),
			crate::Error::<Test>::CallIsNotWhitelisted,
		);

		assert!(!Preimage::preimage_requested(&call_hash));

		assert_err!(
			Whitelist::whitelist_call(Origin::signed(1), call_hash),
			DispatchError::BadOrigin,
		);

		assert!(!Preimage::preimage_requested(&call_hash));

		assert_ok!(Whitelist::whitelist_call(Origin::root(), call_hash));

		assert!(Preimage::preimage_requested(&call_hash));

		assert_err!(
			Whitelist::whitelist_call(Origin::root(), call_hash),
			crate::Error::<Test>::CallAlreadyWhitelisted,
		);

		assert!(Preimage::preimage_requested(&call_hash));

		assert_err!(
			Whitelist::remove_whitelisted_call(Origin::signed(1), call_hash),
			DispatchError::BadOrigin,
		);

		assert!(Preimage::preimage_requested(&call_hash));

		assert_ok!(Whitelist::remove_whitelisted_call(Origin::root(), call_hash));

		assert!(!Preimage::preimage_requested(&call_hash));

		assert_err!(
			Whitelist::remove_whitelisted_call(Origin::root(), call_hash),
			crate::Error::<Test>::CallIsNotWhitelisted,
		);

		assert!(!Preimage::preimage_requested(&call_hash));
	});
}

#[test]
fn test_whitelist_call_and_execute() {
	new_test_ext().execute_with(|| {
		let call = Call::System(frame_system::Call::remark { remark: vec![] });
		let call_weight = call.get_dispatch_info().weight;
		let encoded_call = call.encode();
		let call_hash = <Test as frame_system::Config>::Hashing::hash(&encoded_call[..]);

		assert_err!(
			Whitelist::dispatch_whitelisted_call(Origin::root(), call_hash, call_weight),
			crate::Error::<Test>::CallIsNotWhitelisted,
		);

		assert_ok!(Whitelist::whitelist_call(Origin::root(), call_hash));

		assert_err!(
			Whitelist::dispatch_whitelisted_call(Origin::signed(1), call_hash, call_weight),
			DispatchError::BadOrigin,
		);

		assert_err!(
			Whitelist::dispatch_whitelisted_call(Origin::root(), call_hash, call_weight),
			crate::Error::<Test>::UnavailablePreImage,
		);

		assert_ok!(Preimage::note_preimage(Origin::root(), encoded_call));

		assert_err!(
			Whitelist::dispatch_whitelisted_call(Origin::root(), call_hash, call_weight - 1),
			crate::Error::<Test>::InvalidCallWeightWitness,
		);

		assert!(Preimage::preimage_requested(&call_hash));

		assert_ok!(Whitelist::dispatch_whitelisted_call(Origin::root(), call_hash, call_weight));

		assert!(!Preimage::preimage_requested(&call_hash));

		assert_err!(
			Whitelist::dispatch_whitelisted_call(Origin::root(), call_hash, call_weight),
			crate::Error::<Test>::CallIsNotWhitelisted,
		);
	});
}
