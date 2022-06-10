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

//! Tests for [`ExtendedCallData`].
//! They are in a separate module for faster compilation after a change.

#![cfg(test)]

use super::*;
use crate::{
	mock::{new_test_ext, Test, CALL},
	Config, ExtendedCallData, Pallet as System,
};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{assert_noop, assert_ok, traits::ConstU32, weights::DispatchInfo, *};
use scale_info::TypeInfo;
use sp_core::Hasher;
use sp_runtime::{
	traits::{DispatchInfoOf, Dispatchable, One, SignedExtension},
	transaction_validity::{
		InvalidTransaction, TransactionLongevity, TransactionValidity, TransactionValidityError,
		ValidTransaction,
	},
};
use sp_std::vec::Vec;

#[test]
fn extended_call_data_works() {
	new_test_ext().execute_with(|| {
		let info = DispatchInfo::default();
		let len = 0_usize;
		// Too large for normal Call data.
		let raw = vec![0u8; 4_000_000];
		let ecd: BoundedVec<_, _> = raw.try_into().unwrap();

		let extension = ExtendedCallData::<Test>::from(ecd.clone());
		// The user must sign the complete ECD.
		assert_eq!(extension.additional_signed().unwrap(), Some(ecd.clone()));
		assert!(extension.pre_dispatch(&0, CALL, &info, len).is_ok());

		// Interesting part here:
		// Any extrinsic can now access the ECD via this getter function.
		assert_eq!(System::<Test>::extended_call_data(), Some(ecd));
	})
}
