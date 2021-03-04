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

use crate::*;
use mock::*;
use frame_support::{
	assert_noop, weights::WithPostDispatchInfo, dispatch::PostDispatchInfo,
	sp_runtime::{DispatchError, DispatchErrorWithPostInfo, traits::{Header, BlakeTwo256}},
};

#[test]
fn stored_map_works() {
	new_test_ext().execute_with(|| {
		assert!(Accounts::insert(&0, 42).is_ok());
		assert!(!Accounts::is_provider_required(&0));

		assert_eq!(Account::<Test>::get(0), AccountInfo {
			nonce: 0,
			providers: 1,
			consumers: 0,
			sufficients: 0,
			data: 42,
		});

		assert!(Accounts::inc_consumers(&0).is_ok());
		assert!(Accounts::is_provider_required(&0));

		assert!(Accounts::insert(&0, 69).is_ok());
		assert!(Accounts::is_provider_required(&0));

		Accounts::dec_consumers(&0);
		assert!(!Accounts::is_provider_required(&0));

		assert!(KILLED.with(|r| r.borrow().is_empty()));
		assert!(Accounts::remove(&0).is_ok());
		assert_eq!(KILLED.with(|r| r.borrow().clone()), vec![0u64]);
	});
}

#[test]
fn provider_ref_handover_to_self_sufficient_ref_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Accounts::inc_providers(&0), IncRefStatus::Created);
		Accounts::inc_account_nonce(&0);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// a second reference coming and going doesn't change anything.
		assert_eq!(Accounts::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// a provider reference coming and going doesn't change anything.
		assert_eq!(Accounts::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// decreasing the providers with a self-sufficient present should not delete the account
		assert_eq!(Accounts::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// decreasing the sufficients should delete the account
		assert_eq!(Accounts::dec_sufficients(&0), DecRefStatus::Reaped);
		assert_eq!(Accounts::account_nonce(&0), 0);
	});
}

#[test]
fn self_sufficient_ref_handover_to_provider_ref_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(Accounts::inc_sufficients(&0), IncRefStatus::Created);
		Accounts::inc_account_nonce(&0);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// a second reference coming and going doesn't change anything.
		assert_eq!(Accounts::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// a sufficient reference coming and going doesn't change anything.
		assert_eq!(Accounts::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// decreasing the sufficients with a provider present should not delete the account
		assert_eq!(Accounts::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(Accounts::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(Accounts::account_nonce(&0), 1);

		// decreasing the providers should delete the account
		assert_eq!(Accounts::dec_providers(&0).unwrap(), DecRefStatus::Reaped);
		assert_eq!(Accounts::account_nonce(&0), 0);
	});
}
