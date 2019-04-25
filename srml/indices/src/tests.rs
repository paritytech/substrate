// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Tests for the module.

#![cfg(test)]

use super::*;
use crate::mock::{Indices, new_test_ext, make_account, kill_account, TestIsDeadAccount};
use runtime_io::with_externalities;

#[test]
fn indexing_lookup_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(0), Some(1));
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(2), Some(3));
			assert_eq!(Indices::lookup_index(3), Some(4));
			assert_eq!(Indices::lookup_index(4), None);
		},
	);
}

#[test]
fn default_indexing_on_new_accounts_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(4), None);
			make_account(5);
			assert_eq!(Indices::lookup_index(4), Some(5));
		},
	);
}

#[test]
fn reclaim_indexing_on_new_accounts_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(4), None);

			kill_account(2);					// index 1 no longer locked to id 2

			make_account(1 + 256);				// id 257 takes index 1.
			assert_eq!(Indices::lookup_index(1), Some(257));
		},
	);
}

#[test]
fn alive_account_should_prevent_reclaim() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert!(!TestIsDeadAccount::is_dead_account(&2));
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(4), None);

			make_account(1 + 256);				// id 257 takes index 1.
			assert_eq!(Indices::lookup_index(4), Some(257));
		},
	);
}
