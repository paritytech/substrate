// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::{mock::*, *};
use frame_support::storage::{StorageList, StoragePrefixedContainer};

#[test]
fn iter_independent_works() {
	new_test_ext().execute_with(|| {
		PagedList1::append_many(0..1000);
		PagedList2::append_many(0..1000);

		assert_eq!(PagedList1::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());
		assert_eq!(PagedList1::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());

		// drain
		assert_eq!(PagedList1::drain().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());
		assert_eq!(PagedList2::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());

		assert_eq!(PagedList1::iter().count(), 0);
	});
}

#[test]
fn prefix_distinct() {
	let p1 = List::<Test, ()>::final_prefix();
	let p2 = List::<Test, crate::Instance2>::final_prefix();
	assert_ne!(p1, p2);
}
