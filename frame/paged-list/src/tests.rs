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

//! Mostly pallet doc-tests. Real tests are in [`super::paged_list`] and crate
//! `pallet-paged-list-fuzzer`.

#![cfg(test)]

use crate::{mock::*, *};
use frame_support::storage::{StorageList, StoragePrefixedContainer};

#[docify::export]
#[test]
fn append_one_works() {
	test_closure(|| {
		PagedList::append_one(1);

		assert_eq!(PagedList::iter().collect::<Vec<_>>(), vec![1]);
	});
}

#[docify::export]
#[test]
fn append_many_works() {
	test_closure(|| {
		PagedList::append_many(0..3);

		assert_eq!(PagedList::iter().collect::<Vec<_>>(), vec![0, 1, 2]);
	});
}

#[docify::export]
#[test]
fn appender_works() {
	use frame_support::storage::StorageAppender;
	test_closure(|| {
		let mut appender = PagedList::appender();

		appender.append(0);
		appender.append(1); // Repeated calls are fine here.
		appender.append_many(2..4);

		assert_eq!(PagedList::iter().collect::<Vec<_>>(), vec![0, 1, 2, 3]);
	});
}

#[docify::export]
#[test]
fn iter_works() {
	test_closure(|| {
		PagedList::append_many(0..10);
		let mut iter = PagedList::iter();

		assert_eq!(iter.next(), Some(0));
		assert_eq!(iter.next(), Some(1));
		assert_eq!(iter.collect::<Vec<_>>(), (2..10).collect::<Vec<_>>());
	});
}

#[docify::export]
#[test]
fn drain_works() {
	test_closure(|| {
		PagedList::append_many(0..3);
		PagedList::drain().next();
		assert_eq!(PagedList::iter().collect::<Vec<_>>(), vec![1, 2], "0 is drained");
		PagedList::drain().peekable().peek();
		assert_eq!(PagedList::iter().collect::<Vec<_>>(), vec![2], "Peeking removed 1");
	});
}

#[test]
fn iter_independent_works() {
	test_closure(|| {
		PagedList::append_many(0..1000);
		PagedList2::append_many(0..1000);

		assert_eq!(PagedList::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());
		assert_eq!(PagedList::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());

		// drain
		assert_eq!(PagedList::drain().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());
		assert_eq!(PagedList2::iter().collect::<Vec<_>>(), (0..1000).collect::<Vec<_>>());

		assert_eq!(PagedList::iter().count(), 0);
	});
}

#[test]
fn prefix_distinct() {
	let p1 = List::<Test, ()>::final_prefix();
	let p2 = List::<Test, crate::Instance2>::final_prefix();
	assert_ne!(p1, p2);
}
