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

//! Fuzzer to test all paged data structures in one go to ensure that they won't interfere with
//! each other.

use frame_support::{storage::StorageKeyedList, StorageNoopGuard};
use honggfuzz::fuzz;
use std::collections::BTreeMap;

use frame_support_storage_fuzzer::*;

fn main() {
	loop {
		fuzz!(|data: (Vec<AllInOneOp>, u16)| {
			drain_append_work(data.0, data.1);
		});
	}
}

/// Appends and drains random number of elements in random order and checks storage invariants.
///
/// It also changes the maximal number of elements per page dynamically, hence the `page_size`.
fn drain_append_work(ops: Vec<AllInOneOp>, page_size: u16) {
	if page_size < 4 {
		return
	}

	TestExternalities::default().execute_with(|| {
		// Changing the heapsize should be fine at any point in time - even to non-multiple of 4,
		HeapSize::set(&page_size.into());

		let _g = StorageNoopGuard::default();
		let mut map_totals: BTreeMap<u32, i64> = BTreeMap::new();
		let mut list_total = 0i64;

		for op in ops.into_iter() {
			match op {
				AllInOneOp::NMap(op) => {
					let total = map_totals.entry(op.key).or_insert(0);
					*total += op.op.exec_map(op.key);

					assert!(*total >= 0);
					assert_eq!(NMap::iter((op.key,)).count(), *total as usize);
					assert_eq!(*total as u64, NMap::len((op.key,)));

					// We have the assumption that the queue removes the metadata when empty.
					if *total == 0 {
						assert_eq!(NMap::drain((op.key,)).count(), 0);
						assert_eq!(NMap::meta((op.key,)), Default::default());
					}
				},
				AllInOneOp::List(op) => {
					list_total += op.exec_list::<List>();

					assert!(list_total >= 0);
					assert_eq!(List::iter().count(), list_total as usize);
					assert_eq!(list_total as u64, List::len());

					if list_total == 0 {
						assert_eq!(List::drain().count(), 0);
						assert_eq!(List::meta(), Default::default());
					}
				},
			}
		}

		for (key, total) in map_totals {
			assert_eq!(NMap::drain((key,)).count(), total as usize);
		}
		assert_eq!(List::drain().count(), list_total as usize);
		// `StorageNoopGuard` checks that there is no storage leaked.
	});
}
