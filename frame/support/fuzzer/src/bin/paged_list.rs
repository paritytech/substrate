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

//! # Running
//! Running this fuzzer can be done with `cargo hfuzz run pallet-paged-list`. `honggfuzz` CLI
//! options can be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug pallet-paged-list hfuzz_workspace/pallet-paged-list/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use frame_support::StorageNoopGuard;
use honggfuzz::fuzz;

use frame_support_storage_fuzzer::*;

fn main() {
	loop {
		fuzz!(|data: (Vec<Op>, u8)| {
			drain_append_work(data.0, data.1);
		});
	}
}

/// Appends and drains random number of elements in random order and checks storage invariants.
///
/// It also changes the maximal number of elements per page dynamically, hence the `page_size`.
fn drain_append_work(ops: Vec<Op>, page_size: u8) {
	if page_size == 0 {
		return
	}

	TestExternalities::default().execute_with(|| {
		//ValuesPerNewPage::set(&page_size.into());
		let _g = StorageNoopGuard::default();
		let mut total: i64 = 0;

		for op in ops.into_iter() {
			total += op.exec_list::<List>();

			assert!(total >= 0);
			assert_eq!(List::iter().count(), total as usize);
			assert_eq!(total as u64, List::len());

			// We have the assumption that the queue removes the metadata when empty.
			if total == 0 {
				assert_eq!(List::drain().count(), 0);
				assert_eq!(List::meta(), Default::default());
			}
		}

		assert_eq!(List::drain().count(), total as usize);
		// `StorageNoopGuard` checks that there is no storage leaked.
	});
}
