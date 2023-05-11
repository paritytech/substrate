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
//! Running this fuzzer can be done with `cargo hfuzz run paged-list`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug paged-list hfuzz_workspace/paged-list/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use arbitrary::Arbitrary;
use honggfuzz::fuzz;

fn main() {
	loop {
		fuzz!(|data: (Vec<Op>, u8)| {
			drain_append_work(data.0, data.1);
		});
	}
}

/// Appends and drains random number of elements in random order and checks storage invariants.
fn drain_append_work(ops: Vec<Op>, page_size: u8) {
	use mock::*;
	if page_size == 0 {
		return
	}

	TestExternalities::default().execute_with(|| {
		ValuesPerPage::set(&page_size.into());
		let _g = StorageNoopGuard::default();
		let mut total: i64 = 0;

		for op in ops.into_iter() {
			total += op.exec();

			assert!(total >= 0);
			assert_eq!(List::iter().count(), total as usize);

			// We have the assumption that the queue removes the metadata when being empty.
			if total == 0 {
				assert_eq!(List::drain().count(), 0);
				assert_eq!(List::read_meta().unwrap_or_default(), Default::default());
			}
		}

		assert_eq!(List::drain().count(), total as usize);
		// No storage leaking (checked by `StorageNoopGuard`).
	});
}

enum Op {
	Append(Vec<u32>),
	Drain(u8),
}

impl Arbitrary<'_> for Op {
	fn arbitrary(u: &mut arbitrary::Unstructured<'_>) -> arbitrary::Result<Self> {
		if u.arbitrary::<bool>()? {
			Ok(Op::Append(Vec::<u32>::arbitrary(u)?))
		} else {
			Ok(Op::Drain(u.arbitrary::<u8>()?))
		}
	}
}

impl Op {
	pub fn exec(self) -> i64 {
		use mock::*;

		match self {
			Op::Append(v) => {
				let l = v.len();
				List::append_many(v);
				l as i64
			},
			Op::Drain(v) => -(List::drain().take(v as usize).count() as i64),
		}
	}
}

#[allow(dead_code)]
mod mock {
	pub use frame_support::{
		metadata_ir::{StorageEntryModifierIR, StorageEntryTypeIR, StorageHasherIR},
		parameter_types,
		storage::{types::StoragePagedList, StorageList as _, TestingStoragePagedList as _},
		traits::StorageInstance,
		Blake2_128Concat, StorageNoopGuard,
	};
	pub use sp_io::TestExternalities;

	parameter_types! {
		pub storage ValuesPerPage: u32 = 10;
		pub const MaxPages: Option<u32> = Some(20);
	}

	pub struct Prefix;
	impl StorageInstance for Prefix {
		fn pallet_prefix() -> &'static str {
			"test"
		}
		const STORAGE_PREFIX: &'static str = "foo";
	}

	pub type List = StoragePagedList<Prefix, Blake2_128Concat, u32, ValuesPerPage, MaxPages>;
}
