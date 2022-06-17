// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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
//! Running this fuzzer can be done with `cargo hfuzz run bags-list`. `honggfuzz` CLI options can
//! be used by setting `HFUZZ_RUN_ARGS`, such as `-n 4` to use 4 threads.
//!
//! # Debugging a panic
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug fixed_point hfuzz_workspace/bags_list/*.fuzz`.
//!
//! # More information
//! More information about `honggfuzz` can be found
//! [here](https://docs.rs/honggfuzz/).

use frame_election_provider_support::{SortedListProvider, VoteWeight};
use honggfuzz::fuzz;
use pallet_bags_list::mock::{AccountId, BagsList, ExtBuilder};

const ID_RANGE: AccountId = 25_000;

/// Actions of a `SortedListProvider` that we fuzz.
enum Action {
	Insert,
	Update,
	Remove,
}

impl From<u32> for Action {
	fn from(v: u32) -> Self {
		let num_variants = Self::Remove as u32 + 1;
		match v % num_variants {
			_x if _x == Action::Insert as u32 => Action::Insert,
			_x if _x == Action::Update as u32 => Action::Update,
			_x if _x == Action::Remove as u32 => Action::Remove,
			_ => unreachable!(),
		}
	}
}

fn main() {
	ExtBuilder::default().build_and_execute(|| loop {
		fuzz!(|data: (AccountId, VoteWeight, u32)| {
			let (account_id_seed, vote_weight, action_seed) = data;

			let id = account_id_seed % ID_RANGE;
			let action = Action::from(action_seed);

			match action {
				Action::Insert => {
					if BagsList::on_insert(id, vote_weight).is_err() {
						// this was a duplicate id, which is ok. We can just update it.
						BagsList::on_update(&id, vote_weight).unwrap();
					}
					assert!(BagsList::contains(&id));
				},
				Action::Update => {
					let already_contains = BagsList::contains(&id);
					if already_contains {
						BagsList::on_update(&id, vote_weight).unwrap();
						assert!(BagsList::contains(&id));
					} else {
						BagsList::on_update(&id, vote_weight).unwrap_err();
					}
				},
				Action::Remove => {
					let already_contains = BagsList::contains(&id);
					if already_contains {
						BagsList::on_remove(&id).unwrap();
					} else {
						BagsList::on_remove(&id).unwrap_err();
					}
					assert!(!BagsList::contains(&id));
				},
			}

			assert!(BagsList::sanity_check().is_ok());
		})
	});
}
