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

const ID_RANGE: AccountId = 50_000;
const OPTIONS: AccountId = 3;

fn main() {
	ExtBuilder::default().build_and_execute(|| loop {
		fuzz!(|data: (AccountId, VoteWeight)| {
			let (account_id_seed, vote_weight) = data;

			let id = account_id_seed % ID_RANGE;

			match account_id_seed % OPTIONS {
				0 => {
					if BagsList::on_insert(id.clone(), vote_weight).is_err() {
						// this was a duplicate id, which is ok. We can just update it.
						BagsList::on_update(&id, vote_weight);
					}
					assert!(BagsList::contains(&id));
				},
				1 => {
					if !BagsList::contains(&id) {
						// we must insert before updating.
						assert!(BagsList::on_insert(id.clone(), vote_weight).is_ok());
					}
					BagsList::on_update(&id, vote_weight);
					assert!(BagsList::contains(&id));
				},
				_ => {
					// only `2` should ever get us here, but we must use a wildcard to make the
					// compiler happy.
					BagsList::on_remove(&id);
					assert!(!BagsList::contains(&id));
				},
			}

			assert!(BagsList::sanity_check().is_ok());
		})
	});
}
