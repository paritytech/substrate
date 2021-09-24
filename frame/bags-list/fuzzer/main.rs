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
//!
//! //! MacOS users notethat https://github.com/rust-fuzz/honggfuzz-rs/issues/56 may preclude you from running this locally.

use frame_election_provider_support::{SortedListProvider, VoteWeight};
use honggfuzz::fuzz;
use pallet_bags_list::mock::{AccountId, BagsList, ExtBuilder};

const ID_RANGE: AccountId = 10_000;
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
					BagsList::on_remove(&id);
					assert!(!BagsList::contains(&id));
				},
			}

			assert!(BagsList::sanity_check().is_ok());
		})
	});
}
