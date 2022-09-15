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

//! Mock runtime for pallet-bags-lists tests.

use super::*;
use crate::{self as bags_list};
use frame_election_provider_support::VoteWeight;
use frame_support::parameter_types;
use std::collections::HashMap;

pub type AccountId = u32;
pub type Balance = u32;

parameter_types! {
	// Set the vote weight for any id who's weight has _not_ been set with `set_score_of`.
	pub static NextVoteWeight: VoteWeight = 0;
	pub static NextVoteWeightMap: HashMap<AccountId, VoteWeight> = Default::default();
}

pub struct StakingMock;
impl frame_election_provider_support::ScoreProvider<AccountId> for StakingMock {
	type Score = VoteWeight;

	fn score(id: &AccountId) -> Self::Score {
		*NextVoteWeightMap::get().get(id).unwrap_or(&NextVoteWeight::get())
	}

	#[cfg(any(feature = "runtime-benchmarks", feature = "fuzz", test))]
	fn set_score_of(id: &AccountId, weight: Self::Score) {
		NEXT_VOTE_WEIGHT_MAP.with(|m| m.borrow_mut().insert(*id, weight));
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub static BagThresholds: &'static [VoteWeight] = &[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];
}

impl bags_list::Config for Runtime {
	type RuntimeEvent = RuntimeEvent;
	type WeightInfo = ();
	type BagThresholds = BagThresholds;
	type ScoreProvider = StakingMock;
	type Score = VoteWeight;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Event<T>, Config},
		BagsList: bags_list::{Pallet, Call, Storage, Event<T>},
	}
);

/// Default AccountIds and their weights.
pub(crate) const GENESIS_IDS: [(AccountId, VoteWeight); 4] =
	[(1, 10), (2, 1_000), (3, 1_000), (4, 1_000)];

#[derive(Default)]
pub struct ExtBuilder {
	ids: Vec<(AccountId, VoteWeight)>,
	skip_genesis_ids: bool,
}

#[cfg(any(feature = "runtime-benchmarks", feature = "fuzz", test))]
impl ExtBuilder {
	/// Skip adding the default genesis ids to the list.
	#[cfg(test)]
	pub(crate) fn skip_genesis_ids(mut self) -> Self {
		self.skip_genesis_ids = true;
		self
	}

	/// Add some AccountIds to insert into `List`.
	#[cfg(test)]
	pub(crate) fn add_ids(mut self, ids: Vec<(AccountId, VoteWeight)>) -> Self {
		self.ids = ids;
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let storage = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let ids_with_weight: Vec<_> = if self.skip_genesis_ids {
			self.ids.iter().collect()
		} else {
			GENESIS_IDS.iter().chain(self.ids.iter()).collect()
		};

		let mut ext = sp_io::TestExternalities::from(storage);
		ext.execute_with(|| {
			for (id, weight) in ids_with_weight {
				frame_support::assert_ok!(List::<Runtime>::insert(*id, *weight));
				StakingMock::set_score_of(id, *weight);
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			List::<Runtime>::try_state().expect("Try-state post condition failed")
		})
	}

	#[cfg(test)]
	pub(crate) fn build_and_execute_no_post_check(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(test)
	}
}

#[cfg(test)]
pub(crate) mod test_utils {
	use super::*;
	use list::Bag;

	/// Returns the ordered ids within the given bag.
	pub(crate) fn bag_as_ids(bag: &Bag<Runtime>) -> Vec<AccountId> {
		bag.iter().map(|n| *n.id()).collect::<Vec<_>>()
	}

	/// Returns the ordered ids from the list.
	pub(crate) fn get_list_as_ids() -> Vec<AccountId> {
		List::<Runtime>::iter().map(|n| *n.id()).collect::<Vec<_>>()
	}
}
