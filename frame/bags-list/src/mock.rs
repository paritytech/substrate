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

//! Mock runtime for pallet-bags-lists tests.

use super::*;
use crate::{self as bags_list};
use frame_election_provider_support::VoteWeight;
use frame_support::parameter_types;

pub type AccountId = u32;
pub type Balance = u32;

parameter_types! {
	pub static NextVoteWeight: VoteWeight = 0;
}

pub struct StakingMock;
impl frame_election_provider_support::VoteWeightProvider<AccountId> for StakingMock {
	fn vote_weight(id: &AccountId) -> VoteWeight {
		match id {
			710 => 15,
			711 => 16,
			712 => 2_000, // special cases used for migrate test
			_ => NextVoteWeight::get(),
		}
	}
	#[cfg(any(feature = "runtime-benchmarks", test))]
	fn set_vote_weight_of(_: &AccountId, weight: VoteWeight) {
		// we don't really keep a mapping, just set weight for everyone.
		NextVoteWeight::set(weight)
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
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
}

parameter_types! {
	pub static BagThresholds: &'static [VoteWeight] = &[10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];
}

impl bags_list::Config for Runtime {
	type Event = Event;
	type WeightInfo = ();
	type BagThresholds = BagThresholds;
	type VoteWeightProvider = StakingMock;
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
}

impl ExtBuilder {
	/// Add some AccountIds to insert into `List`.
	#[cfg(test)]
	pub(crate) fn add_ids(mut self, ids: Vec<(AccountId, VoteWeight)>) -> Self {
		self.ids = ids;
		self
	}

	pub(crate) fn build(self) -> sp_io::TestExternalities {
		sp_tracing::try_init_simple();
		let storage = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

		let mut ext = sp_io::TestExternalities::from(storage);
		ext.execute_with(|| {
			for (id, weight) in GENESIS_IDS.iter().chain(self.ids.iter()) {
				frame_support::assert_ok!(List::<Runtime>::insert(*id, *weight));
			}
		});

		ext
	}

	pub fn build_and_execute(self, test: impl FnOnce() -> ()) {
		self.build().execute_with(|| {
			test();
			List::<Runtime>::sanity_check().expect("Sanity check post condition failed")
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
