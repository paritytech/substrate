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

//! Test utilities

use super::*;
use crate as pallet_scored_pool;

use frame_support::{
	bounded_vec, construct_runtime, ord_parameter_types, parameter_types,
	traits::{ConstU32, ConstU64, GenesisBuild},
};
use frame_system::EnsureSignedBy;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		ScoredPool: pallet_scored_pool::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
);

parameter_types! {
	pub const CandidateDeposit: u64 = 25;
}
ord_parameter_types! {
	pub const KickOrigin: u64 = 2;
	pub const ScoreOrigin: u64 = 3;
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type RuntimeEvent = RuntimeEvent;
	type DustRemoval = ();
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}

parameter_types! {
	pub static MembersTestValue: BoundedVec<u64,ConstU32<10_u32>> = bounded_vec![0,10];
}

pub struct TestChangeMembers;
impl ChangeMembers<u64> for TestChangeMembers {
	fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
		let mut old_plus_incoming = MembersTestValue::get().into_inner();
		old_plus_incoming.extend_from_slice(incoming);
		old_plus_incoming.sort();

		let mut new_plus_outgoing = new.to_vec();
		new_plus_outgoing.extend_from_slice(outgoing);
		new_plus_outgoing.sort();

		assert_eq!(old_plus_incoming, new_plus_outgoing);

		MembersTestValue::set(<BoundedVec<u64, ConstU32<10_u32>>>::truncate_from(new.to_vec()));
	}
}

impl InitializeMembers<u64> for TestChangeMembers {
	fn initialize_members(new_members: &[u64]) {
		MembersTestValue::set(<BoundedVec<u64, ConstU32<10_u32>>>::truncate_from(
			new_members.to_vec(),
		));
	}
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type KickOrigin = EnsureSignedBy<KickOrigin, u64>;
	type MembershipInitialized = TestChangeMembers;
	type MembershipChanged = TestChangeMembers;
	type Currency = Balances;
	type CandidateDeposit = CandidateDeposit;
	type Period = ConstU64<4>;
	type Score = u64;
	type ScoreOrigin = EnsureSignedBy<ScoreOrigin, u64>;
	type MaximumMembers = ConstU32<10>;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let mut balances = vec![];
	for i in 1..31 {
		balances.push((i, 500_000));
	}
	balances.push((31, 500_000));
	balances.push((40, 500_000));
	balances.push((99, 1));

	pallet_balances::GenesisConfig::<Test> { balances }
		.assimilate_storage(&mut t)
		.unwrap();
	pallet_scored_pool::GenesisConfig::<Test> {
		pool: bounded_vec![(10, Some(1)), (20, Some(2)), (31, Some(2)), (40, Some(3)), (5, None)],
		member_count: 2,
	}
	.assimilate_storage(&mut t)
	.unwrap();
	t.into()
}

/// Fetch an entity from the pool, if existent.
pub fn fetch_from_pool(who: u64) -> Option<(u64, Option<u64>)> {
	<Pallet<Test>>::pool().into_iter().find(|item| item.0 == who)
}

/// Find an entity in the pool.
/// Returns its position in the `Pool` vec, if existent.
pub fn find_in_pool(who: u64) -> Option<usize> {
	<Pallet<Test>>::pool().into_iter().position(|item| item.0 == who)
}
