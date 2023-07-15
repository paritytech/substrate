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

#![cfg(test)]

use super::*;
use crate as pallet_name_service;
use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
	weights::Weight,
	BoundedVec,
};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, Identity, IdentityLookup},
	BuildStorage,
};

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test {
		System: frame_system,
		Balances: pallet_balances,
		NameService: pallet_name_service
	}
);

type Balance = u64;
type AccountId = u64;

parameter_types! {
	pub static CommitmentDepositConfig: Option<Balance> = Some(1);
	pub static SubNodeDepositConfig: Option<Balance> = Some(1);
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(Weight::MAX);
}

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type Block = Block;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<AccountId>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
	type Nonce = u64;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = Balance;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type FreezeIdentifier = ();
	type MaxFreezes = ();
	type RuntimeHoldReason = ();
	type MaxHolds = ();
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type BlockNumberToBalance = Identity;
	type Currency = Balances;
	type MinCommitmentAge = ConstU64<10>;
	type MaxCommitmentAge = ConstU64<10>;
	type MaxNameLength = ConstU32<2048>; // 2048 is the standard URL limit
	type MaxSuffixLength = ConstU32<4>;
	type MaxTextLength = ConstU32<2048>;
	type NameServiceResolver = NameService;
	type MaxRegistrationLength = ConstU64<365>;
	type RegistrationFeeHandler = ();
	type WeightInfo = ();
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();

	let _ = crate::GenesisConfig::<Test> {
		commitment_deposit: CommitmentDepositConfig::get(),
		subnode_deposit: SubNodeDepositConfig::get(),
		tier_three_letters: 7,
		tier_four_letters: 3,
		tier_default: 1,
		registration_fee_per_block: 1,
		per_byte_fee: 1,
	}
	.assimilate_storage(&mut t);

	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(1, 100), (2, 200), (3, 300), (4, 400), (5, 500), (6, 600)],
	}
	.assimilate_storage(&mut t)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		System::set_block_number(1);
		let suffix: BoundedVec<u8, _> = BoundedVec::try_from("pdot".as_bytes().to_vec()).unwrap();
		let para_id = 1;
		DomainRegistrations::<Test>::insert(para_id, suffix.clone());
		ReverseDomainsLookup::<Test>::insert(suffix, para_id);
	});
	ext
}

pub type NameServiceEvent = crate::Event<Test>;
pub type BalancesError = pallet_balances::Error<Test>;
