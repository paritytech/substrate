// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Test environment for transaction-storage pallet.

use crate as pallet_transaction_storage;
use crate::TransactionStorageProof;
use sp_core::H256;
use sp_runtime::{traits::{BlakeTwo256, IdentityLookup}, testing::Header, BuildStorage};
use frame_support::{
	parameter_types,
	traits::{OnInitialize, OnFinalize},
};


type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
pub type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Config<T>, Storage, Event<T>},
		TransactionStorage: pallet_transaction_storage::{
			Pallet, Call, Storage, Config<T>, Inherent, Event<T>
		},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const SS58Prefix: u8 = 42;
}

impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type Origin = Origin;
	type Call = Call;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = SS58Prefix;
	type OnSetCode = ();
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
}

impl pallet_transaction_storage::Config for Test {
	type Event = Event;
	type Call = Call;
	type Currency = Balances;
	type FeeDestination = ();
	type WeightInfo = ();
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = GenesisConfig {
		frame_system: Default::default(),
		pallet_balances: pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 1000000000), (2, 100), (3, 100), (4, 100)]
		},
		pallet_transaction_storage: pallet_transaction_storage::GenesisConfig::<Test> {
			storage_period: 10,
			byte_fee: 2,
			entry_fee: 200,
			max_block_transactions: crate::DEFAULT_MAX_BLOCK_TRANSACTIONS,
			max_transaction_size: crate::DEFAULT_MAX_TRANSACTION_SIZE,
		},
	}.build_storage().unwrap();
	t.into()
}

pub fn run_to_block(n: u64, f: impl Fn() -> Option<TransactionStorageProof>) {
	while System::block_number() < n {
		if let Some(proof) = f() {
			TransactionStorage::check_proof(Origin::none(), proof).unwrap();
		}
		TransactionStorage::on_finalize(System::block_number());
		System::on_finalize(System::block_number());
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		TransactionStorage::on_initialize(System::block_number());
	}
}
