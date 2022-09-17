// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Test utilities for transaction pause (tx pause) pallet.

use super::*;
use crate as pallet_tx_pause;

use frame_support::{parameter_types, traits::{InsideBoth,SortedMembers, EitherOfDiverse, Everything}};
use frame_system::{EnsureRoot, EnsureSignedBy};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

parameter_types! {
	pub const BlockHashCount: u64 = 250;
}
impl frame_system::Config for Test {
	type BaseCallFilter = InsideBoth<Everything, TxPause>;
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
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
	pub const MaxLocks: u32 = 10;
}
impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = MaxLocks;
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

parameter_types! {
	pub const PauseOrigin: u64 = 1;
	pub const UnpauseOrigin: u64 = 2;
  pub const MaxNameLen: u32 = 50;
  pub const PauseTooLongNames: bool = false;
}

// pub struct MockUnpausablePallets;
// impl Contains<BoundedVec<u8,MaxNameLen>> for MockUnpausablePallets {
// 	fn contains(bounded_vec: &BoundedVec<u8,MaxNameLen>) -> bool {
// 		bounded_vec. 
// 		todo!() // What does this need to be to properly impl contains?
// 	}
// }

pub struct MockUnpausablePallets;
impl Contains<PalletNameOf<Test>> for MockUnpausablePallets {
	fn contains(pallet: &PalletNameOf<Test>) -> bool {
		match pallet {
			<TxPause as PalletInfoAccess>::name() => true,
			b"unpausable_pallet" => true,
			_ => false,
		}
	}
}
// Required impl to use some <Configured Origin>::get() in tests
impl SortedMembers<u64> for PauseOrigin {
	fn sorted_members() -> Vec<u64> {
		vec![Self::get()]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}
impl SortedMembers<u64> for UnpauseOrigin {
	fn sorted_members() -> Vec<u64> {
		vec![Self::get()]
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_m: &u64) {}
}

impl Config for Test {
	type Event = Event;
	type PauseOrigin = EitherOfDiverse<EnsureSignedBy<PauseOrigin, Self::AccountId>, EnsureRoot<Self::AccountId>>; // TODO should not need to explicitly define root in addition?
	type UnpauseOrigin = EitherOfDiverse<EnsureSignedBy<UnpauseOrigin, Self::AccountId>, EnsureRoot<Self::AccountId>>; // TODO should not need to explicitly define root in addition?
  type UnpausablePallets = MockUnpausablePallets;
  type MaxNameLen = MaxNameLen;
  type PauseTooLongNames = PauseTooLongNames;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Balances: pallet_balances,
		TxPause: pallet_tx_pause,
	}
);

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	pallet_balances::GenesisConfig::<Test> {
		balances: vec![(0,1234), (1, 5678), (2, 5678), (3, 5678), (4, 5678)], // The 0 account is NOT a special origin, the rest may be.
	}
	.assimilate_storage(&mut t)
	.unwrap();

	GenesisBuild::<Test>::assimilate_storage(
		&pallet_tx_pause::GenesisConfig {
			paused: vec![],
			_phantom: Default::default(),
		},
		&mut t,
	)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		System::set_block_number(1);
	});
	ext
}

#[cfg(feature = "runtime-benchmarks")]
pub fn new_bench_ext() -> sp_io::TestExternalities {
	GenesisConfig::default().build_storage().unwrap().into()
}

pub fn next_block() {
	TxPause::on_finalize(System::block_number());
	Balances::on_finalize(System::block_number());
	System::on_finalize(System::block_number());
	System::set_block_number(System::block_number() + 1);
	System::on_initialize(System::block_number());
	Balances::on_initialize(System::block_number());
	TxPause::on_initialize(System::block_number());
}

pub fn run_to(n: u64) {
	while System::block_number() < n {
		next_block();
	}
}
