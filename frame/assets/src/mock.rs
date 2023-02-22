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

//! Test environment for Assets pallet.

use super::*;
use crate as pallet_assets;

use codec::Encode;
use frame_support::{
	construct_runtime, parameter_types,
	traits::{AsEnsureOriginWithArg, ConstU32, ConstU64, GenesisBuild},
};
use sp_core::H256;
use sp_io::storage;
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
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
	}
);

type AccountId = u64;
type AssetId = u32;

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<2>;
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
}

pub struct AssetsCallbackHandle;
impl AssetsCallback<AssetId, AccountId> for AssetsCallbackHandle {
	fn created(_id: &AssetId, _owner: &AccountId) {
		storage::set(b"asset_created", &().encode());
	}

	fn destroyed(_id: &AssetId) {
		storage::set(b"asset_destroyed", &().encode());
	}
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Balance = u64;
	type AssetId = u32;
	type AssetIdParameter = u32;
	type Currency = Balances;
	type CreateOrigin = AsEnsureOriginWithArg<frame_system::EnsureSigned<u64>>;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type AssetDeposit = ConstU64<1>;
	type AssetAccountDeposit = ConstU64<10>;
	type MetadataDepositBase = ConstU64<1>;
	type MetadataDepositPerByte = ConstU64<1>;
	type ApprovalDeposit = ConstU64<1>;
	type StringLimit = ConstU32<50>;
	type Freezer = TestFreezer;
	type WeightInfo = ();
	type CallbackHandle = AssetsCallbackHandle;
	type Extra = ();
	type RemoveItemsLimit = ConstU32<5>;
	#[cfg(feature = "runtime-benchmarks")]
	type BenchmarkHelper = ();
}

use std::collections::HashMap;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Hook {
	Died(u32, u64),
}
parameter_types! {
	static Frozen: HashMap<(u32, u64), u64> = Default::default();
	static Hooks: Vec<Hook> = Default::default();
}

pub struct TestFreezer;
impl FrozenBalance<u32, u64, u64> for TestFreezer {
	fn frozen_balance(asset: u32, who: &u64) -> Option<u64> {
		Frozen::get().get(&(asset, *who)).cloned()
	}

	fn died(asset: u32, who: &u64) {
		Hooks::mutate(|v| v.push(Hook::Died(asset, *who)));

		// Sanity check: dead accounts have no balance.
		assert!(Assets::balance(asset, *who).is_zero());
	}
}

pub(crate) fn set_frozen_balance(asset: u32, who: u64, amount: u64) {
	Frozen::mutate(|v| {
		v.insert((asset, who), amount);
	});
}

pub(crate) fn clear_frozen_balance(asset: u32, who: u64) {
	Frozen::mutate(|v| {
		v.remove(&(asset, who));
	});
}

pub(crate) fn hooks() -> Vec<Hook> {
	Hooks::get().clone()
}

pub(crate) fn take_hooks() -> Vec<Hook> {
	Hooks::take()
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let mut storage = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let config: pallet_assets::GenesisConfig<Test> = pallet_assets::GenesisConfig {
		assets: vec![
			// id, owner, is_sufficient, min_balance
			(999, 0, true, 1),
		],
		metadata: vec![
			// id, name, symbol, decimals
			(999, "Token Name".into(), "TOKEN".into(), 10),
		],
		accounts: vec![
			// id, account_id, balance
			(999, 1, 100),
		],
	};

	config.assimilate_storage(&mut storage).unwrap();

	let mut ext: sp_io::TestExternalities = storage.into();
	// Clear thread local vars for https://github.com/paritytech/substrate/issues/10479.
	ext.execute_with(|| take_hooks());
	ext.execute_with(|| System::set_block_number(1));
	ext
}
