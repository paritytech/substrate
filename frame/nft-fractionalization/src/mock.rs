// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Test environment for Nft fractionalization pallet.

use super::*;
use crate as pallet_nft_fractionalization;

use frame_support::{
	construct_runtime, parameter_types,
	traits::{
		tokens::{
			nonfungibles_v2::{Inspect, LockableNonfungible, Mutate},
			AttributeNamespace,
		},
		AsEnsureOriginWithArg, ConstU32, ConstU64, Locker,
	},
	PalletId,
};
use frame_system::EnsureSigned;
use pallet_nfts::{ItemConfig, PalletFeatures};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	DispatchResult,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;
type AccountId = <Test as frame_system::Config>::AccountId;
type ItemId = <Test as pallet_nfts::Config>::ItemId;
type CollectionId = <Test as pallet_nfts::Config>::CollectionId;

// Configure a mock runtime to test the pallet.
construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		NftFractions: pallet_nft_fractionalization,
		Assets: pallet_assets,
		Balances: pallet_balances,
		Nfts: pallet_nfts,
	}
);
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
	type AccountId = u64;
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
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ConstU32<50>;
	type ReserveIdentifier = [u8; 8];
}

impl pallet_assets::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Balance = u64;
	type RemoveItemsLimit = ConstU32<1000>;
	type AssetId = u32;
	type AssetIdParameter = u32;
	type Currency = Balances;
	type CreateOrigin = AsEnsureOriginWithArg<EnsureSigned<u64>>;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type AssetDeposit = ConstU64<1>;
	type AssetAccountDeposit = ConstU64<10>;
	type MetadataDepositBase = ConstU64<1>;
	type MetadataDepositPerByte = ConstU64<1>;
	type ApprovalDeposit = ConstU64<1>;
	type StringLimit = ConstU32<50>;
	type Freezer = ();
	type Extra = ();
	type CallbackHandle = ();
	type WeightInfo = ();
	pallet_assets::runtime_benchmarks_enabled! {
		type BenchmarkHelper = ();
	}
}

parameter_types! {
	pub storage Features: PalletFeatures = PalletFeatures::all_enabled();
}

const LOCKED_NFT_KEY: &[u8; 6] = b"locked";

pub struct TestLocker;
impl Locker<CollectionId, ItemId> for TestLocker {
	fn is_locked(collection: CollectionId, item: ItemId) -> bool {
		Nfts::attribute(&collection, &item, &AttributeNamespace::Pallet, LOCKED_NFT_KEY).is_some()
	}
}

impl pallet_nfts::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type CollectionId = u32;
	type ItemId = u32;
	type Currency = Balances;
	type CreateOrigin = AsEnsureOriginWithArg<frame_system::EnsureSigned<u64>>;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type Locker = TestLocker;
	type CollectionDeposit = ConstU64<2>;
	type ItemDeposit = ConstU64<1>;
	type MetadataDepositBase = ConstU64<1>;
	type AttributeDepositBase = ConstU64<1>;
	type DepositPerByte = ConstU64<1>;
	type StringLimit = ConstU32<50>;
	type KeyLimit = ConstU32<50>;
	type ValueLimit = ConstU32<50>;
	type ApprovalsLimit = ConstU32<10>;
	type ItemAttributesApprovalsLimit = ConstU32<2>;
	type MaxTips = ConstU32<10>;
	type MaxDeadlineDuration = ConstU64<10000>;
	type Features = Features;
	type WeightInfo = ();
	pallet_nfts::runtime_benchmarks_enabled! {
		type Helper = ();
	}
}

parameter_types! {
	pub const NftFractionsPalletId: PalletId = PalletId(*b"fraction");
}

pub struct TestLockableNonfungible;
impl LockableNonfungible<CollectionId, ItemId> for TestLockableNonfungible {
	fn lock(collection: &CollectionId, item: &ItemId) -> DispatchResult {
		<Nfts as Mutate<AccountId, ItemConfig>>::set_attribute(
			collection,
			item,
			LOCKED_NFT_KEY,
			&[1],
		)
	}
	fn unlock(collection: &CollectionId, item: &ItemId) -> DispatchResult {
		<Nfts as Mutate<AccountId, ItemConfig>>::clear_attribute(collection, item, LOCKED_NFT_KEY)
	}
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = Balances;
	type NftCollectionId = <Self as pallet_nfts::Config>::CollectionId;
	type NftId = <Self as pallet_nfts::Config>::ItemId;
	type AssetBalance = <Self as pallet_balances::Config>::Balance;
	type AssetId = <Self as pallet_assets::Config>::AssetId;
	type Assets = Assets;
	type Nfts = Nfts;
	type PalletId = NftFractionsPalletId;
	type NftLocker = TestLockableNonfungible;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}
