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

#![cfg(test)]

use frame_support::{
	parameter_types,
	traits::{ConstU16, ConstU64, fungibles, fungible::ItemOf, tokens::{self, Preservation, Fortitude, Provenance, DepositConsequence, WithdrawConsequence}}
};
use sp_core::{H256, Get, ConstU32, TypedGet};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Broker: crate,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
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
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ConstU16<42>;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

pub struct TestFungibles<Instance, AccountId, AssetId, MinimumBalance>(core::marker::PhantomData<(Instance, AccountId, AssetId, MinimumBalance)>);

use std::collections::HashMap;

parameter_types! {
	static TestAssetOf: HashMap<(u32, Vec<u8>), Vec<u8>> = Default::default();
	static TestBalanceOf: HashMap<(u32, Vec<u8>, Vec<u8>), Vec<u8>> = Default::default();
}

use codec::{Encode, Decode};
impl<
	Instance: Get<u32>,
	AccountId: Encode,
	AssetId: tokens::AssetId + Copy,
	MinimumBalance: TypedGet,
> fungibles::Inspect<AccountId> for TestFungibles<Instance, AccountId, AssetId, MinimumBalance>
where
	MinimumBalance::Type: tokens::Balance,

{
	type AssetId = AssetId;
	type Balance = MinimumBalance::Type;

	fn total_issuance(asset: Self::AssetId) -> Self::Balance {
		TestAssetOf::get().get(&(Instance::get(), asset.encode()))
		.and_then(|data| Decode::decode(&mut &data[..]).ok())
		.unwrap_or_default()
	}

	fn active_issuance(asset: Self::AssetId) -> Self::Balance {
		Self::total_issuance(asset)
	}

	/// The minimum balance any single account may have.
	fn minimum_balance(asset: Self::AssetId) -> Self::Balance {
		MinimumBalance::get()
	}

	fn total_balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance {
		TestBalanceOf::get().get(&(Instance::get(), asset.encode(), who.encode()))
		.and_then(|data| Decode::decode(&mut &data[..]).ok())
		.unwrap_or_default()
	}

	fn balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance {
		Self::total_balance(asset, who)
	}

	fn reducible_balance(
		asset: Self::AssetId,
		who: &AccountId,
		_preservation: Preservation,
		_force: Fortitude,
	) -> Self::Balance {
		Self::total_balance(asset, who)
	}

	fn can_deposit(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		_provenance: Provenance,
	) -> DepositConsequence {
		if !Self::asset_exists(asset) {
			return DepositConsequence::UnknownAsset;
		}
		if amount + Self::balance(asset, who) < Self::minimum_balance(asset) {
			return DepositConsequence::BelowMinimum;
		}
		DepositConsequence::Success
	}

	fn can_withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance> {
		if Self::reducible_balance(asset, who, Preservation::Expendable, Fortitude::Polite) < amount {
			return WithdrawConsequence::BalanceLow;
		}
		if Self::total_balance(asset, who) < Self::minimum_balance(asset) + amount {
			return WithdrawConsequence::WouldDie;
		}
		WithdrawConsequence::Success
	}

	fn asset_exists(asset: Self::AssetId) -> bool {
		TestAssetOf::get().contains_key(&(Instance::get(), asset.encode()))
	}
}

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Currency = ItemOf<TestFungibles<(), u64, (), ConstU64<0>>, (), u64>;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}
