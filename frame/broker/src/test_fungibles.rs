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

use frame_support::{
	parameter_types,
	traits::{ConstU16, ConstU64, fungibles, tokens::{self, Preservation, Fortitude, Provenance, DepositConsequence, WithdrawConsequence}}
};
use sp_std::collections::btree_map::BTreeMap;
use codec::{Encode, Decode};
use sp_core::{ConstU32, TypedGet, Get};

parameter_types! {
	static TestAssetOf: BTreeMap<(u32, Vec<u8>), Vec<u8>> = Default::default();
	static TestBalanceOf: BTreeMap<(u32, Vec<u8>, Vec<u8>), Vec<u8>> = Default::default();
}

pub struct TestFungibles<Instance, AccountId, AssetId, MinimumBalance>(core::marker::PhantomData<(Instance, AccountId, AssetId, MinimumBalance)>);
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
