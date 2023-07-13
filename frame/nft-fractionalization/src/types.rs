// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Various basic types for use in the Nft fractionalization pallet.

use super::*;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::traits::{fungible::Inspect as FunInspect, fungibles::Inspect};
use scale_info::TypeInfo;
use sp_runtime::traits::StaticLookup;

pub type AssetIdOf<T> = <<T as Config>::Assets as Inspect<<T as SystemConfig>::AccountId>>::AssetId;
pub type AssetBalanceOf<T> =
	<<T as Config>::Assets as Inspect<<T as SystemConfig>::AccountId>>::Balance;
pub type DepositOf<T> =
	<<T as Config>::Currency as FunInspect<<T as SystemConfig>::AccountId>>::Balance;
pub type AccountIdLookupOf<T> = <<T as SystemConfig>::Lookup as StaticLookup>::Source;

/// Stores the details of a fractionalized item.
#[derive(Decode, Encode, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo)]
pub struct Details<AssetId, Fractions, Deposit, AccountId> {
	/// Minted asset.
	pub asset: AssetId,

	/// Number of fractions minted.
	pub fractions: Fractions,

	/// Reserved deposit for creating a new asset.
	pub deposit: Deposit,

	/// Account that fractionalized an item.
	pub asset_creator: AccountId,
}

/// Benchmark Helper
#[cfg(feature = "runtime-benchmarks")]
pub trait BenchmarkHelper<AssetId, CollectionId, ItemId> {
	/// Returns an asset id from a given integer.
	fn asset(id: u32) -> AssetId;
	/// Returns a collection id from a given integer.
	fn collection(id: u32) -> CollectionId;
	/// Returns an nft id from a given integer.
	fn nft(id: u32) -> ItemId;
}

#[cfg(feature = "runtime-benchmarks")]
impl<AssetId, CollectionId, ItemId> BenchmarkHelper<AssetId, CollectionId, ItemId> for ()
where
	AssetId: From<u32>,
	CollectionId: From<u32>,
	ItemId: From<u32>,
{
	fn asset(id: u32) -> AssetId {
		id.into()
	}
	fn collection(id: u32) -> CollectionId {
		id.into()
	}
	fn nft(id: u32) -> ItemId {
		id.into()
	}
}
