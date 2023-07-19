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

use super::*;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

pub(super) type PoolIdOf<T> = (<T as Config>::MultiAssetId, <T as Config>::MultiAssetId);

/// Stores the lp_token asset id a particular pool has been assigned.
#[derive(Decode, Encode, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo)]
pub struct PoolInfo<PoolAssetId> {
	/// Liquidity pool asset
	pub lp_token: PoolAssetId,
}

/// A trait that converts between a MultiAssetId and either the native currency or an AssetId.
pub trait MultiAssetIdConverter<MultiAssetId, AssetId> {
	/// Returns the MultiAssetId representing the native currency of the chain.
	fn get_native() -> MultiAssetId;

	/// Returns true if the given MultiAssetId is the native currency.
	fn is_native(asset: &MultiAssetId) -> bool;

	/// If it's not native, returns the AssetId for the given MultiAssetId.
	fn try_convert(asset: &MultiAssetId) -> MultiAssetIdConversionResult<MultiAssetId, AssetId>;
}

/// Result of `MultiAssetIdConverter::try_convert`.
#[cfg_attr(feature = "std", derive(PartialEq, Debug))]
pub enum MultiAssetIdConversionResult<MultiAssetId, AssetId> {
	/// Input asset is successfully converted. Means that converted asset is supported.
	Converted(AssetId),
	/// Means that input asset is the chain's native asset, if it has one, so no conversion (see
	/// `MultiAssetIdConverter::get_native`).
	Native,
	/// Means input asset is not supported for pool.
	Unsupported(MultiAssetId),
}

/// Benchmark Helper
#[cfg(feature = "runtime-benchmarks")]
pub trait BenchmarkHelper<AssetId, MultiAssetId> {
	/// Returns an `AssetId` from a given integer.
	fn asset_id(asset_id: u32) -> AssetId;

	/// Returns a `MultiAssetId` from a given integer.
	fn multiasset_id(asset_id: u32) -> MultiAssetId;
}

#[cfg(feature = "runtime-benchmarks")]
impl<AssetId, MultiAssetId> BenchmarkHelper<AssetId, MultiAssetId> for ()
where
	AssetId: From<u32>,
	MultiAssetId: From<u32>,
{
	fn asset_id(asset_id: u32) -> AssetId {
		asset_id.into()
	}

	fn multiasset_id(asset_id: u32) -> MultiAssetId {
		asset_id.into()
	}
}

/// Trait for providing methods to swap between the various asset classes.
pub trait Swap<AccountId, Balance, MultiAssetId> {
	/// Swap exactly `amount_in` of asset `path[0]` for asset `path[1]`.
	/// If an `amount_out_min` is specified, it will return an error if it is unable to acquire
	/// the amount desired.
	///
	/// Withdraws the `path[0]` asset from `sender`, deposits the `path[1]` asset to `send_to`,
	/// respecting `keep_alive`.
	///
	/// If successful, returns the amount of `path[1]` acquired for the `amount_in`.
	fn swap_exact_tokens_for_tokens(
		sender: AccountId,
		path: Vec<MultiAssetId>,
		amount_in: Balance,
		amount_out_min: Option<Balance>,
		send_to: AccountId,
		keep_alive: bool,
	) -> Result<Balance, DispatchError>;

	/// Take the `path[0]` asset and swap some amount for `amount_out` of the `path[1]`. If an
	/// `amount_in_max` is specified, it will return an error if acquiring `amount_out` would be
	/// too costly.
	///
	/// Withdraws `path[0]` asset from `sender`, deposits `path[1]` asset to `send_to`,
	/// respecting `keep_alive`.
	///
	/// If successful returns the amount of the `path[0]` taken to provide `path[1]`.
	fn swap_tokens_for_exact_tokens(
		sender: AccountId,
		path: Vec<MultiAssetId>,
		amount_out: Balance,
		amount_in_max: Option<Balance>,
		send_to: AccountId,
		keep_alive: bool,
	) -> Result<Balance, DispatchError>;
}
