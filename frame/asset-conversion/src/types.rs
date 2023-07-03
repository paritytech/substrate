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
use core::marker::PhantomData;
use sp_std::cmp::Ordering;

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
	/// Returns the MultiAssetId reperesenting the native currency of the chain.
	fn get_native() -> MultiAssetId;

	/// Returns true if the given MultiAssetId is the native currency.
	fn is_native(asset: &MultiAssetId) -> bool;

	/// If it's not native, returns the AssetId for the given MultiAssetId.
	fn try_convert(asset: &MultiAssetId) -> Result<AssetId, ()>;

	/// Wrapps an AssetId as a MultiAssetId.
	fn into_multiasset_id(asset: &AssetId) -> MultiAssetId;
}

/// Benchmark Helper
#[cfg(feature = "runtime-benchmarks")]
pub trait BenchmarkHelper<AssetId> {
	/// Returns an asset id from a given integer.
	fn asset_id(asset_id: u32) -> AssetId;
}

#[cfg(feature = "runtime-benchmarks")]
impl<AssetId> BenchmarkHelper<AssetId> for ()
where
	AssetId: From<u32>,
{
	fn asset_id(asset_id: u32) -> AssetId {
		asset_id.into()
	}
}

/// An implementation of MultiAssetId that can be either Native or an asset.
#[derive(Decode, Encode, Default, MaxEncodedLen, TypeInfo, Clone, Copy, Debug)]
pub enum NativeOrAssetId<AssetId>
where
	AssetId: Ord,
{
	/// Native asset. For example, on statemint this would be dot.
	#[default]
	Native,
	/// A non-native asset id.
	Asset(AssetId),
}

impl<AssetId: Ord> Ord for NativeOrAssetId<AssetId> {
	fn cmp(&self, other: &Self) -> Ordering {
		match (self, other) {
			(Self::Native, Self::Native) => Ordering::Equal,
			(Self::Native, Self::Asset(_)) => Ordering::Less,
			(Self::Asset(_), Self::Native) => Ordering::Greater,
			(Self::Asset(id1), Self::Asset(id2)) => <AssetId as Ord>::cmp(id1, id2),
		}
	}
}
impl<AssetId: Ord> PartialOrd for NativeOrAssetId<AssetId> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(<Self as Ord>::cmp(self, other))
	}
}
impl<AssetId: Ord> PartialEq for NativeOrAssetId<AssetId> {
	fn eq(&self, other: &Self) -> bool {
		self.cmp(other) == Ordering::Equal
	}
}
impl<AssetId: Ord> Eq for NativeOrAssetId<AssetId> {}

/// Converts between a MultiAssetId and an AssetId
/// (or the native currency).
pub struct NativeOrAssetIdConverter<AssetId> {
	_phantom: PhantomData<AssetId>,
}

impl<AssetId: Ord + Clone> MultiAssetIdConverter<NativeOrAssetId<AssetId>, AssetId>
	for NativeOrAssetIdConverter<AssetId>
{
	fn get_native() -> NativeOrAssetId<AssetId> {
		NativeOrAssetId::Native
	}

	fn is_native(asset: &NativeOrAssetId<AssetId>) -> bool {
		*asset == Self::get_native()
	}

	fn try_convert(asset: &NativeOrAssetId<AssetId>) -> Result<AssetId, ()> {
		match asset {
			NativeOrAssetId::Asset(asset) => Ok(asset.clone()),
			NativeOrAssetId::Native => Err(()),
		}
	}

	fn into_multiasset_id(asset: &AssetId) -> NativeOrAssetId<AssetId> {
		NativeOrAssetId::Asset((*asset).clone())
	}
}
