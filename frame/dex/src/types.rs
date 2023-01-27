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

use core::{fmt::Display, marker::PhantomData};
use sp_std::fmt::Formatter;

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

/// Stores what lp_token a particular pool has.
#[derive(Decode, Encode, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo)]
pub struct PoolInfo<PoolAssetId> {
	/// Liquidity pool asset
	pub lp_token: PoolAssetId,
}

// At the moment when using PartialEq on AssetId, native
// is expected to be loweset.
pub trait MultiAssetIdConverter<MultiAssetId, AssetId> {
	fn get_native() -> MultiAssetId;

	fn try_convert(asset: MultiAssetId) -> Result<AssetId, ()>;

	fn into_multiasset_id(asset: AssetId) -> MultiAssetId;
}

/// An implementation of MultiAssetId that chooses between Native and an asset.
#[derive(
	Decode,
	Encode,
	Default,
	PartialEq,
	Eq,
	MaxEncodedLen,
	TypeInfo,
	Clone,
	Copy,
	Debug,
	Ord,
	PartialOrd,
)]
pub enum NativeOrAssetId<AssetId> {
	/// Native asset. For example on statemint this would be dot.
	#[default]
	Native,
	Asset(AssetId),
}

pub struct NativeOrAssetIdConverter<AssetId> {
	_phantom: PhantomData<AssetId>,
}

impl<AssetId> MultiAssetIdConverter<NativeOrAssetId<AssetId>, AssetId>
	for NativeOrAssetIdConverter<AssetId>
{
	fn get_native() -> NativeOrAssetId<AssetId> {
		NativeOrAssetId::Native
	}

	fn try_convert(asset: NativeOrAssetId<AssetId>) -> Result<AssetId, ()> {
		match asset {
			NativeOrAssetId::Asset(asset) => Ok(asset),
			NativeOrAssetId::Native => Err(()),
		}
	}

	fn into_multiasset_id(asset: AssetId) -> NativeOrAssetId<AssetId> {
		NativeOrAssetId::Asset(asset)
	}
}

impl<AssetId> Display for NativeOrAssetId<AssetId> {
	fn fmt(&self, _: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
		todo!()
	}
}
