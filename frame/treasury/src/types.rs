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

use codec::{Decode, Encode, FullCodec, MaxEncodedLen};
use core::{fmt::Display, marker::PhantomData};
use frame_support::{traits::tokens::Balance, RuntimeDebug};
use scale_info::TypeInfo;

// At the moment when using PartialEq on AssetId, native
// is expected to be loweset.
pub trait MultiAssetBalanceConverter {
	type AssetId;
	type NativeBalance: Balance;
	type AssetBalance: Balance;
	type NativeOrAssetBalance;

	fn get_native(balance: Self::NativeBalance) -> Self::NativeOrAssetBalance;

	fn try_convert_asset(
		asset: Self::NativeOrAssetBalance,
	) -> Result<(Self::AssetId, Self::AssetBalance), ()>;

	fn try_convert_native(asset: Self::NativeOrAssetBalance) -> Result<Self::NativeBalance, ()>;

	fn into_multiasset_balance(
		asset: Self::AssetId,
		balance: Self::AssetBalance,
	) -> Self::NativeOrAssetBalance;
}

/// An implementation of MultiAssetId that chooses between Native and an asset.
#[derive(
	Decode,
	Encode,
	PartialEq,
	Eq,
	MaxEncodedLen,
	TypeInfo,
	Clone,
	Copy,
	Ord,
	PartialOrd,
	RuntimeDebug,
)]
pub enum NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance> {
	/// Native asset. For example on statemint this would be dot.
	Native(NativeBalance),
	Asset(AssetId, AssetBalance),
}

pub struct NativeOrAssetIdConverter<AssetId, NativeBalance, AssetBalance> {
	_phantom: PhantomData<AssetId>,
	_phantom2: PhantomData<NativeBalance>,
	_phantom3: PhantomData<AssetBalance>,
}

impl<AssetId, NativeBalance, AssetBalance> MultiAssetBalanceConverter
	for NativeOrAssetIdConverter<AssetId, NativeBalance, AssetBalance>
{
	type AssetId = AssetId;
	type NativeBalance = NativeBalance;
	type AssetBalance = AssetBalance;
	type NativeOrAssetBalance = NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance>;
	fn get_native(
		balance: NativeBalance,
	) -> NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance> {
		NativeOrAssetBalance::Native(balance)
	}

	fn into_multiasset_balance(
		asset: AssetId,
		balance: AssetBalance,
	) -> NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance> {
		NativeOrAssetBalance::Asset(asset, balance)
	}

	fn try_convert_native(
		asset: NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance>,
	) -> Result<NativeBalance, ()> {
		match asset {
			NativeOrAssetBalance::Asset(_asset, _balance) => Err(()),
			NativeOrAssetBalance::Native(balance) => Ok(balance),
		}
	}

	fn try_convert_asset(
		asset: NativeOrAssetBalance<AssetId, NativeBalance, AssetBalance>,
	) -> Result<(AssetId, AssetBalance), ()> {
		match asset {
			NativeOrAssetBalance::Asset(asset, balance) => Ok((asset, balance)),
			NativeOrAssetBalance::Native(balance) => Err(()),
		}
	}
}

// impl<AssetId, B, C> Display for NativeOrAssetBalance<AssetId, B, C> {
// 	fn fmt(&self, _: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
// 		todo!()
// 	}
// }
