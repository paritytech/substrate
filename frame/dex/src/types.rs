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

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

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
pub enum MultiAssetId<AssetId> {
	#[default]
	Native,
	Asset(AssetId),
}

#[derive(Decode, Encode, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo)]
pub struct PoolInfo<AccountId, PoolAssetId> {
	/// Owner of the pool
	pub owner: AccountId,
	/// Liquidity pool asset
	pub lp_token: PoolAssetId,
}
