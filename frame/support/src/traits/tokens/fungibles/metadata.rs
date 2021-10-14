// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Inspect and Mutate traits for Asset metadata

use crate::dispatch::DispatchResult;
use sp_std::vec::Vec;

pub trait Inspect<AccountId>: super::Inspect<AccountId> {
	// Get name for an AssetId.
	fn name(asset: Self::AssetId) -> Vec<u8>;
	// Get symbol for an AssetId.
	fn symbol(asset: Self::AssetId) -> Vec<u8>;
	// Get decimals for an AssetId.
	fn decimals(asset: Self::AssetId) -> u8;
}

pub trait Mutate<AccountId>: Inspect<AccountId> {
	// Set name, symbol and decimals for a given assetId.
	fn set(
		asset: Self::AssetId,
		from: &AccountId,
		name: Vec<u8>,
		symbol: Vec<u8>,
		decimals: u8,
	) -> DispatchResult;
}
