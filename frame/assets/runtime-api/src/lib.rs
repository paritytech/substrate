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

//! Runtime API definition for assets pallet.
//! Currently supports only one rpc endpoint.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
	pub trait AssetsApi<AccountId, AssetBalance, AssetId> where
		AccountId: Codec,
		AssetBalance: Codec,
		AssetId: Codec
	{
		/// Returns the list of asset id and non-zero balances the AccountId has.
		fn account_balances(account: AccountId) -> Vec<(AssetId, AssetBalance)>;
	}
}
