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

//! Runtime API definition for nomination-pools pallet.
//! Currently supports only one rpc endpoint.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Codec;
use pallet_nomination_pools::PoolId;

sp_api::decl_runtime_apis! {
	/// Runtime api for accessing information about nomination pools.
	pub trait NominationPoolsApi<AccountId, Balance>
		where
			AccountId: Codec,
			Balance: Codec,
	{
		/// Returns the pending rewards for the member that the AccountId was given for.
		fn pending_rewards(who: AccountId) -> Balance;

		/// Returns the equivalent balance of `points` for a given pool.
		fn points_to_balance(pool_id: PoolId, points: Balance) -> Balance;

		/// Returns the equivalent points of `new_funds` for a given pool.
		fn balance_to_points(pool_id: PoolId, new_funds: Balance) -> Balance;
	}
}
