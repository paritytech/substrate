// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Runtime API definition for transaction payment pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};
pub use pallet_nomination_pools::PoolId;
use sp_std::prelude::*;

/// Some points and balance bundled together.
#[derive(Encode, Decode, PartialEq, Eq)]
pub struct PointsAndBalance<B> {
	pub points: B,
	pub balance: B,
}

/// Stats of a member in a pool.
#[derive(Encode, Decode, PartialEq, Eq)]
pub struct MemberStatus<B> {
	/// Active stake, both in points and balance.
	///
	/// The balance value is evaluated on the fly and can change based on external factors, such as
	/// slash.
	pub active: PointsAndBalance<B>,
	/// Unbonding stake, per era, both in points and balance.
	///
	/// The balance value is evaluated on the fly and can change based on external factors, such as
	/// slash.
	pub unbonding: Vec<(u32, PointsAndBalance<B>)>,
	/// The pending rewards of this member in their existing pool.
	pub pending_rewards: B,
	/// The pool to which this member belongs.
	pub pool_id: PoolId,
}

sp_api::decl_runtime_apis! {
	pub trait NominationPoolsApi<AccountId, Balance> where AccountId: Codec, Balance: Codec
	{
		/// Returns the pending rewards for the given member.
		fn pending_rewards(member: AccountId) -> Balance;
	}
}
