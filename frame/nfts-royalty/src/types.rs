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

//! Various basic types for use in the NFTs Royalty pallet.

use super::*;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::Permill;

pub(super) type DepositBalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;

pub(super) type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;

pub(super) type ItemPrice<T> = BalanceOf<T>;

/// Stores the details of an item with royalty.
#[derive(Decode, Encode, Clone, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo, Debug)]
pub struct RoyaltyDetails<AccountId> {
	/// Royalty percentage for item.
	pub royalty_recipient_percentage: Permill,

	/// Account beneficiary of the royalty.
	pub royalty_recipient: AccountId,
}
/// Stores the details of an item with royalty.
#[derive(Decode, Encode, Clone, Default, PartialEq, Eq, MaxEncodedLen, TypeInfo, Debug)]
#[scale_info(skip_type_params(MaxRecipients))]
pub struct RoyaltyConfig<AccountId, BalanceOf, MaxRecipients: Get<u32>> {
	/// Royalty percentage for item.
	pub royalty_percentage: Permill,

	/// List of accounts that the royalty will go to and its correspondent
	/// percentage of the royalties.
	pub recipients: BoundedVec<RoyaltyDetails<AccountId>, MaxRecipients>,

	/// The account that will pay the deposit
	pub depositor: Option<AccountId>,

	/// The amount held in reserve of the `depositor`,
	/// to be returned once this royaltiy is removed.
	pub deposit: BalanceOf,
}
