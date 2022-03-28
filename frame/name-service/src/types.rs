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

//! Types used in the Name Service pallet.

use crate::*;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{traits::Currency, RuntimeDebug};
use scale_info::TypeInfo;

// Allows easy access our Pallet's `Balance` and `NegativeImbalance` type.
//
// Comes from `Currency` interface.
pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

pub type RegistrationOf<T> = Registration<
	<T as frame_system::Config>::AccountId,
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;

pub type NameHash = [u8; 32];
pub type CommitmentHash = [u8; 32];

#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct Commitment<AccountId, Balance, BlockNumber> {
	pub who: AccountId,
	pub when: BlockNumber,
	pub deposit: Balance,
}

#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct Registration<AccountId, Balance, BlockNumber> {
	pub owner: AccountId,
	pub registrant: Option<AccountId>,
	pub expiry: Option<BlockNumber>,
	pub deposit: Option<Balance>,
}
