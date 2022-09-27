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

//! Types used in the Fast Unstake pallet.

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::{Currency, Get},
	BoundedVec, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_staking::EraIndex;
use sp_std::{fmt::Debug, prelude::*};

pub type BalanceOf<T> = <<T as pallet_staking::Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::Balance;

/// An unstake request.
#[derive(
	Encode, Decode, EqNoBound, PartialEqNoBound, Clone, TypeInfo, RuntimeDebugNoBound, MaxEncodedLen,
)]
pub struct UnstakeRequest<
	AccountId: Eq + PartialEq + Debug,
	MaxChecked: Get<u32>,
	Balance: PartialEq + Debug,
> {
	/// Their stash account.
	pub(crate) stash: AccountId,
	/// The list of eras for which they have been checked.
	pub(crate) checked: BoundedVec<EraIndex, MaxChecked>,
	/// Deposit to be slashed if the unstake was unsuccessful.
	pub(crate) deposit: Balance,
}
