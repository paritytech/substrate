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

use crate::{Config, MaxChecking};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::Currency, BoundedVec, EqNoBound, PartialEqNoBound, RuntimeDebugNoBound,
};
use scale_info::TypeInfo;
use sp_staking::EraIndex;
use sp_std::prelude::*;

pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
/// An unstake request.
#[derive(
	Encode, Decode, EqNoBound, PartialEqNoBound, Clone, TypeInfo, RuntimeDebugNoBound, MaxEncodedLen,
)]
#[scale_info(skip_type_params(T))]
pub struct UnstakeRequest<T: Config> {
	/// This list of stashes being processed in this request, and their corresponding deposit.
	pub(crate) stashes: BoundedVec<(T::AccountId, BalanceOf<T>), T::BatchSize>,
	/// The list of eras for which they have been checked.
	pub(crate) checked: BoundedVec<EraIndex, MaxChecking<T>>,
}
