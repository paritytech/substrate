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

//! The MultiCurrency trait.

use super::super::misc::{AssetId, Balance};
use crate::dispatch::DispatchResult;
use sp_runtime::{traits::MaybeSerializeDeserialize, FixedPointOperand};
use sp_std::fmt::Debug;

/// Abstraction over a fungible multi-currency system.
pub trait MultiCurrency<AccountId> {
	/// The currency identifier.
	type CurrencyId: AssetId;

	/// The balance of an account.
	type Balance: Balance + MaybeSerializeDeserialize + Debug + FixedPointOperand;

	/// Transfer some amount from one account to another.
	fn transfer(
		currency_id: Option<Self::CurrencyId>,
		source: &AccountId,
		dest: &AccountId,
		value: Self::Balance,
	) -> DispatchResult;
}
