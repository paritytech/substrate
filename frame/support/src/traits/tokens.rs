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

//! Traits for working with tokens and their associated datastructures.

pub mod currency;
pub mod fungible;
pub mod fungibles;
pub mod imbalance;
mod misc;
pub mod nonfungible;
pub mod nonfungible_v2;
pub mod nonfungibles;
pub mod nonfungibles_v2;
pub use imbalance::Imbalance;
pub mod pay;
pub use misc::{
	AssetId, Balance, BalanceStatus, ConversionFromAssetBalance, ConversionToAssetBalance,
	ConvertRank, DepositConsequence, ExistenceRequirement, Fortitude, GetSalary, Locker, Precision,
	Preservation, Provenance, Restriction, WithdrawConsequence, WithdrawReasons,
};
pub use pay::{Pay, PayFromAccount, PaymentStatus};
