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

//! Traits for dealing with accounts.

use crate::dispatch::DispatchResult;

/// Trait for creating an asset account with a deposit taken from a specified by client depositor.
pub trait Touch<AssetId, AccountId> {
	/// The type for currency units of the deposit.
	type Balance;
	/// The deposit amount of a native currency required for creating an asset account.
	fn deposit() -> Option<Self::Balance>;
	/// Create an account for `who` of the `asset` with a deposit taken from the `depositor`.
	fn touch(asset: AssetId, who: AccountId, depositor: AccountId) -> DispatchResult;
}
