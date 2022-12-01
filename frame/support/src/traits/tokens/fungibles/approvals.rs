// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Inspect and Mutate traits for Asset approvals

use crate::dispatch::DispatchResult;
pub trait Inspect<AccountId>: super::Inspect<AccountId> {
	// Check the amount approved by an owner to be spent by a delegate
	fn allowance(asset: Self::AssetId, owner: &AccountId, delegate: &AccountId) -> Self::Balance;
}

pub trait Mutate<AccountId>: Inspect<AccountId> {
	// Aprove a delegate account to spend an amount of tokens owned by an owner
	fn approve(
		asset: Self::AssetId,
		owner: &AccountId,
		delegate: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;

	// Transfer from a delegate account an amount approved by the owner of the asset
	fn transfer_from(
		asset: Self::AssetId,
		owner: &AccountId,
		delegate: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;
}
