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

//! The traits for putting freezes within a single fungible token class.

use scale_info::TypeInfo;
use sp_runtime::DispatchResult;

/// Trait for inspecting a fungible asset which can be frozen. Freezing is essentially setting a
/// minimum balance below which the total balance (inclusive of any funds placed on hold) may not
/// be normally allowed to drop. Generally, freezers will provide an "update" function such that
/// if the total balance does drop below the limit, then the freezer can update their housekeeping
/// accordingly.
pub trait Inspect<AccountId>: super::Inspect<AccountId> {
	/// An identifier for a freeze.
	type Id: codec::Encode + TypeInfo + 'static;

	/// Amount of funds held in reserve by `who` for the given `id`.
	fn balance_frozen(asset: Self::AssetId, id: &Self::Id, who: &AccountId) -> Self::Balance;

	/// The amount of the balance which can become frozen. Defaults to `total_balance()`.
	fn balance_freezable(asset: Self::AssetId, who: &AccountId) -> Self::Balance {
		Self::total_balance(asset, who)
	}

	/// Returns `true` if it's possible to introduce a freeze for the given `id` onto the
	/// account of `who`. This will be true as long as the implementor supports as many
	/// concurrent freeze locks as there are possible values of `id`.
	fn can_freeze(asset: Self::AssetId, id: &Self::Id, who: &AccountId) -> bool;
}

/// Trait for introducing, altering and removing locks to freeze an account's funds so they never
/// go below a set minimum.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Prevent actions which would reduce the balance of the account of `who` below the given
	/// `amount` and identify this restriction though the given `id`. Unlike `extend_freeze`, any
	/// outstanding freeze in place for `who` under the `id` are dropped.
	///
	/// If `amount` is zero, it is equivalent to using `thaw`.
	///
	/// Note that `amount` can be greater than the total balance, if desired.
	fn set_freeze(
		asset: Self::AssetId,
		id: &Self::Id,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;

	/// Prevent the balance of the account of `who` from being reduced below the given `amount` and
	/// identify this restriction though the given `id`. Unlike `set_freeze`, this does not
	/// counteract any pre-existing freezes in place for `who` under the `id`. Also unlike
	/// `set_freeze`, in the case that `amount` is zero, this is no-op and never fails.
	///
	/// Note that more funds can be locked than the total balance, if desired.
	fn extend_freeze(
		asset: Self::AssetId,
		id: &Self::Id,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;

	/// Remove an existing lock.
	fn thaw(asset: Self::AssetId, id: &Self::Id, who: &AccountId) -> DispatchResult;
}
