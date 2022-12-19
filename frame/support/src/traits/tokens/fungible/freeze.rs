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

use super::*;

/// Trait for inspecting a fungible asset which can be frozen. Freezing is essentially setting a
/// minimum balance bellow which the total balance (inclusive of any funds placed on hold) may not
/// be normally allowed to drop. Generally, freezers will provide an "update" function such that
/// if the total balance does drop below the limit, then the freezer can update their housekeeping
/// accordingly.
pub trait InspectFreeze<AccountId>: Inspect<AccountId> {
	/// An identifier for a freeze.
	type Id: codec::Encode + TypeInfo + 'static;

	/// Amount of funds held in reserve by `who` for the given `id`.
	fn balance_frozen(id: &Self::Id, who: &AccountId) -> Self::Balance;

	/// Returns `true` if it's possible to introduce a freeze for the given `id` onto the
	/// account of `who`. This will be true as long as the implementor supports as many
	/// concurrent freeze locks as there are possible values of `id`.
	fn can_freeze(id: &Self::Id, who: &AccountId) -> bool;
}

/// Trait for introducing, altering and removing locks to freeze an account's funds so they never
/// go below a set minimum.
pub trait MutateFreeze<AccountId>: InspectFreeze<AccountId> {
	/// Create or replace the freeze lock for `id` on account `who`.
	///
	/// The lock applies only for attempts to reduce the balance for the `applicable_circumstances`.
	/// Note that more funds can be locked than the total balance, if desired.
	fn set_lock(id: &Self::Id, who: &AccountId, amount: Self::Balance)
		-> Result<(), DispatchError>;

	/// Changes a balance lock (selected by `id`) so that it becomes less liquid in all
	/// parameters or creates a new one if it does not exist.
	///
	/// Calling `extend_lock` on an existing lock differs from `set_lock` in that it
	/// applies the most severe constraints of the two, while `set_lock` replaces the lock
	/// with the new parameters. As in, `extend_lock` will set the maximum `amount`.
	fn extend_lock(id: &Self::Id, who: &AccountId, amount: Self::Balance);

	/// Remove an existing lock.
	fn remove(id: &Self::Id, who: &AccountId);
}
