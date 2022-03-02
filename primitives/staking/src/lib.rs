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

#![cfg_attr(not(feature = "std"), no_std)]

//! A crate which contains primitives that are useful for implementation that uses staking
//! approaches in general. Definitions related to sessions, slashing, etc go here.
use sp_runtime::{DispatchError, DispatchResult};
use sp_std::collections::btree_map::BTreeMap;

pub mod offence;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

/// Counter for the number of eras that have passed.
pub type EraIndex = u32;

/// Trait for a hook for any operations to perform while a staker is being slashed.
pub trait OnStakerSlash<AccountId, Balance> {
	/// A hook for any operations to perform while a staker is being slashed.
	///
	/// # Arguments
	///
	/// * `stash` - The stash of the staker whom the slash was applied to.
	/// * `slashed_bonded` - The new bonded balance of the staker after the slash was applied.
	/// * `slashed_unlocking` - A map from eras that the staker is unbonding in to the new balance
	///   after the slash was applied.
	fn on_slash(
		stash: &AccountId,
		slashed_bonded: Balance,
		slashed_unlocking: &BTreeMap<EraIndex, Balance>,
	);
}

impl<AccountId, Balance> OnStakerSlash<AccountId, Balance> for () {
	fn on_slash(_: &AccountId, _: Balance, _: &BTreeMap<EraIndex, Balance>) {
		// Nothing to do here
	}
}

/// Trait for communication with the staking pallet.
pub trait StakingInterface {
	/// Balance type used by the staking system.
	type Balance;

	/// AccountId type used by the staking system
	type AccountId;

	type LookupSource;

	/// The minimum amount necessary to bond to be a nominator. This does not necessarily mean the
	/// nomination will be counted in an election, but instead just enough to be stored as a
	/// nominator (e.g. in the bags-list of polkadot)
	fn minimum_bond() -> Self::Balance;

	/// Number of eras that staked funds must remain bonded for. NOTE: it is assumed that this is
	/// always strictly greater than the slash deffer duration.
	fn bonding_duration() -> EraIndex;

	/// The current era for the staking system.
	fn current_era() -> EraIndex;

	/// Balance `controller` has bonded for nominating.
	fn bonded_balance(controller: &Self::AccountId) -> Option<Self::Balance>;

	/// Balance `controller` has locked by the staking system. This is the bonded funds and the
	/// unlocking funds and thus is a superset of bonded funds.
	fn locked_balance(controller: &Self::AccountId) -> Option<Self::Balance>;

	fn bond_extra(controller: Self::AccountId, extra: Self::Balance) -> DispatchResult;

	fn unbond(controller: Self::AccountId, value: Self::Balance) -> DispatchResult;

	/// Withdraw unbonded funds from bonded user.
	fn withdraw_unbonded(
		controller: Self::AccountId,
		num_slashing_spans: u32,
	) -> Result<u64, DispatchError>;

	/// Bond the funds and create a `stash` and `controller`, a bond of `value`, and `payee` account
	/// as the reward destination.
	fn bond(
		stash: Self::AccountId,
		controller: Self::AccountId,
		value: Self::Balance,
		payee: Self::AccountId,
	) -> DispatchResult;

	/// Have `controller` nominate `validators`.
	fn nominate(
		controller: Self::AccountId,
		validators: sp_std::vec::Vec<Self::LookupSource>,
	) -> DispatchResult;
}
