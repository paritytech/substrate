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

/// Trait describing something that implements a hook for any operations to perform when a staker is
/// slashed.
pub trait OnStakerSlash<AccountId, Balance> {
	/// A hook for any operations to perform when a staker is slashed.
	///
	/// # Arguments
	///
	/// * `stash` - The stash of the staker whom the slash was applied to.
	/// * `slashed_active` - The new bonded balance of the staker after the slash was applied.
	/// * `slashed_unlocking` - A map of slashed eras, and the balance of that unlocking chunk after
	///   the slash is applied. Any era not present in the map is not affected at all.
	fn on_slash(
		stash: &AccountId,
		slashed_active: Balance,
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

	/// The minimum amount required to bond in order to be a nominator. This does not necessarily
	/// mean the nomination will be counted in an election, but instead just enough to be stored as
	/// a nominator. In other words, this is the minimum amount to register the intention to
	/// nominate.
	fn minimum_bond() -> Self::Balance;

	/// Number of eras that staked funds must remain bonded for.
	///
	/// # Note
	///
	/// This must be strictly greater than the staking systems slash deffer duration.
	fn bonding_duration() -> EraIndex;

	/// The current era index.
	///
	/// This should be the latest planned era that the staking system knows about.
	fn current_era() -> EraIndex;

	/// The amount of active stake that `stash` has in the staking system.
	fn active_stake(stash: &Self::AccountId) -> Option<Self::Balance>;

	/// The total stake that `stash` has in the staking system. This includes the
	/// [`Self::active_stake`], and any funds currently in the process of unbonding via
	/// [`Self::unbond`].
	///
	/// # Note
	///
	/// This is only guaranteed to reflect the amount locked by the staking system. If there are
	/// non-staking locks on the bonded pair's balance this may not be accurate.
	fn total_stake(stash: &Self::AccountId) -> Option<Self::Balance>;

	/// Bond (lock) `value` of `stash`'s balance. `controller` will be set as the account
	/// controlling `stash`. This creates what is referred to as "bonded pair".
	fn bond(
		stash: Self::AccountId,
		controller: Self::AccountId,
		value: Self::Balance,
		payee: Self::AccountId,
	) -> DispatchResult;

	/// Have `controller` nominate `validators`.
	fn nominate(
		controller: Self::AccountId,
		validators: sp_std::vec::Vec<Self::AccountId>,
	) -> DispatchResult;

	/// Chill `stash`.
	fn chill(controller: Self::AccountId) -> DispatchResult;

	/// Bond some extra amount in the _Stash_'s free balance against the active bonded balance of
	/// the account. The amount extra actually bonded will never be more than the _Stash_'s free
	/// balance.
	fn bond_extra(stash: Self::AccountId, extra: Self::Balance) -> DispatchResult;

	/// Schedule a portion of the active bonded balance to be unlocked at era
	/// [Self::current_era] + [`Self::bonding_duration`].
	///
	/// Once the unlock era has been reached, [`Self::withdraw_unbonded`] can be called to unlock
	/// the funds.
	///
	/// The amount of times this can be successfully called is limited based on how many distinct
	/// eras funds are schedule to unlock in. Calling [`Self::withdraw_unbonded`] after some unlock
	/// schedules have reached their unlocking era should allow more calls to this function.
	fn unbond(stash: Self::AccountId, value: Self::Balance) -> DispatchResult;

	/// Unlock any funds schedule to unlock before or at the current era.
	///
	/// Returns whether the stash was killed because of this withdraw or not.
	fn withdraw_unbonded(
		stash: Self::AccountId,
		num_slashing_spans: u32,
	) -> Result<bool, DispatchError>;

	/// Get the nominations of a stash, if they are a nominator, `None` otherwise.
	#[cfg(feature = "runtime-benchmarks")]
	fn nominations(who: Self::AccountId) -> Option<sp_std::prelude::Vec<Self::AccountId>>;
}
