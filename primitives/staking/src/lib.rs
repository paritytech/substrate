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

/// A generic representation of a staking implementation.
///
/// This interface uses the terminology of NPoS, but it is aims to be generic enough to cover other
/// implementations as well.
pub trait StakingInterface {
	/// Balance type used by the staking system.
	type Balance;

	/// AccountId type used by the staking system
	type AccountId;

	/// The minimum amount required to bond in order to set nomination intentions. This does not
	/// necessarily mean the nomination will be counted in an election, but instead just enough to
	/// be stored as a nominator. In other words, this is the minimum amount to register the
	/// intention to nominate.
	fn minimum_nominator_bond() -> Self::Balance;

	/// The minimum amount required to bond in order to set validation intentions.
	fn minimum_validator_bond() -> Self::Balance;

	/// Return an account that can be potentially controlled by `controller`.
	///
	/// ## Note
	///
	/// The controller abstraction is not permanent and might go away. Avoid using this as much as
	/// possible.
	fn can_control(controller: &Self::AccountId) -> Result<Self::AccountId, DispatchError>;

	/// Number of eras that staked funds must remain bonded for.
	fn bonding_duration() -> EraIndex;

	/// The current era index.
	///
	/// This should be the latest planned era that the staking system knows about.
	fn current_era() -> EraIndex;

	/// The amount of active stake `who` has in the staking system.
	fn active_stake(who: &Self::AccountId) -> Option<Self::Balance>;

	/// The total stake that `who` has in the staking system. This includes the
	/// [`Self::active_stake`], and any funds currently in the process of unbonding via
	/// [`Self::unbond`].
	///
	/// # Note
	///
	/// This is only guaranteed to reflect the amount locked by the staking system. If there are
	/// non-staking locks on the bonded pair's balance this may not be accurate.
	fn total_stake(who: &Self::AccountId) -> Option<Self::Balance>;

	fn is_unbonding(who: &Self::AccountId) -> bool {
		match (Self::active_stake(who), Self::total_stake(who)) {
			(Some(x), Some(y)) if x == y => true,
			_ => false
		}
	}

	fn fully_unbond(who: &Self::AccountId) -> DispatchResult {
		// TODO: active_stake and others should also return `Result`.
		Self::unbond(who, Self::active_stake(who).unwrap())
	}

	/// Bond (lock) `value` of `who`'s balance, while forwarding any rewards to `payee`.
	fn bond(who: &Self::AccountId, value: Self::Balance, payee: &Self::AccountId)
		-> DispatchResult;

	/// Have `who` nominate `validators`.
	fn nominate(
		who: &Self::AccountId,
		validators: sp_std::vec::Vec<Self::AccountId>,
	) -> DispatchResult;

	/// Chill `who`.
	fn chill(who: &Self::AccountId) -> DispatchResult;

	/// Bond some extra amount in `who`'s free balance against the active bonded balance of
	/// the account. The amount extra actually bonded will never be more than `who`'s free
	/// balance.
	fn bond_extra(who: &Self::AccountId, extra: Self::Balance) -> DispatchResult;

	/// Schedule a portion of the active bonded balance to be unlocked at era
	/// [Self::current_era] + [`Self::bonding_duration`].
	///
	/// Once the unlock era has been reached, [`Self::withdraw_unbonded`] can be called to unlock
	/// the funds.
	///
	/// The amount of times this can be successfully called is limited based on how many distinct
	/// eras funds are schedule to unlock in. Calling [`Self::withdraw_unbonded`] after some unlock
	/// schedules have reached their unlocking era should allow more calls to this function.
	fn unbond(stash: &Self::AccountId, value: Self::Balance) -> DispatchResult;

	/// Unlock any funds schedule to unlock before or at the current era.
	///
	/// Returns whether the stash was killed because of this withdraw or not.
	fn withdraw_unbonded(
		stash: Self::AccountId,
		num_slashing_spans: u32,
	) -> Result<bool, DispatchError>;

	/// The ideal number of active validators.
	fn desired_validator_count() -> u32;

	/// Whether or not there is an ongoing election.
	fn election_ongoing() -> bool;

	/// Force a current staker to become completely unstaked, immediately.
	fn force_unstake(who: Self::AccountId) -> DispatchResult;

	/// Checks whether an account `staker` has been exposed in an era.
	fn is_exposed_in_era(who: &Self::AccountId, era: &EraIndex) -> bool;

	/// Get the nominations of a stash, if they are a nominator, `None` otherwise.
	#[cfg(feature = "runtime-benchmarks")]
	fn nominations(who: Self::AccountId) -> Option<sp_std::prelude::Vec<Self::AccountId>>;
}
