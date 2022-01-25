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
use sp_runtime::DispatchResult;
use sp_std::collections::btree_map::BTreeMap;

pub mod offence;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

/// Counter for the number of eras that have passed.
pub type EraIndex = u32;

pub trait PoolsInterface {
	type AccountId;
	type Balance;

	// The current approach here is to share `BTreeMap<EraIndex, BalanceOf<T>>` with the staking
	// API. This is arguably a leaky, suboptimal API because both sides have to share this
	// non-trivial data structure. With the current design we do this because we track the unbonding
	// balance in both the pallet-staking `unlocking` chunks and in here with the pallet-pools
	// `SubPools`. Because both pallets need to know about slashes to unbonding funds we either have
	// to replicate the slashing logic between the pallets, or share some data. A ALTERNATIVE is
	// having the pallet-pools read the unbonding balance per era directly from pallet-staking. The
	// downside of this is that once a delegator calls `withdraw_unbonded`, the chunk is removed and
	// we can't keep track of the balance for that `UnbondPool` anymore, thus we must merge the
	// balance and points of that `UnbondPool` with the `no_era` pool immediately upon calling
	// withdraw_unbonded. We choose not to do this because if there was a slash, it would negatively
	// affect the points:balance ratio of the `no_era` pool for everyone, including those who may
	// not have been unbonding in eras effected by the slash.
	/// Calculate the slashes for each unbonding chunk/unbonding pool and the actively bonded
	/// balance. This should apply the updated balances to the pools and return the updated balances
	/// to the caller (presumably pallet-staking) so they can do the corresponding updates.
	fn slash_pool(
		account_id: &Self::AccountId,
		slash_amount: Self::Balance,
		slash_era: EraIndex,
		active_era: EraIndex,
		active_bonded: Self::Balance,
	) -> Option<(Self::Balance, BTreeMap<EraIndex, Self::Balance>)>;
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

	/// Number of eras that staked funds must remain bonded for.
	fn bonding_duration() -> EraIndex;

	/// The current era for the staking system.
	fn current_era() -> EraIndex;

	/// Balance `controller` has bonded for nominating.
	fn bonded_balance(controller: &Self::AccountId) -> Self::Balance;

	/// If the given staker can successfully call `bond_extra` with `extra`. Assumes the `extra`
	/// balance will be transferred in the stash.
	fn can_bond_extra(controller: &Self::AccountId, extra: Self::Balance) -> bool;

	fn bond_extra(controller: &Self::AccountId, extra: Self::Balance) -> DispatchResult;

	fn unbond(controller: &Self::AccountId, value: Self::Balance) -> DispatchResult;

	fn bond(
		stash: Self::AccountId,
		controller: Self::AccountId,
		amount: Self::Balance,
		payee: Self::AccountId,
	) -> DispatchResult;

	fn nominate(controller: Self::AccountId, targets: Vec<Self::LookupSource>) -> DispatchResult;
}
