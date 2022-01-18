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

	fn slash_pool(
		account_id: &Self::AccountId,
		slash_amount: Self::Balance,
		slash_era: EraIndex,
		active_era: EraIndex,
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
