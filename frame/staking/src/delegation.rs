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

//! An implementation of a delegation system for nominators.
//!
//! This allows an account (called delegator) to delegate their funds to another account
//! (delegatee). Multiple delegators can delegate to the same delegatee. The delegatee is then able
//! to use the funds of all delegators to nominate a set of validators.

use crate::{Delegatee, Delegations, BalanceOf, Config, Error};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{ensure, RuntimeDebug};
use scale_info::TypeInfo;
use frame_support::dispatch::DispatchResult;
use frame_support::traits::{Currency, Defensive, LockableCurrency, LockIdentifier, WithdrawReasons};

/// Lock identifier for funds delegated to another account.
///
/// This helps us differentiate the locks used for direct nomination and delegation based nomination
/// and technically allows a direct nominator to be a delegator as well. We don't strictly need to
/// support this but before delegation based staking were a thing, above was possible and we would
/// like to keep things consistent and compatible once user of this pallet (NominationPools) moves
/// to delegation based staking.
const DELEGATING_ID: LockIdentifier = *b"delegate";

/// A ledger of a delegator.
///
/// This keeps track of the active balance of the delegator that is made up from the funds that are
/// currently delegated to a delegatee. It also tracks the slashes yet to be applied.
#[derive(Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct DelegationLedger<T: Config> {
	/// Sum of all delegated funds to this delegatee.
	#[codec(compact)]
	pub balance: BalanceOf<T>,
	/// Slashes that are not yet applied.
	#[codec(compact)]
	pub pending_slash: BalanceOf<T>,
}

// Delegation state that is not saved yet in database.
struct New;
// Existing delegation state which contains information only about delegatee.
struct OnlyDelegatee;
// Delegation state which contains information about both delegator and delegatee.
struct Full;

pub struct Delegation<T: Config> {
	ledger: DelegationLedger<T>,
	delegator: T::AccountId,
	delegatee: T::AccountId,
	delegator_balance: BalanceOf<T>,
	// state: sp_std::marker::PhantomData<State>,
}

impl<T: Config> Delegation<T> {
	/// The maximum number of delegators that can delegate to a single delegatee.
	pub fn delegator_balance(self) -> BalanceOf<T> {
		// let delegated_balance = Delegations::<T>::get(&delegator, &delegatee)?;
		// // since delegated balance exists, delegatee ledger must exist.
		// let ledger = Delegatee::<T>::get(&delegatee).defensive()?;
		//
		// Some(Self { ledger, delegator, delegatee, balance: delegated_balance })
		todo!()
	}

	pub fn delegate(delegator: T::AccountId, delegatee: T::AccountId, value: BalanceOf<T>) -> DispatchResult {
		// should only delegate to one account.
		// A delegatee can't be delegator.
		// A delegator can't be delegatee.

		// let delegation = Delegation::get(delegator.clone(), delegatee.clone());
		// let existing_balance: BalanceOf<T> = delegation.map(|d: Delegation<T>| d.balance).unwrap_or_default();
		// let new_balance = existing_balance + value;

		let delegator_balance = T::Currency::free_balance(&delegator);
		ensure!(value >= T::Currency::minimum_balance(), Error::<T>::InsufficientBond);
		ensure!(delegator_balance >= value, Error::<T>::InsufficientBond);

		T::Currency::set_lock(
			DELEGATING_ID,
			&delegator,
			value,
			WithdrawReasons::all(),
		);
		todo!()
	}

	pub fn migrate_into(delegatee: T::AccountId, delegator: T::AccountId, value: BalanceOf<T>) -> DispatchResult {
		// (1) Unlock value at delegatee with StakingID.
		// (2) transfer to delegator.
		// (3) lock with delegating_id.
		// (4) Update Ledger
		// (5) Verify no changes needed in Staking Ledger
		todo!()
	}

}
