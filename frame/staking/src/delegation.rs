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

use crate::{Delegatee, Delegations, BalanceOf, Config};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::RuntimeDebug;
use scale_info::TypeInfo;
use frame_support::dispatch::DispatchResult;
use frame_support::traits::Defensive;
use sp_runtime::DispatchError;

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

	pub fn delegate(x: T::AccountId, x0: T::AccountId, value: BalanceOf<T>) -> Result<Self, DispatchError> {
		// should only delegate to one account.
		// A delegatee can't be delegator.
		// A delegator can't be delegatee.

		// let delegation = Delegation::get(delegator.clone(), delegatee.clone());
		// let existing_balance: BalanceOf<T> = delegation.map(|d: Delegation<T>| d.balance).unwrap_or_default();
		// let new_balance = existing_balance + value;
		todo!()
	}

}
