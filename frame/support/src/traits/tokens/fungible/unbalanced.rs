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

//! Trait for doing raw changes to a fungible asset accounting system.

use sp_arithmetic::traits::{CheckedSub, CheckedAdd, Zero};
use sp_runtime::{TokenError, ArithmeticError};
use crate::traits::tokens::misc::KeepAlive;

use super::*;

/// A fungible token class where the balance can be set arbitrarily.
///
/// **WARNING**
/// Do not use this directly unless you want trouble, since it allows you to alter account balances
/// without keeping the issuance up to date. It has no safeguards against accidentally creating
/// token imbalances in your system leading to accidental imflation or deflation. It's really just
/// for the underlying datatype to implement so the user gets the much safer `Balanced` trait to
/// use.
pub trait Unbalanced<AccountId>: Inspect<AccountId> {
	/// Forcefully set the balance of `who` to `amount`.
	///
	/// If this call executes successfully, you can `assert_eq!(Self::balance(), amount);`.
	///
	/// For implementations which include one or more balances on hold, then these are *not*
	/// included in the `amount`.
	///
	/// This function does its best to force the balance change through, but will not break system
	/// invariants such as any Existential Deposits needed or overflows/underflows.
	/// If this cannot be done for some reason (e.g. because the account cannot be created, deleted
	/// or would overflow) then an `Err` is returned.
	fn set_balance(who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Set the total issuance to `amount`.
	fn set_total_issuance(amount: Self::Balance);

	/// Reduce the balance of `who` by `amount`.
	///
	/// If `best_effort` is `false` and it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If `best_effort` is `true`, then
	/// reduce the balance of `who` by the most that is possible, up to `amount`.
	///
	/// In either case, if `Ok` is returned then the inner is the amount by which is was reduced.
	/// Minimum balance will be respected and thus the returned amount may be up to
	/// `Self::minimum_balance() - 1` greater than `amount` in the case that the reduction caused
	/// the account to be deleted.
	fn decrease_balance(
		who: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance(who);
		let free = Self::reducible_balance(who, keep_alive, false);
		if best_effort {
			amount = amount.min(free);
		}
		let new_balance = old_balance.checked_sub(&amount).ok_or(TokenError::NoFunds)?;
		Self::set_balance(who, new_balance)?;
		Ok(amount)
	}

	/// Increase the balance of `who` by `amount`.
	///
	/// If it cannot be increased by that amount for some reason, return `Err` and don't increase
	/// it at all. If Ok, return the imbalance.
	/// Minimum balance will be respected and an error will be returned if
	/// `amount < Self::minimum_balance()` when the account of `who` is zero.
	fn increase_balance(
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance(who);
		let new_balance = if best_effort {
			old_balance.saturating_add(amount)
		} else {
			old_balance.checked_add(&amount).ok_or(ArithmeticError::Overflow)?
		};
		if new_balance < Self::minimum_balance() {
			// Attempt to increase from 0 to below minimum -> stays at zero.
			if best_effort {
				Ok(Self::Balance::zero())
			} else {
				Err(TokenError::BelowMinimum.into())
			}
		} else {
			let amount = new_balance.saturating_sub(old_balance);
			if !amount.is_zero() {
				Self::set_balance(who, new_balance)?;
			}
			Ok(amount)
		}
	}
}

/// A fungible, holdable token class where the balance on hold can be set arbitrarily.
///
/// **WARNING**
/// Do not use this directly unless you want trouble, since it allows you to alter account balances
/// without keeping the issuance up to date. It has no safeguards against accidentally creating
/// token imbalances in your system leading to accidental imflation or deflation. It's really just
/// for the underlying datatype to implement so the user gets the much safer `Balanced` trait to
/// use.
pub trait UnbalancedHold<AccountId>: InspectHold<AccountId> {
	/// Forcefully set the balance on hold of `who` to `amount`. This is independent of any other
	/// balances on hold or the main ("free") balance.
	///
	/// If this call executes successfully, you can `assert_eq!(Self::balance_on_hold(), amount);`.
	///
	/// This function does its best to force the balance change through, but will not break system
	/// invariants such as any Existential Deposits needed or overflows/underflows.
	/// If this cannot be done for some reason (e.g. because the account doesn't exist) then an
	/// `Err` is returned.
	// Implmentation note: This should increment the consumer refs if it moves total on hold from
	// zero to non-zero and decrement in the opposite direction.
	//
	// Since this was not done in the previous logic, this will need either a migration or a
	// state item which tracks whether the account is on the old logic or new.
	fn set_balance_on_hold(reason: &Self::Reason, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Reduce the balance on hold of `who` by `amount`.
	///
	/// If `best_effort` is `false` and it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If `best_effort` is `true`, then
	/// reduce the balance of `who` by the most that is possible, up to `amount`.
	///
	/// In either case, if `Ok` is returned then the inner is the amount by which is was reduced.
	fn decrease_balance_on_hold(
		reason: &Self::Reason,
		who: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(reason, who);
		if best_effort {
			amount = amount.min(old_balance);
		}
		let new_balance = old_balance.checked_sub(&amount).ok_or(TokenError::NoFunds)?;
		Self::set_balance_on_hold(reason, who, new_balance)?;
		Ok(amount)
	}

	/// Increase the balance on hold of `who` by `amount`.
	///
	/// If it cannot be increased by that amount for some reason, return `Err` and don't increase
	/// it at all. If Ok, return the imbalance.
	fn increase_balance_on_hold(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(reason, who);
		let new_balance = if best_effort {
			old_balance.saturating_add(amount)
		} else {
			old_balance.checked_add(&amount).ok_or(ArithmeticError::Overflow)?
		};
		let amount = new_balance.saturating_sub(old_balance);
		if !amount.is_zero() {
			Self::set_balance_on_hold(reason, who, new_balance)?;
		}
		Ok(amount)
	}
}
