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

//! The traits for dealing with a single fungible token class and any associated types.
//!
//! ### User-implememted traits
//! - `Inspect`: Regular balance inspector functions.
//! - `Unbalanced`: Low-level balance mutating functions. Does not guarantee proper book-keeping and
//!   so should not be called into directly from application code. Other traits depend on this and
//!   provide default implementations based on it.
//! - `UnbalancedHold`: Low-level balance mutating functions for balances placed on hold. Does not
//!   guarantee proper book-keeping and so should not be called into directly from application code.
//!   Other traits depend on this and provide default implementations based on it.
//! - `Mutate`: Regular balance mutator functions. Pre-implemented using `Unbalanced`, though the
//!   `done_*` functions should likely be reimplemented in case you want to do something following
//!   the operation such as emit events.
//! - `InspectHold`: Inspector functions for balances on hold.
//! - `MutateHold`: Mutator functions for balances on hold. Mostly pre-implemented using
//!   `UnbalancedHold`.
//! - `InspectFreeze`: Inspector functions for frozen balance.
//! - `MutateFreeze`: Mutator functions for frozen balance.
//! - `Balanced`: One-sided mutator functions for regular balances, which return imbalance objects
//!   which guaranete eventual book-keeping. May be useful for some sophisticated operations where
//!   funds must be removed from an account before it is known precisely what should be done with
//!   them.
//! - `Balanced`: One-sided mutator functions for balances on hold, which return imbalance objects
//!   which guaranete eventual book-keeping.

use super::{
	misc::{Balance, DepositConsequence, KeepAlive, WithdrawConsequence},
	*,
};
use crate::{
	dispatch::{DispatchError, DispatchResult},
	ensure,
	traits::misc::Get,
};
use scale_info::TypeInfo;
use sp_arithmetic::traits::{CheckedAdd, CheckedSub};
use sp_runtime::{traits::Saturating, ArithmeticError, TokenError};

mod balanced;
mod freeze;
mod hold;
mod imbalance;
mod item_of;
mod unbalanced;

pub use balanced::{Balanced, BalancedHold, DecreaseIssuance, IncreaseIssuance};
pub use freeze::{InspectFreeze, MutateFreeze};
pub use hold::{InspectHold, MutateHold};
pub use imbalance::{CreditOf, DebtOf, HandleImbalanceDrop, Imbalance};
pub use item_of::ItemOf;
pub use unbalanced::{Unbalanced, UnbalancedHold};

/// Trait for providing balance-inspection access to a fungible asset.
pub trait Inspect<AccountId> {
	/// Scalar type for representing balance of an account.
	type Balance: Balance;

	/// The total amount of issuance in the system.
	fn total_issuance() -> Self::Balance;

	/// The total amount of issuance in the system excluding those which are controlled by the
	/// system.
	fn active_issuance() -> Self::Balance {
		Self::total_issuance()
	}

	/// The minimum balance any single account may have.
	fn minimum_balance() -> Self::Balance;

	/// Get the total amount of funds whose ultimate bneficial ownership can be determined as `who`.
	///
	/// This may include funds which are wholly inaccessible to `who`, either temporarily or even
	/// indefinitely.
	///
	/// For the amount of the balance which is currently free to be removed from the account without
	/// error, use `reducible_balance`.
	///
	/// For the amount of the balance which may eventually be free to be removed from the account,
	/// use `balance()`.
	fn total_balance(who: &AccountId) -> Self::Balance;

	/// Get the balance of `who` which does not include funds which are exclusively allocated to
	/// subsystems of the chain ("on hold" or "reserved").
	///
	/// In general this isn't especially useful outside of tests, and for practical purposes, you'll
	/// want to use `reducible_balance()`.
	fn balance(who: &AccountId) -> Self::Balance;

	/// Get the maximum amount that `who` can withdraw/transfer successfully based on whether the
	/// account should be kept alive (`keep_alive`) or whether we are willing to force the reduction
	/// and potentially go below user-level restrictions on the minimum amount of the account.
	///
	/// Always less than `balance()`.
	fn reducible_balance(who: &AccountId, keep_alive: KeepAlive, force: bool) -> Self::Balance;

	/// Returns `true` if the balance of `who` may be increased by `amount`.
	///
	/// - `who`: The account of which the balance should be increased by `amount`.
	/// - `amount`: How much should the balance be increased?
	/// - `mint`: Will `amount` be minted to deposit it into `account`?
	fn can_deposit(who: &AccountId, amount: Self::Balance, mint: bool) -> DepositConsequence;

	/// Returns `Failed` if the balance of `who` may not be decreased by `amount`, otherwise
	/// the consequence.
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance>;
}

/// Trait for providing a basic fungible asset.
pub trait Mutate<AccountId>: Inspect<AccountId> + Unbalanced<AccountId> {
	/// Increase the balance of `who` by exactly `amount`, minting new tokens. If that isn't
	/// possible then an `Err` is returned and nothing is changed.
	fn mint_into(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		Self::total_issuance().checked_add(&amount).ok_or(ArithmeticError::Overflow)?;
		let actual = Self::increase_balance(who, amount, false)?;
		Self::set_total_issuance(Self::total_issuance().saturating_add(actual));
		Self::done_mint_into(who, amount);
		Ok(actual)
	}

	/// Decrease the balance of `who` by at least `amount`, possibly slightly more in the case of
	/// minimum-balance requirements, burning the tokens. If that isn't possible then an `Err` is
	/// returned and nothing is changed. If successful, the amount of tokens reduced is returned.
	fn burn_from(
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		let actual = Self::reducible_balance(who, KeepAlive::CanKill, force).min(amount);
		ensure!(actual == amount || best_effort, TokenError::FundsUnavailable);
		Self::total_issuance().checked_sub(&actual).ok_or(ArithmeticError::Overflow)?;
		let actual = Self::decrease_balance(who, actual, true, KeepAlive::CanKill, force)?;
		Self::set_total_issuance(Self::total_issuance().saturating_sub(actual));
		Self::done_burn_from(who, actual);
		Ok(actual)
	}

	/// Attempt to increase the `asset` balance of `who` by `amount`.
	///
	/// Equivalent to `burn_from`, except with an expectation that within the bounds of some
	/// universal issuance, the total assets `suspend`ed and `resume`d will be equivalent. The
	/// implementation may be configured such that the total assets suspended may never be less than
	/// the total assets resumed (which is the invariant for an issuing system), or the reverse
	/// (which the invariant in a non-issuing system).
	///
	/// Because of this expectation, any metadata associated with the asset is expected to survive
	/// the suspect-resume cycle.
	fn shelve(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		let actual = Self::reducible_balance(who, KeepAlive::CanKill, false).min(amount);
		ensure!(actual == amount, TokenError::FundsUnavailable);
		Self::total_issuance().checked_sub(&actual).ok_or(ArithmeticError::Overflow)?;
		let actual = Self::decrease_balance(who, actual, true, KeepAlive::CanKill, false)?;
		Self::set_total_issuance(Self::total_issuance().saturating_sub(actual));
		Self::done_shelve(who, actual);
		Ok(actual)
	}

	/// Attempt to increase the `asset` balance of `who` by `amount`.
	///
	/// Equivalent to `mint_into`, except with an expectation that within the bounds of some
	/// universal issuance, the total assets `suspend`ed and `resume`d will be equivalent. The
	/// implementation may be configured such that the total assets suspended may never be less than
	/// the total assets resumed (which is the invariant for an issuing system), or the reverse
	/// (which the invariant in a non-issuing system).
	///
	/// Because of this expectation, any metadata associated with the asset is expected to survive
	/// the suspect-resume cycle.
	fn restore(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		Self::total_issuance().checked_add(&amount).ok_or(ArithmeticError::Overflow)?;
		let actual = Self::increase_balance(who, amount, false)?;
		Self::set_total_issuance(Self::total_issuance().saturating_add(actual));
		Self::done_restore(who, amount);
		Ok(actual)
	}

	/// Transfer funds from one account into another.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
		keep_alive: KeepAlive,
	) -> Result<Self::Balance, DispatchError> {
		let _extra =
			Self::can_withdraw(source, amount).into_result(keep_alive != KeepAlive::CanKill)?;
		Self::can_deposit(dest, amount, false).into_result()?;
		Self::decrease_balance(source, amount, true, keep_alive, false)?;
		// This should never fail as we checked `can_deposit` earlier. But we do a best-effort
		// anyway.
		let _ = Self::increase_balance(dest, amount, true);
		Self::done_transfer(source, dest, amount);
		Ok(amount)
	}

	fn done_mint_into(_who: &AccountId, _amount: Self::Balance) {}
	fn done_burn_from(_who: &AccountId, _amount: Self::Balance) {}
	fn done_shelve(_who: &AccountId, _amount: Self::Balance) {}
	fn done_restore(_who: &AccountId, _amount: Self::Balance) {}
	fn done_transfer(_source: &AccountId, _dest: &AccountId, _amount: Self::Balance) {}
}
