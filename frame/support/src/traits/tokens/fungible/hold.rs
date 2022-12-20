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

//! The traits for putting holds within a single fungible token class.

use crate::ensure;
use sp_runtime::TokenError;
use DepositConsequence::Success;

use super::*;

/// Trait for inspecting a fungible asset whose accounts support partitioning and slashing.
pub trait InspectHold<AccountId>: Inspect<AccountId> {
	/// An identifier for a hold. Used for disambiguating different holds so that
	/// they can be individually replaced or removed and funds from one hold don't accidentally
	/// become unreserved or slashed for another.
	type Reason: codec::Encode + TypeInfo + 'static;

	/// Amount of funds on hold (for all hold reasons) of `who`.
	fn total_balance_on_hold(who: &AccountId) -> Self::Balance;

	/// Get the maximum amount that the `total_balance_on_hold` of `who` can be reduced successfully
	/// based on whether we are willing to force the reduction and potentially go below user-level
	/// restrictions on the minimum amount of the account.
	///
	/// Always less than `total_balance_on_hold()`.
	fn reducible_total_balance_on_hold(who: &AccountId, force: bool) -> Self::Balance;

	/// Amount of funds on hold (for all hold reasons) of `who`.
	fn balance_on_hold(reason: &Self::Reason, who: &AccountId) -> Self::Balance;

	/// Returns `true` if it's possible to place (additional) funds under a hold of a given
	/// `reason`. This may fail if the account has exhausted a limited number of concurrent
	/// holds or if it cannot be made to exist (e.g. there is no provider reference).
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn hold_available(reason: &Self::Reason, who: &AccountId) -> bool;

	/// Check to see if some `amount` of funds of `who` may be placed on hold for the given
	/// `reason`. Reasons why this may not be true:
	///
	/// - The implementor supports only a limited number of concurrernt holds on an account which is
	///   the possible values of `reason`;
	/// - The main balance of the account is less than `amount`;
	/// - Removing `amount` from the main balance would kill the account and remove the only
	///   provider reference.
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn ensure_can_hold(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		ensure!(Self::hold_available(reason, who), TokenError::CannotCreateHold);
		ensure!(
			amount <= Self::reducible_balance(who, KeepAlive::NoKill, false),
			TokenError::FundsUnavailable
		);
		Ok(())
	}

	/// Check to see if some `amount` of funds of `who` may be placed on hold for the given
	/// `reason`. Reasons why this may not be true:
	///
	/// - The implementor supports only a limited number of concurrernt holds on an account which is
	///   the possible values of `reason`;
	/// - The main balance of the account is less than `amount`;
	/// - Removing `amount` from the main balance would kill the account and remove the only
	///   provider reference.
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn can_hold(reason: &Self::Reason, who: &AccountId, amount: Self::Balance) -> bool {
		Self::ensure_can_hold(reason, who, amount).is_ok()
	}
}

/// Trait for mutating a fungible asset which can be placed on hold.
pub trait MutateHold<AccountId>: InspectHold<AccountId> {
	/// Hold some funds in an account. If a hold for `reason` is already in place, then this
	/// will increase it.
	fn hold(reason: &Self::Reason, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Release up to `amount` held funds in an account.
	///
	/// The actual amount released is returned with `Ok`.
	///
	/// If `best_effort` is `true`, then the amount actually unreserved and returned as the inner
	/// value of `Ok` may be smaller than the `amount` passed.
	fn release(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError>;

	/// Attempt to decrease the balance of `who` which is held for the given `reason` by `amount`.
	///
	/// If `best_effort` is true, then as much as possible is reduced, up to `amount`, and the
	/// amount of tokens reduced is returned. Otherwise, if the total amount can be reduced, then it
	/// is and the amount returned, and if not, then nothing changes and `Err` is returned.
	///
	/// If `force` is true, then locks/freezes will be ignored. This should only be used when
	/// conducting slashing or other activity which materially disadvantages the account holder
	/// since it could provide a means of circumventing freezes.
	fn burn_held(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError>;

	/// Transfer held funds into a destination account.
	///
	/// If `on_hold` is `true`, then the destination account must already exist and the assets
	/// transferred will still be on hold in the destination account. If not, then the destination
	/// account need not already exist, but must be creatable.
	///
	/// If `best_effort` is `true`, then an amount less than `amount` may be transferred without
	/// error.
	///
	/// If `force` is `true`, then other fund-locking mechanisms may be disregarded. It should be
	/// left as `false` in most circumstances, but when you want the same power as a `slash`, it
	/// may be `true`.
	///
	/// The actual amount transferred is returned, or `Err` in the case of error and nothing is
	/// changed.
	fn transfer_on_hold(
		reason: &Self::Reason,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		on_hold: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError>;
}

/// Trait for slashing a fungible asset which can be place on hold.
pub trait BalancedHold<AccountId>: Balanced<AccountId> + MutateHold<AccountId> {
	/// Reduce the balance of some funds on hold in an account.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds that are on hold up to `amount` will be deducted as possible. If this is less
	/// than `amount`, then a non-zero second item will be returned.
	fn slash(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> (CreditOf<AccountId, Self>, Self::Balance);
}

impl<AccountId, U: Unbalanced<AccountId> + UnbalancedHold<AccountId> + InspectHold<AccountId>>
	MutateHold<AccountId> for U
{
	fn hold(reason: &Self::Reason, who: &AccountId, amount: Self::Balance) -> DispatchResult {
		// NOTE: This doesn't change the total balance of the account so there's no need to
		// check liquidity.

		Self::ensure_can_hold(reason, who, amount)?;
		// Should be infallible now, but we proceed softly anyway.
		Self::decrease_balance(who, amount, true, KeepAlive::NoKill)?;
		Self::increase_balance_on_hold(reason, who, amount, true)?;
		Ok(())
	}

	fn release(
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		// NOTE: This doesn't change the total balance of the account so there's no need to
		// check liquidity.

		// We want to make sure we can deposit the amount in advance. If we can't then something is
		// very wrong.
		ensure!(Self::can_deposit(who, amount, false) == Success, TokenError::CannotCreate);
		// Get the amount we can actually take from the hold. This might be less than what we want
		// if we're only doing a best-effort.
		let amount = Self::decrease_balance_on_hold(reason, who, amount, best_effort)?;
		// Increase the main balance by what we took. We always do a best-effort here because we
		// already checked that we can deposit before.
		Self::increase_balance(who, amount, true)
	}

	fn burn_held(
		reason: &Self::Reason,
		who: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		// We must check total-balance requirements if `!force`.
		let liquid = Self::reducible_total_balance_on_hold(who, force);
		if best_effort {
			amount = amount.min(liquid);
		} else {
			ensure!(amount <= liquid, TokenError::Frozen);
		}
		let amount = Self::decrease_balance_on_hold(reason, who, amount, best_effort)?;
		Self::set_total_issuance(Self::total_issuance().saturating_sub(amount));
		Ok(amount)
	}

	fn transfer_on_hold(
		reason: &Self::Reason,
		source: &AccountId,
		dest: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
		on_hold: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError> {
		// We must check total-balance requirements if `!force`.
		let have = Self::balance_on_hold(reason, source);
		let liquid = Self::reducible_total_balance_on_hold(source, force);
		if best_effort {
			amount = amount.min(liquid).min(have);
		} else {
			ensure!(amount <= liquid, TokenError::Frozen);
			ensure!(amount <= have, TokenError::FundsUnavailable);
		}

		// We want to make sure we can deposit the amount in advance. If we can't then something is
		// very wrong.
		ensure!(Self::can_deposit(dest, amount, false) == Success, TokenError::CannotCreate);
		if on_hold {
			ensure!(Self::hold_available(reason, dest), TokenError::CannotCreateHold);
		}

		let amount = Self::decrease_balance_on_hold(reason, source, amount, best_effort)?;
		if on_hold {
			Self::increase_balance_on_hold(reason, dest, amount, best_effort)
		} else {
			Self::increase_balance(dest, amount, best_effort)
		}
	}
}
