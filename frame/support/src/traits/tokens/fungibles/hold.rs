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

use crate::{
	ensure,
	traits::tokens::{
		DepositConsequence::Success,
		Fortitude::{self, Force},
		Precision::{self, BestEffort, Exact},
		Preservation::{self, Protect},
		Provenance::Extant,
		Restriction::{self, Free, OnHold},
	},
};
use scale_info::TypeInfo;
use sp_arithmetic::{
	traits::{CheckedAdd, CheckedSub, Zero},
	ArithmeticError,
};
use sp_runtime::{DispatchError, DispatchResult, Saturating, TokenError};

use super::*;

/// Trait for inspecting a fungible asset whose accounts support partitioning and slashing.
pub trait Inspect<AccountId>: super::Inspect<AccountId> {
	/// An identifier for a hold. Used for disambiguating different holds so that
	/// they can be individually replaced or removed and funds from one hold don't accidentally
	/// become unreserved or slashed for another.
	type Reason: codec::Encode + TypeInfo + 'static;

	/// Amount of funds on hold (for all hold reasons) of `who`.
	fn total_balance_on_hold(asset: Self::AssetId, who: &AccountId) -> Self::Balance;

	/// Get the maximum amount that the `total_balance_on_hold` of `who` can be reduced successfully
	/// based on whether we are willing to force the reduction and potentially go below user-level
	/// restrictions on the minimum amount of the account. Note: This cannot bring the account into
	/// an inconsistent state with regards any required existential deposit.
	///
	/// Always less than `total_balance_on_hold()`.
	fn reducible_total_balance_on_hold(
		asset: Self::AssetId,
		who: &AccountId,
		force: Fortitude,
	) -> Self::Balance;

	/// Amount of funds on hold (for the given reason) of `who`.
	fn balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
	) -> Self::Balance;

	/// Returns `true` if it's possible to place (additional) funds under a hold of a given
	/// `reason`. This may fail if the account has exhausted a limited number of concurrent
	/// holds or if it cannot be made to exist (e.g. there is no provider reference).
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn hold_available(asset: Self::AssetId, reason: &Self::Reason, who: &AccountId) -> bool;

	/// Check to see if some `amount` of funds of `who` may be placed on hold with the given
	/// `reason`. Reasons why this may not be true:
	///
	/// - The implementor supports only a limited number of concurrent holds on an account which is
	///   the possible values of `reason`;
	/// - The total balance of the account is less than `amount`;
	/// - Removing `amount` from the total balance would kill the account and remove the only
	///   provider reference.
	///
	/// Note: we pass `Fortitude::Force` as the last argument to `reducible_balance` since we assume
	/// that if needed the balance can slashed. If we are using a simple non-forcing
	/// reserve-transfer, then we really ought to check that we are not reducing the funds below the
	/// freeze-limit (if any).
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn ensure_can_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		ensure!(Self::hold_available(asset.clone(), reason, who), TokenError::CannotCreateHold);
		ensure!(
			amount <= Self::reducible_balance(asset, who, Protect, Force),
			TokenError::FundsUnavailable
		);
		Ok(())
	}

	/// Check to see if some `amount` of funds of `who` may be placed on hold for the given
	/// `reason`. Reasons why this may not be true:
	///
	/// - The implementor supports only a limited number of concurrent holds on an account which is
	///   the possible values of `reason`;
	/// - The main balance of the account is less than `amount`;
	/// - Removing `amount` from the main balance would kill the account and remove the only
	///   provider reference.
	///
	/// NOTE: This does not take into account changes which could be made to the account of `who`
	/// (such as removing a provider reference) after this call is made. Any usage of this should
	/// therefore ensure the account is already in the appropriate state prior to calling it.
	fn can_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> bool {
		Self::ensure_can_hold(asset, reason, who, amount).is_ok()
	}
}

/// A fungible, holdable token class where the balance on hold can be set arbitrarily.
///
/// **WARNING**
/// Do not use this directly unless you want trouble, since it allows you to alter account balances
/// without keeping the issuance up to date. It has no safeguards against accidentally creating
/// token imbalances in your system leading to accidental inflation or deflation. It's really just
/// for the underlying datatype to implement so the user gets the much safer `Balanced` trait to
/// use.
pub trait Unbalanced<AccountId>: Inspect<AccountId> {
	/// Forcefully set the balance on hold of `who` to `amount`. This is independent of any other
	/// balances on hold or the main ("free") balance.
	///
	/// If this call executes successfully, you can `assert_eq!(Self::balance_on_hold(), amount);`.
	///
	/// This function does its best to force the balance change through, but will not break system
	/// invariants such as any Existential Deposits needed or overflows/underflows.
	/// If this cannot be done for some reason (e.g. because the account doesn't exist) then an
	/// `Err` is returned.
	// Implementation note: This should increment the consumer refs if it moves total on hold from
	// zero to non-zero and decrement in the opposite direction.
	//
	// Since this was not done in the previous logic, this will need either a migration or a
	// state item which tracks whether the account is on the old logic or new.
	fn set_balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;

	/// Reduce the balance on hold of `who` by `amount`.
	///
	/// If `precision` is `Precision::Exact` and it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If `precision` is
	/// `Precision::BestEffort`, then reduce the balance of `who` by the most that is possible, up
	/// to `amount`.
	///
	/// In either case, if `Ok` is returned then the inner is the amount by which is was reduced.
	fn decrease_balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		mut amount: Self::Balance,
		precision: Precision,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(asset.clone(), reason, who);
		if let BestEffort = precision {
			amount = amount.min(old_balance);
		}
		let new_balance = old_balance.checked_sub(&amount).ok_or(TokenError::FundsUnavailable)?;
		Self::set_balance_on_hold(asset, reason, who, new_balance)?;
		Ok(amount)
	}

	/// Increase the balance on hold of `who` by `amount`.
	///
	/// If it cannot be increased by that amount for some reason, return `Err` and don't increase
	/// it at all. If Ok, return the imbalance.
	fn increase_balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		precision: Precision,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(asset.clone(), reason, who);
		let new_balance = if let BestEffort = precision {
			old_balance.saturating_add(amount)
		} else {
			old_balance.checked_add(&amount).ok_or(ArithmeticError::Overflow)?
		};
		let amount = new_balance.saturating_sub(old_balance);
		if !amount.is_zero() {
			Self::set_balance_on_hold(asset, reason, who, new_balance)?;
		}
		Ok(amount)
	}
}

/// Trait for slashing a fungible asset which can be place on hold.
pub trait Balanced<AccountId>: super::Balanced<AccountId> + Unbalanced<AccountId> {
	/// Reduce the balance of some funds on hold in an account.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds that are on hold up to `amount` will be deducted as possible. If this is less
	/// than `amount`, then a non-zero second item will be returned.
	fn slash(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> (Credit<AccountId, Self>, Self::Balance) {
		let decrease =
			Self::decrease_balance_on_hold(asset.clone(), reason, who, amount, BestEffort)
				.unwrap_or(Default::default());
		let credit =
			Imbalance::<Self::AssetId, Self::Balance, Self::OnDropCredit, Self::OnDropDebt>::new(
				asset.clone(),
				decrease,
			);
		Self::done_slash(asset, reason, who, decrease);
		(credit, amount.saturating_sub(decrease))
	}

	fn done_slash(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_who: &AccountId,
		_amount: Self::Balance,
	) {
	}
}

/// Trait for mutating a fungible asset which can be placed on hold.
pub trait Mutate<AccountId>:
	Inspect<AccountId> + super::Unbalanced<AccountId> + Unbalanced<AccountId>
{
	/// Hold some funds in an account. If a hold for `reason` is already in place, then this
	/// will increase it.
	fn hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult {
		// NOTE: This doesn't change the total balance of the account so there's no need to
		// check liquidity.

		Self::ensure_can_hold(asset.clone(), reason, who, amount)?;
		// Should be infallible now, but we proceed softly anyway.
		Self::decrease_balance(asset.clone(), who, amount, Exact, Protect, Force)?;
		Self::increase_balance_on_hold(asset.clone(), reason, who, amount, BestEffort)?;
		Self::done_hold(asset, reason, who, amount);
		Ok(())
	}

	/// Release up to `amount` held funds in an account.
	///
	/// The actual amount released is returned with `Ok`.
	///
	/// If `precision` is `BestEffort`, then the amount actually unreserved and returned as the
	/// inner value of `Ok` may be smaller than the `amount` passed.
	fn release(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
		precision: Precision,
	) -> Result<Self::Balance, DispatchError> {
		// NOTE: This doesn't change the total balance of the account so there's no need to
		// check liquidity.

		// We want to make sure we can deposit the amount in advance. If we can't then something is
		// very wrong.
		ensure!(
			Self::can_deposit(asset.clone(), who, amount, Extant) == Success,
			TokenError::CannotCreate
		);
		// Get the amount we can actually take from the hold. This might be less than what we want
		// if we're only doing a best-effort.
		let amount = Self::decrease_balance_on_hold(asset.clone(), reason, who, amount, precision)?;
		// Increase the main balance by what we took. We always do a best-effort here because we
		// already checked that we can deposit before.
		let actual = Self::increase_balance(asset.clone(), who, amount, BestEffort)?;
		Self::done_release(asset, reason, who, actual);
		Ok(actual)
	}

	/// Attempt to decrease the balance of `who` which is held for the given `reason` by `amount`.
	///
	/// If `precision` is true, then as much as possible is reduced, up to `amount`, and the
	/// amount of tokens reduced is returned. Otherwise, if the total amount can be reduced, then it
	/// is and the amount returned, and if not, then nothing changes and `Err` is returned.
	///
	/// If `force` is `Force`, then locks/freezes will be ignored. This should only be used when
	/// conducting slashing or other activity which materially disadvantages the account holder
	/// since it could provide a means of circumventing freezes.
	fn burn_held(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		mut amount: Self::Balance,
		precision: Precision,
		force: Fortitude,
	) -> Result<Self::Balance, DispatchError> {
		// We must check total-balance requirements if `!force`.
		let liquid = Self::reducible_total_balance_on_hold(asset.clone(), who, force);
		if let BestEffort = precision {
			amount = amount.min(liquid);
		} else {
			ensure!(amount <= liquid, TokenError::Frozen);
		}
		let amount = Self::decrease_balance_on_hold(asset.clone(), reason, who, amount, precision)?;
		Self::set_total_issuance(
			asset.clone(),
			Self::total_issuance(asset.clone()).saturating_sub(amount),
		);
		Self::done_burn_held(asset, reason, who, amount);
		Ok(amount)
	}

	/// Transfer held funds into a destination account.
	///
	/// If `mode` is `OnHold`, then the destination account must already exist and the assets
	/// transferred will still be on hold in the destination account. If not, then the destination
	/// account need not already exist, but must be creatable.
	///
	/// If `precision` is `BestEffort`, then an amount less than `amount` may be transferred without
	/// error.
	///
	/// If `force` is `Force`, then other fund-locking mechanisms may be disregarded. It should be
	/// left as `Regular` in most circumstances, but when you want the same power as a `slash`, it
	/// may be `Force`.
	///
	/// The actual amount transferred is returned, or `Err` in the case of error and nothing is
	/// changed.
	fn transfer_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		source: &AccountId,
		dest: &AccountId,
		mut amount: Self::Balance,
		precision: Precision,
		mode: Restriction,
		force: Fortitude,
	) -> Result<Self::Balance, DispatchError> {
		// We must check total-balance requirements if `!force`.
		let have = Self::balance_on_hold(asset.clone(), reason, source);
		let liquid = Self::reducible_total_balance_on_hold(asset.clone(), source, force);
		if let BestEffort = precision {
			amount = amount.min(liquid).min(have);
		} else {
			ensure!(amount <= liquid, TokenError::Frozen);
			ensure!(amount <= have, TokenError::FundsUnavailable);
		}

		// We want to make sure we can deposit the amount in advance. If we can't then something is
		// very wrong.
		ensure!(
			Self::can_deposit(asset.clone(), dest, amount, Extant) == Success,
			TokenError::CannotCreate
		);
		ensure!(
			mode == Free || Self::hold_available(asset.clone(), reason, dest),
			TokenError::CannotCreateHold
		);

		let amount =
			Self::decrease_balance_on_hold(asset.clone(), reason, source, amount, precision)?;
		let actual = if mode == OnHold {
			Self::increase_balance_on_hold(asset.clone(), reason, dest, amount, precision)?
		} else {
			Self::increase_balance(asset.clone(), dest, amount, precision)?
		};
		Self::done_transfer_on_hold(asset, reason, source, dest, actual);
		Ok(actual)
	}

	/// Transfer some `amount` of free balance from `source` to become owned by `dest` but on hold
	/// for `reason`.
	/// for `reason`.
	///
	/// If `precision` is `BestEffort`, then an amount less than `amount` may be transferred without
	/// error.
	///
	/// `source` must obey the requirements of `keep_alive`.
	///
	/// If `force` is `Force`, then other fund-locking mechanisms may be disregarded. It should be
	/// left as `Regular` in most circumstances, but when you want the same power as a `slash`, it
	/// may be `Force`.
	///
	/// The amount placed on hold is returned or `Err` in the case of error and nothing is changed.
	///
	/// WARNING: This may return an error after a partial storage mutation. It should be used only
	/// inside a transactional storage context and an `Err` result must imply a storage rollback.
	fn transfer_and_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
		precision: Precision,
		expendability: Preservation,
		force: Fortitude,
	) -> Result<Self::Balance, DispatchError> {
		ensure!(Self::hold_available(asset.clone(), reason, dest), TokenError::CannotCreateHold);
		ensure!(
			Self::can_deposit(asset.clone(), dest, amount, Extant) == Success,
			TokenError::CannotCreate
		);
		let actual =
			Self::decrease_balance(asset.clone(), source, amount, precision, expendability, force)?;
		Self::increase_balance_on_hold(asset.clone(), reason, dest, actual, precision)?;
		Self::done_transfer_on_hold(asset, reason, source, dest, actual);
		Ok(actual)
	}

	fn done_hold(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_who: &AccountId,
		_amount: Self::Balance,
	) {
	}
	fn done_release(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_who: &AccountId,
		_amount: Self::Balance,
	) {
	}
	fn done_burn_held(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_who: &AccountId,
		_amount: Self::Balance,
	) {
	}
	fn done_transfer_on_hold(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_source: &AccountId,
		_dest: &AccountId,
		_amount: Self::Balance,
	) {
	}
	fn done_transfer_and_hold(
		_asset: Self::AssetId,
		_reason: &Self::Reason,
		_source: &AccountId,
		_dest: &AccountId,
		_transferred: Self::Balance,
	) {
	}
}
