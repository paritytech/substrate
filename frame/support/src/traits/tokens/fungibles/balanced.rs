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

//! The trait and associated types for sets of fungible tokens that manage total issuance without
//! requiring atomic balanced operations.

use super::*;
use crate::{
	dispatch::{DispatchError, DispatchResult},
	traits::misc::{SameOrOther, TryDrop},
};
use sp_arithmetic::traits::{CheckedSub, Saturating};
use sp_runtime::{
	traits::{CheckedAdd, Zero},
	ArithmeticError, TokenError,
};
use sp_std::marker::PhantomData;

/// A fungible token class where any creation and deletion of tokens is semi-explicit and where the
/// total supply is maintained automatically.
///
/// This is auto-implemented when a token class has `Unbalanced` implemented.
pub trait Balanced<AccountId>: Inspect<AccountId> {
	/// The type for managing what happens when an instance of `Debt` is dropped without being used.
	type OnDropDebt: HandleImbalanceDrop<Self::AssetId, Self::Balance>;
	/// The type for managing what happens when an instance of `Credit` is dropped without being
	/// used.
	type OnDropCredit: HandleImbalanceDrop<Self::AssetId, Self::Balance>;

	/// Reduce the total issuance by `amount` and return the according imbalance. The imbalance will
	/// typically be used to reduce an account by the same amount with e.g. `settle`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is burnt, for example
	/// in the case of underflow.
	fn rescind(asset: Self::AssetId, amount: Self::Balance) -> DebtOf<AccountId, Self>;

	/// Increase the total issuance by `amount` and return the according imbalance. The imbalance
	/// will typically be used to increase an account by the same amount with e.g.
	/// `resolve_into_existing` or `resolve_creating`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is issued, for example
	/// in the case of overflow.
	fn issue(asset: Self::AssetId, amount: Self::Balance) -> CreditOf<AccountId, Self>;

	/// Produce a pair of imbalances that cancel each other out exactly.
	///
	/// This is just the same as burning and issuing the same amount and has no effect on the
	/// total issuance.
	fn pair(
		asset: Self::AssetId,
		amount: Self::Balance,
	) -> (DebtOf<AccountId, Self>, CreditOf<AccountId, Self>) {
		(Self::rescind(asset, amount), Self::issue(asset, amount))
	}

	/// Mints `value` into the `asset` account of `who`, creating it as needed.
	///
	/// If `best_effort` is `true` and `value` in full could not be minted (e.g. due to overflow),
	/// then the maximum is minted, up to `value`. If `best_effort` is `false`, then exactly `value`
	/// must be minted into the account of `who` or the operation will fail with an `Err` and
	/// nothing will change.
	///
	/// If the operation is successful, this will return `Ok` with a `Debt` of the total value
	/// added to the account.
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
		best_effort: bool,
	) -> Result<DebtOf<AccountId, Self>, DispatchError>;

	/// Removes `value` balance from the `asset` account of `who` if possible.
	///
	/// If `best_effort` is `true` and `value` in full could not be removed (e.g. due to underflow),
	/// then the maximum is removed, up to `value`. If `best_effort` is `false`, then exactly
	/// `value` must be removed from the account of `who` or the operation will fail with an `Err`
	/// and nothing will change.
	///
	/// If the removal is needed but not possible, then it returns `Err` and nothing is changed.
	/// If the account needed to be deleted, then slightly more than `value` may be removed from the
	/// account owning since up to (but not including) minimum balance may also need to be removed.
	///
	/// If the operation is successful, this will return `Ok` with a `Credit` of the total value
	/// removed from the account.
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
	) -> Result<CreditOf<AccountId, Self>, DispatchError>;

	/// The balance of `who` is increased in order to counter `credit`. If the whole of `credit`
	/// cannot be countered, then nothing is changed and the original `credit` is returned in an
	/// `Err`.
	///
	/// Please note: If `credit.peek()` is less than `Self::minimum_balance()`, then `who` must
	/// already exist for this to succeed.
	fn resolve(
		who: &AccountId,
		credit: CreditOf<AccountId, Self>,
	) -> Result<(), CreditOf<AccountId, Self>> {
		let v = credit.peek();
		let debt = match Self::deposit(credit.asset(), who, v, false) {
			Err(_) => return Err(credit),
			Ok(d) => d,
		};
		if let Ok(result) = credit.offset(debt) {
			let result = result.try_drop();
			debug_assert!(result.is_ok(), "ok deposit return must be equal to credit value; qed");
		} else {
			debug_assert!(false, "debt.asset is credit.asset; qed");
		}
		Ok(())
	}

	/// The balance of `who` is decreased in order to counter `debt`. If the whole of `debt`
	/// cannot be countered, then nothing is changed and the original `debt` is returned in an
	/// `Err`.
	fn settle(
		who: &AccountId,
		debt: DebtOf<AccountId, Self>,
		keep_alive: KeepAlive,
	) -> Result<CreditOf<AccountId, Self>, DebtOf<AccountId, Self>> {
		let amount = debt.peek();
		let asset = debt.asset();
		let credit = match Self::withdraw(asset, who, amount, false, keep_alive) {
			Err(_) => return Err(debt),
			Ok(d) => d,
		};
		match credit.offset(debt) {
			Ok(SameOrOther::None) => Ok(CreditOf::<AccountId, Self>::zero(asset)),
			Ok(SameOrOther::Same(dust)) => Ok(dust),
			Ok(SameOrOther::Other(rest)) => {
				debug_assert!(false, "ok withdraw return must be at least debt value; qed");
				Err(rest)
			},
			Err(_) => {
				debug_assert!(false, "debt.asset is credit.asset; qed");
				Ok(CreditOf::<AccountId, Self>::zero(asset))
			},
		}
	}
}

/// A fungible token class where the balance can be set arbitrarily.
///
/// **WARNING**
/// Do not use this directly unless you want trouble, since it allows you to alter account balances
/// without keeping the issuance up to date. It has no safeguards against accidentally creating
/// token imbalances in your system leading to accidental inflation or deflation. It's really just
/// for the underlying datatype to implement so the user gets the much safer `Balanced` trait to
/// use.
pub trait Unbalanced<AccountId>: Inspect<AccountId> {
	/// Forcefully set the `asset` balance of `who` to `amount`.
	///
	/// If this this call executes successfully, you can `assert_eq!(Self::balance(), amount);`.
	///
	/// For implementations which include one or more balances on hold, then these are *not*
	/// included in the `amount`.
	///
	/// This function does its best to force the balance change through, but will not break system
	/// invariants such as any Existential Deposits needed or overflows/underflows.
	/// If this cannot be done for some reason (e.g. because the account cannot be created, deleted
	/// or would overflow) then an `Err` is returned.
	fn set_balance(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Set the total issuance of `asset` to `amount`.
	fn set_total_issuance(asset: Self::AssetId, amount: Self::Balance);

	/// Reduce the `asset` balance of `who` by `amount`.
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
		asset: Self::AssetId,
		who: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
	) -> Result<Self::Balance, DispatchError> {
		let free = Self::reducible_balance(asset, who, keep_alive, false);
		if best_effort {
			amount = amount.min(free);
		}
		let new_free = free.checked_sub(&amount).ok_or(TokenError::FundsUnavailable)?;
		Self::set_balance(asset, who, new_free)?;
		Ok(amount)
	}

	/// Increase the `asset` balance of `who` by `amount`.
	///
	/// If it cannot be increased by that amount for some reason, return `Err` and don't increase
	/// it at all. If Ok, return the imbalance.
	/// Minimum balance will be respected and an error will be returned if
	/// `amount < Self::minimum_balance()` when the account of `who` is zero.
	fn increase_balance(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance(asset, who);
		let new_balance = if best_effort {
			old_balance.saturating_add(amount)
		} else {
			old_balance.checked_add(&amount).ok_or(ArithmeticError::Overflow)?
		};
		if new_balance < Self::minimum_balance(asset) {
			// Attempt to increase from 0 to below minimum -> stays at zero.
			if best_effort {
				Ok(Self::Balance::zero())
			} else {
				Err(TokenError::BelowMinimum.into())
			}
		} else {
			let amount = new_balance.saturating_sub(old_balance);
			if !amount.is_zero() {
				Self::set_balance(asset, who, new_balance)?;
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
	fn set_balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		amount: Self::Balance,
	) -> DispatchResult;

	/// Reduce the balance on hold of `who` by `amount`.
	///
	/// If `best_effort` is `false` and it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If `best_effort` is `true`, then
	/// reduce the balance of `who` by the most that is possible, up to `amount`.
	///
	/// In either case, if `Ok` is returned then the inner is the amount by which is was reduced.
	fn decrease_balance_on_hold(
		asset: Self::AssetId,
		reason: &Self::Reason,
		who: &AccountId,
		mut amount: Self::Balance,
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(asset, reason, who);
		if best_effort {
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
		best_effort: bool,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance_on_hold(asset, reason, who);
		let new_balance = if best_effort {
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

/// Simple handler for an imbalance drop which increases the total issuance of the system by the
/// imbalance amount. Used for leftover debt.
pub struct IncreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: Unbalanced<AccountId>> HandleImbalanceDrop<U::AssetId, U::Balance>
	for IncreaseIssuance<AccountId, U>
{
	fn handle(asset: U::AssetId, amount: U::Balance) {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_add(amount))
	}
}

/// Simple handler for an imbalance drop which decreases the total issuance of the system by the
/// imbalance amount. Used for leftover credit.
pub struct DecreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: Unbalanced<AccountId>> HandleImbalanceDrop<U::AssetId, U::Balance>
	for DecreaseIssuance<AccountId, U>
{
	fn handle(asset: U::AssetId, amount: U::Balance) {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_sub(amount))
	}
}

/// An imbalance type which uses `DecreaseIssuance` to deal with anything `Drop`ed.
///
/// Basically means that funds in someone's account have been removed and not yet placed anywhere
/// else. If it gets dropped, then those funds will be assumed to be "burned" and the total supply
/// will be accordingly decreased to ensure it equals the sum of the balances of all accounts.
type Credit<AccountId, U> = Imbalance<
	<U as Inspect<AccountId>>::AssetId,
	<U as Inspect<AccountId>>::Balance,
	DecreaseIssuance<AccountId, U>,
	IncreaseIssuance<AccountId, U>,
>;

/// An imbalance type which uses `IncreaseIssuance` to deal with anything `Drop`ed.
///
/// Basically means that there are funds in someone's account whose origin is as yet unaccounted
/// for. If it gets dropped, then those funds will be assumed to be "minted" and the total supply
/// will be accordingly increased to ensure it equals the sum of the balances of all accounts.
type Debt<AccountId, U> = Imbalance<
	<U as Inspect<AccountId>>::AssetId,
	<U as Inspect<AccountId>>::Balance,
	IncreaseIssuance<AccountId, U>,
	DecreaseIssuance<AccountId, U>,
>;

/// Create some `Credit` item. Only for internal use.
fn credit<AccountId, U: Unbalanced<AccountId>>(
	asset: U::AssetId,
	amount: U::Balance,
) -> Credit<AccountId, U> {
	Imbalance::new(asset, amount)
}

/// Create some `Debt` item. Only for internal use.
fn debt<AccountId, U: Unbalanced<AccountId>>(
	asset: U::AssetId,
	amount: U::Balance,
) -> Debt<AccountId, U> {
	Imbalance::new(asset, amount)
}

impl<AccountId, U: Unbalanced<AccountId>> Balanced<AccountId> for U {
	type OnDropCredit = DecreaseIssuance<AccountId, U>;
	type OnDropDebt = IncreaseIssuance<AccountId, U>;
	fn rescind(asset: Self::AssetId, amount: Self::Balance) -> Debt<AccountId, Self> {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_sub(amount));
		debt(asset, amount)
	}
	fn issue(asset: Self::AssetId, amount: Self::Balance) -> Credit<AccountId, Self> {
		U::set_total_issuance(asset, U::total_issuance(asset).saturating_add(amount));
		credit(asset, amount)
	}
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
	) -> Result<Debt<AccountId, Self>, DispatchError> {
		let increase = U::increase_balance(asset, who, amount, best_effort)?;
		Ok(debt(asset, increase))
	}
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
	) -> Result<Credit<AccountId, Self>, DispatchError> {
		let decrease = U::decrease_balance(asset, who, amount, best_effort, keep_alive)?;
		Ok(credit(asset, decrease))
	}
}
