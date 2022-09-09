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
use sp_arithmetic::traits::Saturating;
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

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then a non-zero second item will be returned.
	fn slash(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> (CreditOf<AccountId, Self>, Self::Balance);

	/// Mints exactly `value` into the `asset` account of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an `Err` returned. This could happen because it
	/// the account doesn't yet exist and it isn't possible to create it under the current
	/// circumstances and with `value` in it.
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
	) -> Result<DebtOf<AccountId, Self>, DispatchError>;

	/// Removes `value` free `asset` balance from `who` account if possible.
	///
	/// If the removal is not possible, then it returns `Err` and nothing is changed.
	///
	/// If the operation is successful, this will return `Ok` with a `NegativeImbalance` whose value
	/// is no less than `value`. It may be more in the case that removing it reduced it below
	/// `Self::minimum_balance()`.
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		value: Self::Balance,
		// TODO: liveness: ExistenceRequirement,
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
		let debt = match Self::deposit(credit.asset(), who, v) {
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
		// TODO: liveness: ExistenceRequirement,
	) -> Result<CreditOf<AccountId, Self>, DebtOf<AccountId, Self>> {
		let amount = debt.peek();
		let asset = debt.asset();
		let credit = match Self::withdraw(asset, who, amount) {
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
	/// Set the `asset` balance of `who` to `amount`. If this cannot be done for some reason (e.g.
	/// because the account cannot be created or an overflow) then an `Err` is returned.
	fn set_balance(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Set the total issuance of `asset` to `amount`.
	fn set_total_issuance(asset: Self::AssetId, amount: Self::Balance);

	/// Reduce the `asset` balance of `who` by `amount`. If it cannot be reduced by that amount for
	/// some reason, return `Err` and don't reduce it at all. If Ok, return the imbalance.
	///
	/// Minimum balance will be respected and the returned imbalance may be up to
	/// `Self::minimum_balance() - 1` greater than `amount`.
	fn decrease_balance(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance(asset, who);
		let (mut new_balance, mut amount) = if old_balance < amount {
			return Err(TokenError::NoFunds.into())
		} else {
			(old_balance - amount, amount)
		};
		if new_balance < Self::minimum_balance(asset) {
			amount = amount.saturating_add(new_balance);
			new_balance = Zero::zero();
		}
		// Defensive only - this should not fail now.
		Self::set_balance(asset, who, new_balance)?;
		Ok(amount)
	}

	/// Reduce the `asset` balance of `who` by the most that is possible, up to `amount`.
	///
	/// Minimum balance will be respected and the returned imbalance may be up to
	/// `Self::minimum_balance() - 1` greater than `amount`.
	///
	/// Return the imbalance by which the account was reduced.
	fn decrease_balance_at_most(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> Self::Balance {
		let old_balance = Self::balance(asset, who);
		let (mut new_balance, mut amount) = if old_balance < amount {
			(Zero::zero(), old_balance)
		} else {
			(old_balance - amount, amount)
		};
		let minimum_balance = Self::minimum_balance(asset);
		if new_balance < minimum_balance {
			amount = amount.saturating_add(new_balance);
			new_balance = Zero::zero();
		}
		let mut r = Self::set_balance(asset, who, new_balance);
		if r.is_err() {
			// Some error, probably because we tried to destroy an account which cannot be
			// destroyed.
			if new_balance.is_zero() && amount >= minimum_balance {
				new_balance = minimum_balance;
				amount -= minimum_balance;
				r = Self::set_balance(asset, who, new_balance);
			}
			if r.is_err() {
				// Still an error. Apparently it's not possible to reduce at all.
				amount = Zero::zero();
			}
		}
		amount
	}

	/// Increase the `asset` balance of `who` by `amount`. If it cannot be increased by that amount
	/// for some reason, return `Err` and don't increase it at all. If Ok, return the imbalance.
	///
	/// Minimum balance will be respected and an error will be returned if
	/// `amount < Self::minimum_balance()` when the account of `who` is zero.
	fn increase_balance(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		let old_balance = Self::balance(asset, who);
		let new_balance = old_balance.checked_add(&amount).ok_or(ArithmeticError::Overflow)?;
		if new_balance < Self::minimum_balance(asset) {
			return Err(TokenError::BelowMinimum.into())
		}
		if old_balance != new_balance {
			Self::set_balance(asset, who, new_balance)?;
		}
		Ok(amount)
	}

	/// Increase the `asset` balance of `who` by the most that is possible, up to `amount`.
	///
	/// Minimum balance will be respected and the returned imbalance will be zero in the case that
	/// `amount < Self::minimum_balance()`.
	///
	/// Return the imbalance by which the account was increased.
	fn increase_balance_at_most(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> Self::Balance {
		let old_balance = Self::balance(asset, who);
		let mut new_balance = old_balance.saturating_add(amount);
		let mut amount = new_balance - old_balance;
		if new_balance < Self::minimum_balance(asset) {
			new_balance = Zero::zero();
			amount = Zero::zero();
		}
		if old_balance == new_balance || Self::set_balance(asset, who, new_balance).is_ok() {
			amount
		} else {
			Zero::zero()
		}
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
	fn slash(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> (Credit<AccountId, Self>, Self::Balance) {
		let slashed = U::decrease_balance_at_most(asset, who, amount);
		// `slashed` could be less than, greater than or equal to `amount`.
		// If slashed == amount, it means the account had at least amount in it and it could all be
		//   removed without a problem.
		// If slashed > amount, it means the account had more than amount in it, but not enough more
		//   to push it over minimum_balance.
		// If slashed < amount, it means the account didn't have enough in it to be reduced by
		//   `amount` without being destroyed.
		(credit(asset, slashed), amount.saturating_sub(slashed))
	}
	fn deposit(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> Result<Debt<AccountId, Self>, DispatchError> {
		let increase = U::increase_balance(asset, who, amount)?;
		Ok(debt(asset, increase))
	}
	fn withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		// TODO: liveness: ExistenceRequirement,
	) -> Result<Credit<AccountId, Self>, DispatchError> {
		let decrease = U::decrease_balance(asset, who, amount)?;
		Ok(credit(asset, decrease))
	}
}
