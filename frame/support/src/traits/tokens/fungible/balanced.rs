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

use super::{super::Imbalance as ImbalanceT, *};
use crate::{
	dispatch::DispatchError,
	traits::{
		misc::{SameOrOther, TryDrop},
		tokens::KeepAlive,
	},
};
use sp_runtime::Saturating;
use sp_std::marker::PhantomData;

/// A fungible token class where any creation and deletion of tokens is semi-explicit and where the
/// total supply is maintained automatically.
///
/// This is auto-implemented when a token class has `Unbalanced` implemented.
pub trait Balanced<AccountId>: Inspect<AccountId> + Unbalanced<AccountId> {
	/// The type for managing what happens when an instance of `Debt` is dropped without being used.
	type OnDropDebt: HandleImbalanceDrop<Self::Balance>;
	/// The type for managing what happens when an instance of `Credit` is dropped without being
	/// used.
	type OnDropCredit: HandleImbalanceDrop<Self::Balance>;

	/// Reduce the total issuance by `amount` and return the according imbalance. The imbalance will
	/// typically be used to reduce an account by the same amount with e.g. `settle`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is burnt, for example
	/// in the case of underflow.
	fn rescind(amount: Self::Balance) -> DebtOf<AccountId, Self> {
		let old = Self::total_issuance();
		let new = old.saturating_sub(amount);
		Self::set_total_issuance(new);
		let delta = old - new;
		Self::done_rescind(delta);
		Imbalance::<Self::Balance, Self::OnDropDebt, Self::OnDropCredit>::new(delta)
	}

	/// Increase the total issuance by `amount` and return the according imbalance. The imbalance
	/// will typically be used to increase an account by the same amount with e.g.
	/// `resolve_into_existing` or `resolve_creating`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is issued, for example
	/// in the case of overflow.
	fn issue(amount: Self::Balance) -> CreditOf<AccountId, Self> {
		let old = Self::total_issuance();
		let new = old.saturating_add(amount);
		Self::set_total_issuance(new);
		let delta = new - old;
		Self::done_issue(delta);
		Imbalance::<Self::Balance, Self::OnDropCredit, Self::OnDropDebt>::new(delta)
	}

	/// Produce a pair of imbalances that cancel each other out exactly.
	///
	/// This is just the same as burning and issuing the same amount and has no effect on the
	/// total issuance.
	fn pair(amount: Self::Balance) -> (DebtOf<AccountId, Self>, CreditOf<AccountId, Self>) {
		(Self::rescind(amount), Self::issue(amount))
	}

	/// Mints `value` into the account of `who`, creating it as needed.
	///
	/// If `best_effort` is `true` and `value` in full could not be minted (e.g. due to overflow),
	/// then the maximum is minted, up to `value`. If `best_effort` is `false`, then exactly `value`
	/// must be minted into the account of `who` or the operation will fail with an `Err` and
	/// nothing will change.
	///
	/// If the operation is successful, this will return `Ok` with a `Debt` of the total value
	/// added to the account.
	fn deposit(
		who: &AccountId,
		value: Self::Balance,
		best_effort: bool,
	) -> Result<DebtOf<AccountId, Self>, DispatchError> {
		let increase = Self::increase_balance(who, value, best_effort)?;
		Self::done_deposit(who, increase);
		Ok(Imbalance::<Self::Balance, Self::OnDropDebt, Self::OnDropCredit>::new(increase))
	}

	/// Removes `value` balance from `who` account if possible.
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
		who: &AccountId,
		value: Self::Balance,
		best_effort: bool,
		keep_alive: KeepAlive,
	) -> Result<CreditOf<AccountId, Self>, DispatchError> {
		let decrease = Self::decrease_balance(who, value, best_effort, keep_alive, false)?;
		Self::done_withdraw(who, decrease);
		Ok(Imbalance::<Self::Balance, Self::OnDropCredit, Self::OnDropDebt>::new(decrease))
	}

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
		let debt = match Self::deposit(who, v, false) {
			Err(_) => return Err(credit),
			Ok(d) => d,
		};
		let result = credit.offset(debt).try_drop();
		debug_assert!(result.is_ok(), "ok deposit return must be equal to credit value; qed");
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
		let credit = match Self::withdraw(who, amount, false, keep_alive) {
			Err(_) => return Err(debt),
			Ok(d) => d,
		};

		match credit.offset(debt) {
			SameOrOther::None => Ok(CreditOf::<AccountId, Self>::zero()),
			SameOrOther::Same(dust) => Ok(dust),
			SameOrOther::Other(rest) => {
				debug_assert!(false, "ok withdraw return must be at least debt value; qed");
				Err(rest)
			},
		}
	}

	fn done_rescind(_amount: Self::Balance) {}
	fn done_issue(_amount: Self::Balance) {}
	fn done_deposit(_who: &AccountId, _amount: Self::Balance) {}
	fn done_withdraw(_who: &AccountId, _amount: Self::Balance) {}
}

/// Trait for slashing a fungible asset which can be place on hold.
pub trait BalancedHold<AccountId>: Balanced<AccountId> + UnbalancedHold<AccountId> {
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
	) -> (CreditOf<AccountId, Self>, Self::Balance) {
		let decrease =
			Self::decrease_balance_on_hold(reason, who, amount, true).unwrap_or(Default::default());
		let credit =
			Imbalance::<Self::Balance, Self::OnDropCredit, Self::OnDropDebt>::new(decrease);
		Self::done_slash(reason, who, decrease);
		(credit, amount.saturating_sub(decrease))
	}

	fn done_slash(_reason: &Self::Reason, _who: &AccountId, _amount: Self::Balance) {}
}

/// Simple handler for an imbalance drop which increases the total issuance of the system by the
/// imbalance amount. Used for leftover debt.
pub struct IncreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: Unbalanced<AccountId>> HandleImbalanceDrop<U::Balance>
	for IncreaseIssuance<AccountId, U>
{
	fn handle(amount: U::Balance) {
		U::set_total_issuance(U::total_issuance().saturating_add(amount))
	}
}

/// Simple handler for an imbalance drop which decreases the total issuance of the system by the
/// imbalance amount. Used for leftover credit.
pub struct DecreaseIssuance<AccountId, U>(PhantomData<(AccountId, U)>);
impl<AccountId, U: Unbalanced<AccountId>> HandleImbalanceDrop<U::Balance>
	for DecreaseIssuance<AccountId, U>
{
	fn handle(amount: U::Balance) {
		U::set_total_issuance(U::total_issuance().saturating_sub(amount))
	}
}
