// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use super::*;
use sp_runtime::traits::Saturating;
use crate::traits::misc::Get;
use crate::dispatch::{DispatchResult, DispatchError};
use super::misc::{DepositConsequence, WithdrawConsequence, Balance};

mod balanced;
mod imbalance;
pub use balanced::{Balanced, Unbalanced};
pub use imbalance::{Imbalance, HandleImbalanceDrop, DebtOf, CreditOf};

/// Trait for providing balance-inspection access to a fungible asset.
pub trait Inspect<AccountId> {
	/// Scalar type for representing balance of an account.
	type Balance: Balance;
	/// The total amount of issuance in the system.
	fn total_issuance() -> Self::Balance;
	/// The minimum balance any single account may have.
	fn minimum_balance() -> Self::Balance;
	/// Get the balance of `who`.
	fn balance(who: &AccountId) -> Self::Balance;
	/// Returns `true` if the balance of `who` may be increased by `amount`.
	fn can_deposit(who: &AccountId, amount: Self::Balance) -> DepositConsequence;
	/// Returns `Failed` if the balance of `who` may not be decreased by `amount`, otherwise
	/// the consequence.
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance>;
}

/// Trait for providing an ERC-20 style fungible asset.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Increase the balance of `who` by `amount`.
	fn deposit(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Attempt to reduce the balance of `who` by `amount`.
	fn withdraw(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError>;
	/// Transfer funds from one account into another.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		let extra = Self::can_withdraw(&source, amount).into_result()?;
		Self::can_deposit(&dest, amount.saturating_add(extra)).into_result()?;
		let actual = Self::withdraw(source, amount)?;
		debug_assert!(actual == amount.saturating_add(extra), "can_withdraw must agree with withdraw; qed");
		match Self::deposit(dest, actual) {
			Ok(_) => Ok(actual),
			Err(err) => {
				debug_assert!(false, "can_deposit returned true previously; qed");
				// attempt to return the funds back to source
				let revert = Self::deposit(source, actual);
				debug_assert!(revert.is_ok(), "withdrew funds previously; qed");
				Err(err)
			}
		}
	}
}

/// Trait for providing a fungible asset which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer funds from one account into another.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError>;
}

/// Trait for providing a fungible asset which can be reserved.
pub trait Reserve<AccountId>: Inspect<AccountId> {
	/// Amount of funds held in reserve by `who`.
	fn reserved_balance(who: &AccountId) -> Self::Balance;
	/// Amount of funds held in total by `who`.
	fn total_balance(who: &AccountId) -> Self::Balance {
		Self::reserved_balance(who).saturating_add(Self::balance(who))
	}
	/// Check to see if some `amount` of funds may be reserved on the account of `who`.
	fn can_reserve(who: &AccountId, amount: Self::Balance) -> bool;
	/// Reserve some funds in an account.
	fn reserve(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Unreserve some funds in an account.
	fn unreserve(who: &AccountId, amount: Self::Balance) -> DispatchResult;
	/// Transfer reserved funds into another account.
	fn repatriate_reserved(
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult;
}

pub struct ItemOf<
	F: fungibles::Inspect<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
>(
	sp_std::marker::PhantomData<(F, A, AccountId)>
);

impl<
	F: fungibles::Inspect<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
> Inspect<AccountId> for ItemOf<F, A, AccountId> {
	type Balance = <F as fungibles::Inspect<AccountId>>::Balance;
	fn total_issuance() -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::total_issuance(A::get())
	}
	fn minimum_balance() -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::minimum_balance(A::get())
	}
	fn balance(who: &AccountId) -> Self::Balance {
		<F as fungibles::Inspect<AccountId>>::balance(A::get(), who)
	}
	fn can_deposit(who: &AccountId, amount: Self::Balance) -> DepositConsequence {
		<F as fungibles::Inspect<AccountId>>::can_deposit(A::get(), who, amount)
	}
	fn can_withdraw(who: &AccountId, amount: Self::Balance) -> WithdrawConsequence<Self::Balance> {
		<F as fungibles::Inspect<AccountId>>::can_withdraw(A::get(), who, amount)
	}
}

impl<
	F: fungibles::Mutate<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
> Mutate<AccountId> for ItemOf<F, A, AccountId> {
	fn deposit(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as fungibles::Mutate<AccountId>>::deposit(A::get(), who, amount)
	}
	fn withdraw(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::Mutate<AccountId>>::withdraw(A::get(), who, amount)
	}
}

impl<
	F: fungibles::Transfer<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
> Transfer<AccountId> for ItemOf<F, A, AccountId> {
	fn transfer(source: &AccountId, dest: &AccountId, amount: Self::Balance)
		-> Result<Self::Balance, DispatchError>
	{
		<F as fungibles::Transfer<AccountId>>::transfer(A::get(), source, dest, amount)
	}
}

impl<
	F: fungibles::Reserve<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
> Reserve<AccountId> for ItemOf<F, A, AccountId> {
	fn reserved_balance(who: &AccountId) -> Self::Balance {
		<F as fungibles::Reserve<AccountId>>::reserved_balance(A::get(), who)
	}
	fn total_balance(who: &AccountId) -> Self::Balance {
		<F as fungibles::Reserve<AccountId>>::total_balance(A::get(), who)
	}
	fn can_reserve(who: &AccountId, amount: Self::Balance) -> bool {
		<F as fungibles::Reserve<AccountId>>::can_reserve(A::get(), who, amount)
	}
	fn reserve(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as fungibles::Reserve<AccountId>>::reserve(A::get(), who, amount)
	}
	fn unreserve(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as fungibles::Reserve<AccountId>>::unreserve(A::get(), who, amount)
	}
	fn repatriate_reserved(
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult {
		<F as fungibles::Reserve<AccountId>>::repatriate_reserved(A::get(), who, amount, status)
	}
}

impl<
	F: fungibles::Unbalanced<AccountId>,
	A: Get<<F as fungibles::Inspect<AccountId>>::AssetId>,
	AccountId,
> Unbalanced<AccountId> for ItemOf<F, A, AccountId> {
	fn set_balance(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		<F as fungibles::Unbalanced<AccountId>>::set_balance(A::get(), who, amount)
	}
	fn set_total_issuance(amount: Self::Balance) -> () {
		<F as fungibles::Unbalanced<AccountId>>::set_total_issuance(A::get(), amount)
	}
	fn decrease_balance(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::Unbalanced<AccountId>>::decrease_balance(A::get(), who, amount)
	}
	fn decrease_balance_at_most(who: &AccountId, amount: Self::Balance) -> Self::Balance {
		<F as fungibles::Unbalanced<AccountId>>::decrease_balance_at_most(A::get(), who, amount)
	}
	fn increase_balance(who: &AccountId, amount: Self::Balance) -> Result<Self::Balance, DispatchError> {
		<F as fungibles::Unbalanced<AccountId>>::increase_balance(A::get(), who, amount)
	}
	fn increase_balance_at_most(who: &AccountId, amount: Self::Balance) -> Self::Balance {
		<F as fungibles::Unbalanced<AccountId>>::increase_balance_at_most(A::get(), who, amount)
	}
}

