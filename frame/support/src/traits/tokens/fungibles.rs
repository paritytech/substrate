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

//! The traits for sets of fungible tokens and any associated types.

use super::*;
use crate::dispatch::{DispatchError, DispatchResult};
use super::misc::{AssetId, Balance};
use sp_runtime::traits::Saturating;

mod balanced;
pub use balanced::{Balanced, Unbalanced};
mod imbalance;
pub use imbalance::{Imbalance, HandleImbalanceDrop, DebtOf, CreditOf};

/// Trait for providing balance-inspection access to a set of named fungible assets.
pub trait Inspect<AccountId> {
	/// Means of identifying one asset class from another.
	type AssetId: AssetId;
	/// Scalar type for representing balance of an account.
	type Balance: Balance;
	/// The total amount of issuance in the system.
	fn total_issuance(asset: Self::AssetId) -> Self::Balance;
	/// The minimum balance any single account may have.
	fn minimum_balance(asset: Self::AssetId) -> Self::Balance;
	/// Get the `asset` balance of `who`.
	fn balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;
	/// Returns `true` if the `asset` balance of `who` may be increased by `amount`.
	fn can_deposit(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> DepositConsequence;
	/// Returns `Failed` if the `asset` balance of `who` may not be decreased by `amount`, otherwise
	/// the consequence.
	fn can_withdraw(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
	) -> WithdrawConsequence<Self::Balance>;
}

/// Trait for providing a set of named fungible assets which can be created and destroyed.
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Attempt to increase the `asset` balance of `who` by `amount`.
	///
	/// If not possible then don't do anything. Possible reasons for failure include:
	/// - Minimum balance not met.
	/// - Account cannot be created (e.g. because there is no provider reference and/or the asset
	///   isn't considered worth anything).
	///
	/// Since this is an operation which should be possible to take alone, if successful it will
	/// increase the overall supply of the underlying token.
	fn deposit(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Attempt to reduce the `asset` balance of `who` by `amount`.
	///
	/// If not possible then don't do anything. Possible reasons for failure include:
	/// - Less funds in the account than `amount`
	/// - Liquidity requirements (locks, reservations) prevent the funds from being removed
	/// - Operation would require destroying the account and it is required to stay alive (e.g.
	///   because it's providing a needed provider reference).
	///
	/// Since this is an operation which should be possible to take alone, if successful it will
	/// reduce the overall supply of the underlying token.
	///
	/// Due to minimum balance requirements, it's possible that the amount withdrawn could be up to
	/// `Self::minimum_balance() - 1` more than the `amount`. The total amount withdrawn is returned
	/// in an `Ok` result. This may be safely ignored if you don't mind the overall supply reducing.
	fn withdraw(asset: Self::AssetId, who: &AccountId, amount: Self::Balance)
		-> Result<Self::Balance, DispatchError>;

	/// Transfer funds from one account into another.
	fn transfer(
		asset: Self::AssetId,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		let extra = Self::can_withdraw(asset, &source, amount).into_result()?;
		Self::can_deposit(asset, &dest, amount.saturating_add(extra)).into_result()?;
		let actual = Self::withdraw(asset, source, amount)?;
		debug_assert!(actual == amount.saturating_add(extra), "can_withdraw must agree with withdraw; qed");
		match Self::deposit(asset, dest, actual) {
			Ok(_) => Ok(actual),
			Err(err) => {
				debug_assert!(false, "can_deposit returned true previously; qed");
				// attempt to return the funds back to source
				let revert = Self::deposit(asset, source, actual);
				debug_assert!(revert.is_ok(), "withdrew funds previously; qed");
				Err(err)
			}
		}
	}
}

/// Trait for providing a set of named fungible assets which can only be transferred.
pub trait Transfer<AccountId>: Inspect<AccountId> {
	/// Transfer funds from one account into another.
	fn transfer(
		asset: Self::AssetId,
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError>;
}

/// Trait for providing a set of named fungible assets which can be reserved.
pub trait Reserve<AccountId>: Inspect<AccountId> {
	/// Amount of funds held in reserve.
	fn reserved_balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;

	/// Amount of funds held in reserve.
	fn total_balance(asset: Self::AssetId, who: &AccountId) -> Self::Balance;

	/// Check to see if some `amount` of `asset` may be reserved on the account of `who`.
	fn can_reserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> bool;

	/// Reserve some funds in an account.
	fn reserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Unreserve some funds in an account.
	fn unreserve(asset: Self::AssetId, who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Transfer reserved funds into another account.
	fn repatriate_reserved(
		asset: Self::AssetId,
		who: &AccountId,
		amount: Self::Balance,
		status: BalanceStatus,
	) -> DispatchResult;
}
