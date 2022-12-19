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

use super::{
	misc::{Balance, DepositConsequence, KeepAlive, WithdrawConsequence},
	*,
};
use crate::{
	dispatch::{DispatchError, DispatchResult},
	traits::misc::Get,
};
use scale_info::TypeInfo;
use sp_runtime::traits::Saturating;

mod balanced;
mod freeze;
mod hold;
mod imbalance;
mod item_of;
mod unbalanced;

pub use balanced::Balanced;
pub use freeze::{InspectFreeze, MutateFreeze};
pub use hold::{BalancedHold, InspectHold, MutateHold};
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
pub trait Mutate<AccountId>: Inspect<AccountId> {
	/// Increase the balance of `who` by exactly `amount`, minting new tokens. If that isn't
	/// possible then an `Err` is returned and nothing is changed.
	fn mint_into(who: &AccountId, amount: Self::Balance) -> DispatchResult;

	/// Decrease the balance of `who` by at least `amount`, possibly slightly more in the case of
	/// minimum-balance requirements, burning the tokens. If that isn't possible then an `Err` is
	/// returned and nothing is changed. If successful, the amount of tokens reduced is returned.
	fn burn_from(
		who: &AccountId,
		amount: Self::Balance,
		best_effort: bool,
		force: bool,
	) -> Result<Self::Balance, DispatchError>;

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
	fn suspend(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		Self::burn_from(who, amount, false, false).map(|_| ())
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
	fn resume(who: &AccountId, amount: Self::Balance) -> DispatchResult {
		Self::mint_into(who, amount)
	}

	/// Transfer funds from one account into another. The default implementation uses `mint_into`
	/// and `burn_from` and may generate unwanted events.
	fn teleport(
		source: &AccountId,
		dest: &AccountId,
		amount: Self::Balance,
	) -> Result<Self::Balance, DispatchError> {
		let extra = Self::can_withdraw(&source, amount).into_result()?;
		// As we first burn and then mint, we don't need to check if `mint` fits into the supply.
		// If we can withdraw/burn it, we can also mint it again.
		let actual = amount.saturating_add(extra);
		Self::can_deposit(dest, actual, false).into_result()?;
		Self::suspend(source, actual)?;
		match Self::resume(dest, actual) {
			Ok(_) => Ok(actual),
			Err(err) => {
				debug_assert!(false, "can_deposit returned true previously; qed");
				// attempt to return the funds back to source
				let revert = Self::resume(source, actual);
				debug_assert!(revert.is_ok(), "withdrew funds previously; qed");
				Err(err)
			},
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
		keep_alive: KeepAlive,
	) -> Result<Self::Balance, DispatchError>;

	/// Reduce the active issuance by some amount.
	fn deactivate(_: Self::Balance) {}

	/// Increase the active issuance by some amount, up to the outstanding amount reduced.
	fn reactivate(_: Self::Balance) {}
}
