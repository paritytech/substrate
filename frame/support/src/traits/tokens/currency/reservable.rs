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

//! The reservable currency trait.

use super::Currency;
use super::super::misc::BalanceStatus;
use crate::dispatch::{DispatchResult, DispatchError};

/// A currency where funds can be reserved from the user.
pub trait ReservableCurrency<AccountId>: Currency<AccountId> {
	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	fn can_reserve(who: &AccountId, value: Self::Balance) -> bool;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If the reserve balance of `who`
	/// is less than `value`, then a non-zero second item will be returned.
	fn slash_reserved(
		who: &AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance);

	/// The amount of the balance of a given account that is externally reserved; this can still get
	/// slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable.
	///
	/// When this balance falls below the value of `ExistentialDeposit`, then this 'reserve account'
	/// is deleted: specifically, `ReservedBalance`.
	///
	/// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn reserved_balance(who: &AccountId) -> Self::Balance;

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behavior than `unreserve`.
	fn reserve(who: &AccountId, value: Self::Balance) -> DispatchResult;

	/// Moves up to `value` from reserved balance to free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be moved as possible. If the reserve balance of `who`
	/// is less than `value`, then the remaining amount will be returned.
	///
	/// # NOTES
	///
	/// - This is different from `reserve`.
	/// - If the remaining reserved balance is less than `ExistentialDeposit`, it will
	/// invoke `on_reserved_too_low` and could reap the account.
	fn unreserve(who: &AccountId, value: Self::Balance) -> Self::Balance;

	/// Moves up to `value` from reserved balance of account `slashed` to balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned. Funds will be placed in either the `free` balance or the `reserved` balance,
	/// depending on the `status`.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Ok(non_zero)` will be returned.
	fn repatriate_reserved(
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance,
		status: BalanceStatus,
	) -> Result<Self::Balance, DispatchError>;
}

pub trait NamedReservableCurrency<AccountId>: ReservableCurrency<AccountId> {
	/// An identifier for a reserve. Used for disambiguating different reserves so that
	/// they can be individually replaced or removed.
	type ReserveIdentifier;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If the reserve balance of `who`
	/// is less than `value`, then a non-zero second item will be returned.
	fn slash_reserved_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance);

	/// The amount of the balance of a given account that is externally reserved; this can still get
	/// slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable.
	///
	/// When this balance falls below the value of `ExistentialDeposit`, then this 'reserve account'
	/// is deleted: specifically, `ReservedBalance`.
	///
	/// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn reserved_balance_named(id: &Self::ReserveIdentifier, who: &AccountId) -> Self::Balance;

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behavior than `unreserve`.
	fn reserve_named(id: &Self::ReserveIdentifier, who: &AccountId, value: Self::Balance) -> DispatchResult;

	/// Moves up to `value` from reserved balance to free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be moved as possible. If the reserve balance of `who`
	/// is less than `value`, then the remaining amount will be returned.
	///
	/// # NOTES
	///
	/// - This is different from `reserve`.
	/// - If the remaining reserved balance is less than `ExistentialDeposit`, it will
	/// invoke `on_reserved_too_low` and could reap the account.
	fn unreserve_named(id: &Self::ReserveIdentifier, who: &AccountId, value: Self::Balance) -> Self::Balance;

	/// Moves up to `value` from reserved balance of account `slashed` to balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned. Funds will be placed in either the `free` balance or the `reserved` balance,
	/// depending on the `status`.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Ok(non_zero)` will be returned.
	fn repatriate_reserved_named(
		id: &Self::ReserveIdentifier,
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance,
		status: BalanceStatus,
	) -> Result<Self::Balance, DispatchError>;

	/// Ensure the reserved balance is equal to `value`.
	///
	/// This will reserve extra amount of current reserved balance is less than `value`.
	/// And unreserve if current reserved balance is greater than `value`.
	fn ensure_reserved_named(id: &Self::ReserveIdentifier, who: &AccountId, value: Self::Balance) -> DispatchResult {
		let current = Self::reserved_balance_named(id, who);
 		if current > value {
			// we always have enough balance to unreserve here
			Self::unreserve_named(id, who, current - value);
			Ok(())
		} else if value > current {
			// we checked value > current
			Self::reserve_named(id, who, value - current)
		} else { // current == value
			Ok(())
		}
	}

	/// Unreserve all the named reserved balances, returning unreserved amount.
	///
	/// Is a no-op if the value to be unreserved is zero.
	fn unreserve_all_named(id: &Self::ReserveIdentifier, who: &AccountId) -> Self::Balance {
		let value = Self::reserved_balance_named(id, who);
		Self::slash_reserved_named(id, who, value);
		value
	}

	/// Slash all the reserved balance, returning the negative imbalance created.
	///
	/// Is a no-op if the value to be slashed is zero.
	fn slash_all_reserved_named(id: &Self::ReserveIdentifier, who: &AccountId) -> Self::NegativeImbalance {
		let value = Self::reserved_balance_named(id, who);
		Self::slash_reserved_named(id, who, value).0
	}

	/// Move all the named reserved balance of one account into the balance of another, according to `status`.
	/// If `status` is `Reserved`, the balance will be reserved with given `id`.
	///
	/// Is a no-op if:
	/// - the value to be moved is zero; or
	/// - the `slashed` id equal to `beneficiary` and the `status` is `Reserved`.
	fn repatriate_all_reserved_named(
		id: &Self::ReserveIdentifier,
		slashed: &AccountId,
		beneficiary: &AccountId,
		status: BalanceStatus,
	) -> DispatchResult {
		let value = Self::reserved_balance_named(id, slashed);
		Self::repatriate_reserved_named(id, slashed, beneficiary, value, status).map(|_| ())
	}
}
