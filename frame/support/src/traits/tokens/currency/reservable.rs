// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use scale_info::TypeInfo;
use sp_core::Get;

use super::{super::misc::BalanceStatus, Currency};
use crate::{
	dispatch::{DispatchError, DispatchResult},
	traits::{ExistenceRequirement, SignedImbalance, WithdrawReasons},
};

/// A currency where funds can be reserved from the user.
pub trait ReservableCurrency<AccountId>: Currency<AccountId> {
	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	fn can_reserve(who: &AccountId, value: Self::Balance) -> bool;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If the reserve balance of `who`
	/// is less than `value`, then the second item will be equal to the value not able to be
	/// slashed.
	fn slash_reserved(
		who: &AccountId,
		value: Self::Balance,
	) -> (Self::NegativeImbalance, Self::Balance);

	/// The amount of the balance of a given account that is externally reserved; this can still get
	/// slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable.
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
	/// is less than `value`, then the remaining amount will be returned. This is different
	/// behavior than `reserve`.
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

#[cfg(feature = "std")]
impl<AccountId> ReservableCurrency<AccountId> for () {
	fn can_reserve(_: &AccountId, _: Self::Balance) -> bool {
		true
	}
	fn slash_reserved(_: &AccountId, _: Self::Balance) -> (Self::NegativeImbalance, Self::Balance) {
		((), 0)
	}
	fn reserved_balance(_: &AccountId) -> Self::Balance {
		0
	}
	fn reserve(_: &AccountId, _: Self::Balance) -> DispatchResult {
		Ok(())
	}
	fn unreserve(_: &AccountId, _: Self::Balance) -> Self::Balance {
		0
	}
	fn repatriate_reserved(
		_: &AccountId,
		_: &AccountId,
		_: Self::Balance,
		_: BalanceStatus,
	) -> Result<Self::Balance, DispatchError> {
		Ok(0)
	}
}

pub trait NamedReservableCurrency<AccountId>: ReservableCurrency<AccountId> {
	/// An identifier for a reserve. Used for disambiguating different reserves so that
	/// they can be individually replaced or removed.
	type ReserveIdentifier: codec::Encode + TypeInfo + 'static;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If the reserve balance of `who`
	/// is less than `value`, then a non-zero second item will be returned.
	fn slash_reserved_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
		value: Self::Balance,
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
	fn reserve_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
		value: Self::Balance,
	) -> DispatchResult;

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
	fn unreserve_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
		value: Self::Balance,
	) -> Self::Balance;

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
	fn ensure_reserved_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
		value: Self::Balance,
	) -> DispatchResult {
		let current = Self::reserved_balance_named(id, who);
		if current > value {
			// we always have enough balance to unreserve here
			Self::unreserve_named(id, who, current - value);
			Ok(())
		} else if value > current {
			// we checked value > current
			Self::reserve_named(id, who, value - current)
		} else {
			// current == value
			Ok(())
		}
	}

	/// Unreserve all the named reserved balances, returning unreserved amount.
	///
	/// Is a no-op if the value to be unreserved is zero.
	fn unreserve_all_named(id: &Self::ReserveIdentifier, who: &AccountId) -> Self::Balance {
		let value = Self::reserved_balance_named(id, who);
		Self::unreserve_named(id, who, value);
		value
	}

	/// Slash all the reserved balance, returning the negative imbalance created.
	///
	/// Is a no-op if the value to be slashed is zero.
	fn slash_all_reserved_named(
		id: &Self::ReserveIdentifier,
		who: &AccountId,
	) -> Self::NegativeImbalance {
		let value = Self::reserved_balance_named(id, who);
		Self::slash_reserved_named(id, who, value).0
	}

	/// Move all the named reserved balance of one account into the balance of another, according to
	/// `status`. If `status` is `Reserved`, the balance will be reserved with given `id`.
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

/// Adapter to allow a `NamedReservableCurrency` to be passed as regular `ReservableCurrency`
/// together with an `Id`.
///
/// All "anonymous" operations are then implemented as their named counterparts with the given `Id`.
pub struct WithName<NamedReservable, Id, AccountId>(
	sp_std::marker::PhantomData<(NamedReservable, Id, AccountId)>,
);
impl<
		NamedReservable: NamedReservableCurrency<AccountId>,
		Id: Get<NamedReservable::ReserveIdentifier>,
		AccountId,
	> Currency<AccountId> for WithName<NamedReservable, Id, AccountId>
{
	type Balance = <NamedReservable as Currency<AccountId>>::Balance;
	type PositiveImbalance = <NamedReservable as Currency<AccountId>>::PositiveImbalance;
	type NegativeImbalance = <NamedReservable as Currency<AccountId>>::NegativeImbalance;

	fn total_balance(who: &AccountId) -> Self::Balance {
		NamedReservable::total_balance(who)
	}
	fn can_slash(who: &AccountId, value: Self::Balance) -> bool {
		NamedReservable::can_slash(who, value)
	}
	fn total_issuance() -> Self::Balance {
		NamedReservable::total_issuance()
	}
	fn minimum_balance() -> Self::Balance {
		NamedReservable::minimum_balance()
	}
	fn burn(amount: Self::Balance) -> Self::PositiveImbalance {
		NamedReservable::burn(amount)
	}
	fn issue(amount: Self::Balance) -> Self::NegativeImbalance {
		NamedReservable::issue(amount)
	}
	fn pair(amount: Self::Balance) -> (Self::PositiveImbalance, Self::NegativeImbalance) {
		NamedReservable::pair(amount)
	}
	fn free_balance(who: &AccountId) -> Self::Balance {
		NamedReservable::free_balance(who)
	}
	fn ensure_can_withdraw(
		who: &AccountId,
		amount: Self::Balance,
		reasons: WithdrawReasons,
		new_balance: Self::Balance,
	) -> DispatchResult {
		NamedReservable::ensure_can_withdraw(who, amount, reasons, new_balance)
	}

	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		value: Self::Balance,
		existence_requirement: ExistenceRequirement,
	) -> DispatchResult {
		NamedReservable::transfer(source, dest, value, existence_requirement)
	}
	fn slash(who: &AccountId, value: Self::Balance) -> (Self::NegativeImbalance, Self::Balance) {
		NamedReservable::slash(who, value)
	}
	fn deposit_into_existing(
		who: &AccountId,
		value: Self::Balance,
	) -> Result<Self::PositiveImbalance, DispatchError> {
		NamedReservable::deposit_into_existing(who, value)
	}
	fn resolve_into_existing(
		who: &AccountId,
		value: Self::NegativeImbalance,
	) -> Result<(), Self::NegativeImbalance> {
		NamedReservable::resolve_into_existing(who, value)
	}
	fn deposit_creating(who: &AccountId, value: Self::Balance) -> Self::PositiveImbalance {
		NamedReservable::deposit_creating(who, value)
	}
	fn resolve_creating(who: &AccountId, value: Self::NegativeImbalance) {
		NamedReservable::resolve_creating(who, value)
	}
	fn withdraw(
		who: &AccountId,
		value: Self::Balance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> Result<Self::NegativeImbalance, DispatchError> {
		NamedReservable::withdraw(who, value, reasons, liveness)
	}
	fn settle(
		who: &AccountId,
		value: Self::PositiveImbalance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> Result<(), Self::PositiveImbalance> {
		NamedReservable::settle(who, value, reasons, liveness)
	}
	fn make_free_balance_be(
		who: &AccountId,
		balance: Self::Balance,
	) -> SignedImbalance<Self::Balance, Self::PositiveImbalance> {
		NamedReservable::make_free_balance_be(who, balance)
	}
}
impl<
		NamedReservable: NamedReservableCurrency<AccountId>,
		Id: Get<NamedReservable::ReserveIdentifier>,
		AccountId,
	> ReservableCurrency<AccountId> for WithName<NamedReservable, Id, AccountId>
{
	fn can_reserve(who: &AccountId, value: Self::Balance) -> bool {
		NamedReservable::can_reserve(who, value)
	}

	fn slash_reserved(
		who: &AccountId,
		value: Self::Balance,
	) -> (Self::NegativeImbalance, Self::Balance) {
		NamedReservable::slash_reserved_named(&Id::get(), who, value)
	}

	fn reserved_balance(who: &AccountId) -> Self::Balance {
		NamedReservable::reserved_balance_named(&Id::get(), who)
	}

	fn reserve(who: &AccountId, value: Self::Balance) -> DispatchResult {
		NamedReservable::reserve_named(&Id::get(), who, value)
	}

	fn unreserve(who: &AccountId, value: Self::Balance) -> Self::Balance {
		NamedReservable::unreserve_named(&Id::get(), who, value)
	}

	fn repatriate_reserved(
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance,
		status: BalanceStatus,
	) -> Result<Self::Balance, DispatchError> {
		NamedReservable::repatriate_reserved_named(&Id::get(), slashed, beneficiary, value, status)
	}
}
