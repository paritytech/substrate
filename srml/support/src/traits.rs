// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Traits for SRML

use crate::rstd::result;
use crate::codec::{Codec, Encode, Decode};
use crate::runtime_primitives::traits::{
	MaybeSerializeDebug, SimpleArithmetic, As
};

/// The account with the given id was killed.
pub trait OnFreeBalanceZero<AccountId> {
	/// The account was the given id was killed.
	fn on_free_balance_zero(who: &AccountId);
}

impl<AccountId> OnFreeBalanceZero<AccountId> for () {
	fn on_free_balance_zero(_who: &AccountId) {}
}
impl<
	AccountId,
	X: OnFreeBalanceZero<AccountId>,
	Y: OnFreeBalanceZero<AccountId>,
> OnFreeBalanceZero<AccountId> for (X, Y) {
	fn on_free_balance_zero(who: &AccountId) {
		X::on_free_balance_zero(who);
		Y::on_free_balance_zero(who);
	}
}

/// Trait for a hook to get called when some balance has been minted, causing dilution.
pub trait OnDilution<Balance> {
	/// Some `portion` of the total balance just "grew" by `minted`. `portion` is the pre-growth
	/// amount (it doesn't take account of the recent growth).
	fn on_dilution(minted: Balance, portion: Balance);
}

impl<Balance> OnDilution<Balance> for () {
	fn on_dilution(_minted: Balance, _portion: Balance) {}
}

/// Outcome of a balance update.
pub enum UpdateBalanceOutcome {
	/// Account balance was simply updated.
	Updated,
	/// The update has led to killing of the account.
	AccountKilled,
}

pub trait ArithmeticType {
	type Type: SimpleArithmetic + As<usize> + As<u64> + Codec + Copy + MaybeSerializeDebug + Default;
}

/// Abstraction over a fungible assets system.
pub trait Currency<AccountId> {
	/// The balance of an account.
	type Balance;

	// PUBLIC IMMUTABLES

	/// The combined balance of `who`.
	fn total_balance(who: &AccountId) -> Self::Balance;

	/// Some result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime and only the reserved balance is not taken into account.
	fn can_slash(who: &AccountId, value: Self::Balance) -> bool;

	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	fn can_reserve(who: &AccountId, value: Self::Balance) -> bool;

	/// The total amount of stake on the system.
	fn total_issuance() -> Self::Balance;

	/// The minimum balance any single account may have. This is equivalent to Balances module's
	/// Existential Deposit.
	fn minimum_balance() -> Self::Balance;

	/// The 'free' balance of a given account.
	///
	/// This is the only balance that matters in terms of most operations on tokens. It is
	/// alone used to determine the balance when in the contract execution environment. When this
	/// balance falls below the value of `ExistentialDeposit`, then the 'current account' is
	/// deleted: specifically `FreeBalance`. Furthermore, `OnFreeBalanceZero` callback
	/// is invoked, giving a chance to external modules to cleanup data associated with
	/// the deleted account.
	///
	/// `system::AccountNonce` is also deleted if `ReservedBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn free_balance(who: &AccountId) -> Self::Balance;

	/// The amount of the balance of a given account that is externally reserved; this can still get
	/// slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable. (This is different
	/// and wholly unrelated to the `Bondage` system used in the staking module.)
	///
	/// When this balance falls below the value of `ExistentialDeposit`, then this 'reserve account'
	/// is deleted: specifically, `ReservedBalance`.
	///
	/// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn reserved_balance(who: &AccountId) -> Self::Balance;

	// PUBLIC MUTABLES (DANGEROUS)

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	fn slash(who: &AccountId, value: Self::Balance) -> Option<Self::Balance>;

	/// Adds up to `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an Err returned.
	fn reward(who: &AccountId, value: Self::Balance) -> result::Result<(), &'static str>;

	/// Adds up to `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, it is created
	///
	/// Returns if the account was successfully updated or update has led to killing of the account.
	///
	/// NOTE: This assumes that the total stake remains unchanged after this operation.
	fn increase_free_balance_creating(who: &AccountId, value: Self::Balance) -> UpdateBalanceOutcome;

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behaviour to `unreserve`.
	fn reserve(who: &AccountId, value: Self::Balance) -> result::Result<(), &'static str>;

	/// Moves up to `value` from reserved balance to balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	/// NOTE: This is different to `reserve`.
	fn unreserve(who: &AccountId, value: Self::Balance) -> Option<Self::Balance>;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	fn slash_reserved(who: &AccountId, value: Self::Balance) -> Option<Self::Balance>;

	/// Moves up to `value` from reserved balance of account `slashed` to free balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned.
	///
	/// As much funds up to `value` will be moved as possible. If this is less than `value`, then
	/// `Ok(Some(remaining))` will be returned. Full completion is given by `Ok(None)`.
	fn repatriate_reserved(
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance
	) -> result::Result<Option<Self::Balance>, &'static str>;
}

/// An identifier for a lock. Used for disambiguating different locks so that
/// they can be individually replaced or removed.
pub type LockIdentifier = [u8; 8];

/// A currency whose accounts can have liquidity restrictions.
pub trait LockableCurrency<AccountId>: Currency<AccountId> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// Introduce a new lock or change an existing one.
	fn set_lock(
		id: LockIdentifier,
		who: &AccountId,
		amount: Self::Balance,
		until: Self::Moment,
		reasons: WithdrawReasons,
	);

	/// Change any existing lock so that it becomes strictly less liquid in all
	/// respects to the given parameters.
	fn extend_lock(
		id: LockIdentifier,
		who: &AccountId,
		amount: Self::Balance,
		until: Self::Moment,
		reasons: WithdrawReasons,
	);

	/// Remove an existing lock.
	fn remove_lock(
		id: LockIdentifier,
		who: &AccountId,
	);
}

/// Charge bytes fee trait
pub trait ChargeBytesFee<AccountId> {
	/// Charge fees from `transactor` for an extrinsic (transaction) of encoded length
	/// `encoded_len` bytes. Return Ok if the payment was successful.
	fn charge_base_bytes_fee(transactor: &AccountId, encoded_len: usize) -> Result<(), &'static str>;
}

/// Charge fee trait
pub trait ChargeFee<AccountId>: ChargeBytesFee<AccountId> {
	/// The type of fee amount.
	type Amount;

	/// Charge `amount` of fees from `transactor`. Return Ok iff the payment was successful.
	fn charge_fee(transactor: &AccountId, amount: Self::Amount) -> Result<(), &'static str>;

	/// Refund `amount` of previous charged fees from `transactor`. Return Ok if the refund was successful.
	fn refund_fee(transactor: &AccountId, amount: Self::Amount) -> Result<(), &'static str>;
}

bitmask! {
	/// Reasons for moving funds out of an account.
	#[derive(Encode, Decode)]
	pub mask WithdrawReasons: i8 where

	/// Reason for moving funds out of an account.
	#[derive(Encode, Decode)]
	flags WithdrawReason {
		/// In order to pay for (system) transaction costs.
		TransactionPayment = 0b00000001,
		/// In order to transfer ownership.
		Transfer = 0b00000010,
		/// In order to reserve some funds for a later return or repatriation
		Reserve = 0b00000100,
	}
}

/// Transfer fungible asset trait
pub trait TransferAsset<AccountId> {
	/// The type of asset amount.
	type Amount;

	/// Transfer asset from `from` account to `to` account with `amount` of asset.
	fn transfer(from: &AccountId, to: &AccountId, amount: Self::Amount) -> Result<(), &'static str>;

	/// Remove asset from `who` account by deducting `amount` in the account balances.
	fn withdraw(who: &AccountId, amount: Self::Amount, reason: WithdrawReason) -> Result<(), &'static str>;

	/// Add asset to `who` account by increasing `amount` in the account balances.
	fn deposit(who: &AccountId, amount: Self::Amount) -> Result<(), &'static str>;
}

impl<T> ChargeBytesFee<T> for () {
	fn charge_base_bytes_fee(_: &T, _: usize) -> Result<(), &'static str> { Ok(()) }
}

impl<T> ChargeFee<T> for () {
	type Amount = ();

	fn charge_fee(_: &T, _: Self::Amount) -> Result<(), &'static str> { Ok(()) }
	fn refund_fee(_: &T, _: Self::Amount) -> Result<(), &'static str> { Ok(()) }
}

impl<T> TransferAsset<T> for () {
	type Amount = ();

	fn transfer(_: &T, _: &T, _: Self::Amount) -> Result<(), &'static str> { Ok(()) }
	fn withdraw(_: &T, _: Self::Amount, _: WithdrawReason) -> Result<(), &'static str> { Ok(()) }
	fn deposit(_: &T, _: Self::Amount) -> Result<(), &'static str> { Ok(()) }
}
