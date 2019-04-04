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
	MaybeSerializeDebug, SimpleArithmetic
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
	/// The update led to killing the account.
	AccountKilled,
}

/// Simple trait designed for hooking into a transaction payment.
///
/// It operates over a single generic `AccountId` type.
pub trait MakePayment<AccountId> {
	/// Make transaction payment from `who` for an extrinsic of encoded length
	/// `encoded_len` bytes. Return `Ok` iff the payment was successful.
	fn make_payment(who: &AccountId, encoded_len: usize) -> Result<(), &'static str>;
}

impl<T> MakePayment<T> for () {
	fn make_payment(_: &T, _: usize) -> Result<(), &'static str> { Ok(()) }
}

/// Handler for when some currency "account" decreased in balance for
/// some reason.
///
/// The only reason at present for an increase would be for validator rewards, but
/// there may be other reasons in the future or for other chains.
///
/// Reasons for decreases include:
///
/// - Someone got slashed.
/// - Someone paid for a transaction to be included.
pub trait OnUnbalanced<Imbalance> {
	/// Handler for some imbalance. Infallible.
	fn on_unbalanced(amount: Imbalance);
}

impl<Imbalance: Drop> OnUnbalanced<Imbalance> for () {
	fn on_unbalanced(amount: Imbalance) { drop(amount); }
}

/// Simple boolean for whether an account needs to be kept in existence.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ExistenceRequirement {
	/// Operation must not result in the account going out of existence.
	KeepAlive,
	/// Operation may result in account going out of existence.
	AllowDeath,
}

/// A trait for a not-quite Linear Type that tracks an imbalance.
///
/// Functions that alter account balances return an object of this trait to
/// express how much account balances have been altered in aggregate. If
/// dropped, the currency system will take some default steps to deal with
/// the imbalance (`balances` module simply reduces or increases its
/// total issuance). Your module should generally handle it in some way,
/// good practice is to do so in a configurable manner using an
/// `OnUnbalanced` type for each situation in which your module needs to
/// handle an imbalance.
///
/// Imbalances can either be Positive (funds were added somewhere without
/// being subtracted elsewhere - e.g. a reward) or Negative (funds deducted
/// somewhere without an equal and opposite addition - e.g. a slash or
/// system fee payment).
///
/// Since they are unsigned, the actual type is always Positive or Negative.
/// The trait makes no distinction except to define the `Opposite` type.
///
/// New instances of zero value can be created (`zero`) and destroyed
/// (`drop_zero`).
///
/// Existing instances can be `split` and merged either consuming `self` with
/// `merge` or mutating `self` with `subsume`. If the target is an `Option`,
/// then `maybe_merge` and `maybe_subsume` might work better. Instances can
/// also be `offset` with an `Opposite` that is less than or equal to in value.
///
/// You can always retrieve the raw balance value using `peek`.
#[must_use]
pub trait Imbalance<Balance>: Sized {
	/// The oppositely imbalanced type. They come in pairs.
	type Opposite: Imbalance<Balance>;

	/// The zero imbalance. Can be destroyed with `drop_zero`.
	fn zero() -> Self;

	/// Drop an instance cleanly. Only works if its `value()` is zero.
	fn drop_zero(self) -> Result<(), Self>;

	/// Consume `self` and return two independent instances; the first
	/// is guaranteed to be at most `amount` and the second will be the remainder.
	fn split(self, amount: Balance) -> (Self, Self);

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	fn merge(self, other: Self) -> Self;

	/// Consume `self` and maybe an `other` to return a new instance that combines
	/// both.
	fn maybe_merge(self, other: Option<Self>) -> Self {
		if let Some(o) = other {
			self.merge(o)
		} else {
			self
		}
	}

	/// Consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn subsume(&mut self, other: Self);

	/// Maybe consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn maybe_subsume(&mut self, other: Option<Self>) {
		if let Some(o) = other {
			self.subsume(o)
		}
	}

	/// Consume self and along with an opposite counterpart to return
	/// a combined result.
	///
	/// Returns `Ok` along with a new instance of `Self` if this instance has a
	/// greater value than the `other`. Otherwise returns `Err` with an instance of
	/// the `Opposite`. In both cases the value represents the combination of `self`
	/// and `other`.
	fn offset(self, other: Self::Opposite) -> Result<Self, Self::Opposite>;

	/// The raw value of self.
	fn peek(&self) -> Balance;
}

/// Either a positive or a negative imbalance.
pub enum SignedImbalance<B, P: Imbalance<B>>{
	/// A positive imbalance (funds have been created but none destroyed).
	Positive(P),
	/// A negative imbalance (funds have been destroyed but none created).
	Negative(P::Opposite),
}

impl<
	P: Imbalance<B, Opposite=N>,
	N: Imbalance<B, Opposite=P>,
	B: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default,
> SignedImbalance<B, P> {
	pub fn zero() -> Self {
		SignedImbalance::Positive(P::zero())
	}

	pub fn drop_zero(self) -> Result<(), Self> {
		match self {
			SignedImbalance::Positive(x) => x.drop_zero().map_err(SignedImbalance::Positive),
			SignedImbalance::Negative(x) => x.drop_zero().map_err(SignedImbalance::Negative),
		}
	}

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	pub fn merge(self, other: Self) -> Self {
		match (self, other) {
			(SignedImbalance::Positive(one), SignedImbalance::Positive(other)) =>
				SignedImbalance::Positive(one.merge(other)),
			(SignedImbalance::Negative(one), SignedImbalance::Negative(other)) =>
				SignedImbalance::Negative(one.merge(other)),
			(SignedImbalance::Positive(one), SignedImbalance::Negative(other)) =>
				if one.peek() > other.peek() {
					SignedImbalance::Positive(one.offset(other).ok().unwrap_or_else(P::zero))
				} else {
					SignedImbalance::Negative(other.offset(one).ok().unwrap_or_else(N::zero))
				},
			(one, other) => other.merge(one),
		}
	}
}

/// Abstraction over a fungible assets system.
pub trait Currency<AccountId> {
	/// The balance of an account.
	type Balance: SimpleArithmetic + Codec + Copy + MaybeSerializeDebug + Default;

	/// The opaque token type for an imbalance. This is returned by unbalanced operations
	/// and must be dealt with. It may be dropped but cannot be cloned.
	type PositiveImbalance: Imbalance<Self::Balance, Opposite=Self::NegativeImbalance>;

	/// The opaque token type for an imbalance. This is returned by unbalanced operations
	/// and must be dealt with. It may be dropped but cannot be cloned.
	type NegativeImbalance: Imbalance<Self::Balance, Opposite=Self::PositiveImbalance>;

	// PUBLIC IMMUTABLES

	/// The combined balance of `who`.
	fn total_balance(who: &AccountId) -> Self::Balance;

	/// Same result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime and only the reserved balance is not taken into account.
	fn can_slash(who: &AccountId, value: Self::Balance) -> bool;

	/// The total amount of issuance in the system.
	fn total_issuance() -> Self::Balance;

	/// The minimum balance any single account may have. This is equivalent to the `Balances` module's
	/// `ExistentialDeposit`.
	fn minimum_balance() -> Self::Balance;

	/// The 'free' balance of a given account.
	///
	/// This is the only balance that matters in terms of most operations on tokens. It alone
	/// is used to determine the balance when in the contract execution environment. When this
	/// balance falls below the value of `ExistentialDeposit`, then the 'current account' is
	/// deleted: specifically `FreeBalance`. Further, the `OnFreeBalanceZero` callback
	/// is invoked, giving a chance to external modules to clean up data associated with
	/// the deleted account.
	///
	/// `system::AccountNonce` is also deleted if `ReservedBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn free_balance(who: &AccountId) -> Self::Balance;

	/// Returns `Ok` iff the account is able to make a withdrawal of the given amount
	/// for the given reason. Basically, it's just a dry-run of `withdraw`.
	///
	/// `Err(...)` with the reason why not otherwise.
	fn ensure_can_withdraw(
		who: &AccountId,
		_amount: Self::Balance,
		reason: WithdrawReason,
		new_balance: Self::Balance,
	) -> result::Result<(), &'static str>;

	// PUBLIC MUTABLES (DANGEROUS)

	/// Transfer some liquid free balance to another staker.
	///
	/// This is a very high-level function. It will ensure all appropriate fees are paid
	/// and no imbalance in the system remains.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		value: Self::Balance,
	) -> result::Result<(), &'static str>;

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then a non-zero second item will be returned.
	fn slash(
		who: &AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance);

	/// Mints `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an Err returned.
	fn deposit_into_existing(
		who: &AccountId,
		value: Self::Balance
	) -> result::Result<Self::PositiveImbalance, &'static str>;

	/// Removes some free balance from `who` account for `reason` if possible. If `liveness` is `KeepAlive`,
	/// then no less than `ExistentialDeposit` must be left remaining.
	///
	/// This checks any locks, vesting, and liquidity requirements. If the removal is not possible, then it
	/// returns `Err`.
	fn withdraw(
		who: &AccountId,
		value: Self::Balance,
		reason: WithdrawReason,
		liveness: ExistenceRequirement,
	) -> result::Result<Self::NegativeImbalance, &'static str>;

	/// Adds up to `value` to the free balance of `who`. If `who` doesn't exist, it is created.
	///
	/// Infallible.
	fn deposit_creating(
		who: &AccountId,
		value: Self::Balance,
	) -> Self::PositiveImbalance;

	/// Ensure an account's free balance equals some value; this will create the account
	/// if needed.
	///
	/// Returns a signed imbalance and status to indicate if the account was successfully updated or update
	/// has led to killing of the account.
	fn make_free_balance_be(
		who: &AccountId,
		balance: Self::Balance,
	) -> (
		SignedImbalance<Self::Balance, Self::PositiveImbalance>,
		UpdateBalanceOutcome,
	);
}

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
	fn reserve(who: &AccountId, value: Self::Balance) -> result::Result<(), &'static str>;

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

	/// Moves up to `value` from reserved balance of account `slashed` to free balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Ok(non_zero)` will be returned.
	fn repatriate_reserved(
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance
	) -> result::Result<Self::Balance, &'static str>;
}

/// An identifier for a lock. Used for disambiguating different locks so that
/// they can be individually replaced or removed.
pub type LockIdentifier = [u8; 8];

/// A currency whose accounts can have liquidity restrictions.
pub trait LockableCurrency<AccountId>: Currency<AccountId> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// Create a new balance lock on account `who`.
	///
	/// If the new lock is valid (i.e. not already expired), it will push the struct to
	/// the `Locks` vec in storage. Note that you can lock more funds than a user has.
	///
	/// If the lock `id` already exists, this will update it.
	fn set_lock(
		id: LockIdentifier,
		who: &AccountId,
		amount: Self::Balance,
		until: Self::Moment,
		reasons: WithdrawReasons,
	);

	/// Changes a balance lock (selected by `id`) so that it becomes less liquid in all
	/// parameters or creates a new one if it does not exist.
	///
	/// Calling `extend_lock` on an existing lock `id` differs from `set_lock` in that it
	/// applies the most severe constraints of the two, while `set_lock` replaces the lock
	/// with the new parameters. As in, `extend_lock` will set:
	/// - maximum `amount`
	/// - farthest duration (`until`)
	/// - bitwise mask of all `reasons`
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
		/// In order to pay some other (higher-level) fees.
		Fee = 0b00001000,
	}
}

