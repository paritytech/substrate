// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Balances: Handles setting and retrieval of free balance,
//! retrieving total balance, reserve and unreserve balance,
//! repatriating a reserved balance to a beneficiary account that exists,
//! transfering a balance between accounts (when not reserved),
//! slashing an account balance, account removal, rewards,
//! lookup of an index to reclaim an account (when not balance not reserved),
//! increasing total stake.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate srml_support as runtime_support;

extern crate sr_std as rstd;

#[macro_use]
extern crate parity_codec_derive;

extern crate parity_codec as codec;
extern crate sr_primitives as primitives;
extern crate srml_system as system;

#[cfg(test)]
extern crate sr_io as runtime_io;
#[cfg(test)]
extern crate substrate_primitives;

use rstd::prelude::*;
use rstd::{cmp, result};
use codec::Codec;
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;
use primitives::traits::{Zero, SimpleArithmetic, TransferAsset,
	As, StaticLookup, Member, CheckedAdd, CheckedSub};
use system::{IsDeadAccount, OnNewAccount, ensure_signed};

mod mock;
mod tests;

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

/// Determinator for whether a given account is able to transfer balance.
pub trait EnsureAccountLiquid<AccountId> {
	/// Returns `Ok` iff the account is able to transfer funds normally. `Err(...)`
	/// with the reason why not otherwise.
	fn ensure_account_liquid(who: &AccountId) -> Result;
}
impl<
	AccountId,
	X: EnsureAccountLiquid<AccountId>,
	Y: EnsureAccountLiquid<AccountId>,
> EnsureAccountLiquid<AccountId> for (X, Y) {
	fn ensure_account_liquid(who: &AccountId) -> Result {
		X::ensure_account_liquid(who)?;
		Y::ensure_account_liquid(who)
	}
}
impl<AccountId> EnsureAccountLiquid<AccountId> for () {
	fn ensure_account_liquid(_who: &AccountId) -> Result { Ok(()) }
}

pub trait Trait: system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy + As<usize> + As<u64>;

	/// A function which is invoked when the free-balance has fallen below the existential deposit and
	/// has been reduced to zero.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnFreeBalanceZero: OnFreeBalanceZero<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// A function that returns true iff a given account can transfer its funds to another account.
	type EnsureAccountLiquid: EnsureAccountLiquid<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		/// Transfer some liquid free balance to another staker.
		pub fn transfer(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: T::Balance
		) {
			let transactor = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			Self::make_transfer(&transactor, &dest, value)?;
		}

		/// Set the balances of a given account.
		fn set_balance(
			who: <T::Lookup as StaticLookup>::Source,
			#[compact] free: T::Balance,
			#[compact] reserved: T::Balance
		) {
			let who = T::Lookup::lookup(who)?;
			Self::set_free_balance(&who, free);
			Self::set_reserved_balance(&who, reserved);
		}
	}
}

decl_event!(
	pub enum Event<T> where
		<T as system::Trait>::AccountId,
		<T as Trait>::Balance
	{
		/// A new account was created.
		NewAccount(AccountId, Balance),
		/// An account was reaped.
		ReapedAccount(AccountId),
		/// Transfer succeeded (from, to, value, fees).
		Transfer(AccountId, AccountId, Balance, Balance),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Balances {
		/// The total amount of stake on the system.
		pub TotalIssuance get(total_issuance) build(|config: &GenesisConfig<T>| {
			config.balances.iter().fold(Zero::zero(), |acc: T::Balance, &(_, n)| acc + n)
		}): T::Balance;
		/// The minimum amount allowed to keep an account open.
		pub ExistentialDeposit get(existential_deposit) config(): T::Balance;
		/// The fee required to make a transfer.
		pub TransferFee get(transfer_fee) config(): T::Balance;
		/// The fee required to create an account. At least as big as ReclaimRebate.
		pub CreationFee get(creation_fee) config(): T::Balance;

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
		pub FreeBalance get(free_balance) build(|config: &GenesisConfig<T>| config.balances.clone()): map T::AccountId => T::Balance;

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
		pub ReservedBalance get(reserved_balance): map T::AccountId => T::Balance;


		// Payment stuff.

		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee) config(): T::Balance;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee) config(): T::Balance;
	}
	add_extra_genesis {
		config(balances): Vec<(T::AccountId, T::Balance)>;
	}
}

/// Outcome of a balance update.
pub enum UpdateBalanceOutcome {
	/// Account balance was simply updated.
	Updated,
	/// The update has led to killing of the account.
	AccountKilled,
}

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	/// The combined balance of `who`.
	pub fn total_balance(who: &T::AccountId) -> T::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	/// Some result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime and only the reserved balance is not taken into account.
	pub fn can_slash(who: &T::AccountId, value: T::Balance) -> bool {
		Self::free_balance(who) >= value
	}

	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	pub fn can_reserve(who: &T::AccountId, value: T::Balance) -> bool {
		if T::EnsureAccountLiquid::ensure_account_liquid(who).is_ok() {
			Self::free_balance(who) >= value
		} else {
			false
		}
	}

	//PUBLIC MUTABLES (DANGEROUS)

	/// Set the free balance of an account to some new value.
	///
	/// Will enforce ExistentialDeposit law, anulling the account as needed.
	/// In that case it will return `AccountKilled`.
	pub fn set_reserved_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		if balance < Self::existential_deposit() {
			<ReservedBalance<T>>::insert(who, balance);
			Self::on_reserved_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<ReservedBalance<T>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Set the free balance of an account to some new value. Will enforce ExistentialDeposit
	/// law anulling the account as needed.
	///
	/// Doesn't do any preparatory work for creating a new account, so should only be used when it
	/// is known that the account already exists.
	///
	/// Returns if the account was successfully updated or update has led to killing of the account.
	pub fn set_free_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		// Commented out for no - but consider it instructive.
		// assert!(!Self::total_balance(who).is_zero());
		if balance < Self::existential_deposit() {
			<FreeBalance<T>>::insert(who, balance);
			Self::on_free_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<FreeBalance<T>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Set the free balance on an account to some new value.
	///
	/// Same as [`set_free_balance`], but will create a new account.
	///
	/// Returns if the account was successfully updated or update has led to killing of the account.
	///
	/// [`set_free_balance`]: #method.set_free_balance
	pub fn set_free_balance_creating(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		let ed = <Module<T>>::existential_deposit();
		// If the balance is too low, then the account is reaped.
		// NOTE: There are two balances for every account: `reserved_balance` and
		// `free_balance`. This contract subsystem only cares about the latter: whenever
		// the term "balance" is used *here* it should be assumed to mean "free balance"
		// in the rest of the module.
		// Free balance can never be less than ED. If that happens, it gets reduced to zero
		// and the account information relevant to this subsystem is deleted (i.e. the
		// account is reaped).
		// NOTE: This is orthogonal to the `Bondage` value that an account has, a high
		// value of which makes even the `free_balance` unspendable.
		if balance < ed {
			Self::set_free_balance(who, balance);
			UpdateBalanceOutcome::AccountKilled
		} else {
			if !<FreeBalance<T>>::exists(who) {
				Self::new_account(&who, balance);
			}
			Self::set_free_balance(who, balance);

			UpdateBalanceOutcome::Updated
		}
	}

	/// Adds up to `value` to the free balance of `who`. If `who` doesn't exist, it is created.
	///
	/// This is a sensitive function since it circumvents any fees associated with account
	/// setup. Ensure it is only called by trusted code.
	///
	/// NOTE: This assumes that the total stake remains unchanged after this operation. If
	/// you mean to actually mint value into existence, then use `reward` instead.
	pub fn increase_free_balance_creating(who: &T::AccountId, value: T::Balance) -> UpdateBalanceOutcome {
		Self::set_free_balance_creating(who, Self::free_balance(who) + value)
	}

	/// Substrates `value` from the free balance of `who`. If the whole amount cannot be
	/// deducted, an error is returned.
	///
	/// NOTE: This assumes that the total stake remains unchanged after this operation. If
	/// you mean to actually burn value out of existence, then use `slash` instead.
	pub fn decrease_free_balance(
		who: &T::AccountId,
		value: T::Balance
	) -> result::Result<UpdateBalanceOutcome, &'static str> {
		T::EnsureAccountLiquid::ensure_account_liquid(who)?;
		let b = Self::free_balance(who);
		if b < value {
			return Err("account has too few funds")
		}
		Ok(Self::set_free_balance(who, b - value))
	}

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	pub fn slash(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		Self::set_free_balance(who, free_balance - free_slash);
		Self::decrease_total_stake_by(free_slash);
		if free_slash < value {
			Self::slash_reserved(who, value - free_slash)
		} else {
			None
		}
	}

	/// Adds up to `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an Err returned.
	pub fn reward(who: &T::AccountId, value: T::Balance) -> Result {
		if Self::total_balance(who).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		Self::set_free_balance(who, Self::free_balance(who) + value);
		Self::increase_total_stake_by(value);
		Ok(())
	}

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behaviour to `unreserve`.
	pub fn reserve(who: &T::AccountId, value: T::Balance) -> Result {
		let b = Self::free_balance(who);
		if b < value {
			return Err("not enough free funds")
		}
		T::EnsureAccountLiquid::ensure_account_liquid(who)?;
		Self::set_reserved_balance(who, Self::reserved_balance(who) + value);
		Self::set_free_balance(who, b - value);
		Ok(())
	}

	/// Moves up to `value` from reserved balance to balance. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	/// NOTE: This is different to `reserve`.
	pub fn unreserve(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let b = Self::reserved_balance(who);
		let actual = cmp::min(b, value);
		Self::set_free_balance(who, Self::free_balance(who) + actual);
		Self::set_reserved_balance(who, b - actual);
		if actual == value {
			None
		} else {
			Some(value - actual)
		}
	}

	/// Transfer some liquid free balance to another staker.
	pub fn make_transfer(transactor: &T::AccountId, dest: &T::AccountId, value: T::Balance) -> Result {
		let from_balance = Self::free_balance(transactor);
		let to_balance = Self::free_balance(dest);
		let would_create = to_balance.is_zero();
		let fee = if would_create { Self::creation_fee() } else { Self::transfer_fee() };
		let liability = match value.checked_add(&fee) {
			Some(l) => l,
			None => return Err("got overflow after adding a fee to value"),
		};

		let new_from_balance = match from_balance.checked_sub(&liability) {
			Some(b) => b,
			None => return Err("balance too low to send value"),
		};
		if would_create && value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		T::EnsureAccountLiquid::ensure_account_liquid(transactor)?;

		// NOTE: total stake being stored in the same type means that this could never overflow
		// but better to be safe than sorry.
		let new_to_balance = match to_balance.checked_add(&value) {
			Some(b) => b,
			None => return Err("destination balance too high to receive value"),
		};

		if transactor != dest {
			Self::set_free_balance(transactor, new_from_balance);
			Self::decrease_total_stake_by(fee);
			Self::set_free_balance_creating(dest, new_to_balance);
			Self::deposit_event(RawEvent::Transfer(transactor.clone(), dest.clone(), value, fee));
		}

		Ok(())
	}

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Some(remaining)` will be returned. Full completion is given by `None`.
	pub fn slash_reserved(who: &T::AccountId, value: T::Balance) -> Option<T::Balance> {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		Self::set_reserved_balance(who, b - slash);
		Self::decrease_total_stake_by(slash);
		if value == slash {
			None
		} else {
			Some(value - slash)
		}
	}

	/// Moves up to `value` from reserved balance of account `slashed` to free balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned.
	///
	/// As much funds up to `value` will be moved as possible. If this is less than `value`, then
	/// `Ok(Some(remaining))` will be returned. Full completion is given by `Ok(None)`.
	pub fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: T::Balance
	) -> result::Result<Option<T::Balance>, &'static str> {
		if Self::total_balance(beneficiary).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		let b = Self::reserved_balance(slashed);
		let slash = cmp::min(b, value);
		Self::set_free_balance(beneficiary, Self::free_balance(beneficiary) + slash);
		Self::set_reserved_balance(slashed, b - slash);
		if value == slash {
			Ok(None)
		} else {
			Ok(Some(value - slash))
		}
	}

	/// Register a new account (with existential balance).
	fn new_account(who: &T::AccountId, balance: T::Balance) {
		T::OnNewAccount::on_new_account(&who);
		Self::deposit_event(RawEvent::NewAccount(who.clone(), balance.clone()));
	}

	fn reap_account(who: &T::AccountId) {
		<system::AccountNonce<T>>::remove(who);
		Self::deposit_event(RawEvent::ReapedAccount(who.clone()));
	}

	/// Kill an account's free portion.
	fn on_free_too_low(who: &T::AccountId) {
		Self::decrease_total_stake_by(Self::free_balance(who));
		<FreeBalance<T>>::remove(who);

		T::OnFreeBalanceZero::on_free_balance_zero(who);

		if Self::reserved_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}

	/// Kill an account's reserved portion.
	fn on_reserved_too_low(who: &T::AccountId) {
		Self::decrease_total_stake_by(Self::reserved_balance(who));
		<ReservedBalance<T>>::remove(who);

		if Self::free_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}

	/// Increase TotalIssuance by Value.
	pub fn increase_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T>>::total_issuance().checked_add(&value) {
			<TotalIssuance<T>>::put(v);
		}
	}
	/// Decrease TotalIssuance by Value.
	pub fn decrease_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T>>::total_issuance().checked_sub(&value) {
			<TotalIssuance<T>>::put(v);
		}
	}
}

impl<T: Trait> TransferAsset<T::AccountId> for Module<T> {
	type Amount = T::Balance;

	fn transfer(from: &T::AccountId, to: &T::AccountId, amount: T::Balance) -> Result {
		Self::make_transfer(from, to, amount)
	}

	fn remove_from(who: &T::AccountId, value: T::Balance) -> Result {
		T::EnsureAccountLiquid::ensure_account_liquid(who)?;
		let b = Self::free_balance(who);
		ensure!(b >= value, "account has too few funds");
		Self::set_free_balance(who, b - value);
		Self::decrease_total_stake_by(value);
		Ok(())
	}

	fn add_to(who: &T::AccountId, value: T::Balance) -> Result {
		Self::set_free_balance_creating(who, Self::free_balance(who) + value);
		Self::increase_total_stake_by(value);
		Ok(())
	}
}

impl<T: Trait> IsDeadAccount<T::AccountId> for Module<T> {
	fn is_dead_account(who: &T::AccountId) -> bool {
		Self::total_balance(who).is_zero()
	}
}
