// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use rstd::prelude::*;
use rstd::{cmp, result};
use parity_codec::{Codec, Encode, Decode};
use srml_support::{StorageValue, StorageMap, Parameter, decl_event, decl_storage, decl_module, ensure};
use srml_support::traits::{
	UpdateBalanceOutcome, Currency, OnFreeBalanceZero, TransferAsset,
	WithdrawReason, WithdrawReasons, ArithmeticType, LockIdentifier, LockableCurrency
};
use srml_support::dispatch::Result;
use primitives::traits::{
	Zero, SimpleArithmetic, As, StaticLookup, Member, CheckedAdd, CheckedSub, MaybeSerializeDebug
};
use system::{IsDeadAccount, OnNewAccount, ensure_signed};

mod mock;
mod tests;

pub trait Trait<I: Instance = DefaultInstance>: system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy + As<usize> + As<u64> + MaybeSerializeDebug;

	/// A function which is invoked when the free-balance has fallen below the existential deposit and
	/// has been reduced to zero.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnFreeBalanceZero: OnFreeBalanceZero<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;
}

impl<T: Trait> ArithmeticType for Module<T> {
	type Type = <T as Trait>::Balance;
}

decl_event!(
	pub enum Event<T, I: Instance = DefaultInstance> where
		<T as system::Trait>::AccountId,
		<T as Trait<I>>::Balance
	{
		/// A new account was created.
		NewAccount(AccountId, Balance),
		/// An account was reaped.
		ReapedAccount(AccountId),
		/// Transfer succeeded (from, to, value, fees).
		Transfer(AccountId, AccountId, Balance, Balance),
	}
);

/// Struct to encode the vesting schedule of an individual account.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct VestingSchedule<Balance> {
	/// Locked amount at genesis.
	pub offset: Balance,
	/// Amount that gets unlocked every block from genesis.
	pub per_block: Balance,
}

impl<Balance: SimpleArithmetic + Copy + As<u64>> VestingSchedule<Balance> {
	/// Amount locked at block `n`.
	pub fn locked_at<BlockNumber: As<u64>>(&self, n: BlockNumber) -> Balance {
		if let Some(x) = Balance::sa(n.as_()).checked_mul(&self.per_block) {
			self.offset.max(x) - x
		} else {
			Zero::zero()
		}
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct BalanceLock<Balance, BlockNumber> {
	pub id: LockIdentifier,
	pub amount: Balance,
	pub until: BlockNumber,
	pub reasons: WithdrawReasons,
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Balances {
		/// The total amount of stake on the system.
		pub TotalIssuance get(total_issuance) build(|config: &GenesisConfig<T, I>| {
			config.balances.iter().fold(Zero::zero(), |acc: T::Balance, &(_, n)| acc + n)
		}): T::Balance;
		/// The minimum amount allowed to keep an account open.
		pub ExistentialDeposit get(existential_deposit) config(): T::Balance;
		/// The fee required to make a transfer.
		pub TransferFee get(transfer_fee) config(): T::Balance;
		/// The fee required to create an account. At least as big as ReclaimRebate.
		pub CreationFee get(creation_fee) config(): T::Balance;

		/// Information regarding the vesting of a given account.
		pub Vesting get(vesting) build(|config: &GenesisConfig<T, I>| {
			config.vesting.iter().filter_map(|&(ref who, begin, length)| {
				let begin: u64 = begin.as_();
				let length: u64 = length.as_();
				let begin: T::Balance = As::sa(begin);
				let length: T::Balance = As::sa(length);

				config.balances.iter()
					.find(|&&(ref w, _)| w == who)
					.map(|&(_, balance)| {
						// <= begin it should be >= balance
						// >= begin+length it should be <= 0

						let per_block = balance / length;
						let offset = begin * per_block + balance;

						(who.clone(), VestingSchedule { offset, per_block })
					})
			}).collect::<Vec<_>>()
		}): map T::AccountId => Option<VestingSchedule<T::Balance>>;

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
		pub FreeBalance get(free_balance) build(|config: &GenesisConfig<T, I>| config.balances.clone()): map T::AccountId => T::Balance;

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

		/// Any liquidity locks on some account balances.
		pub Locks get(locks): map T::AccountId => Vec<BalanceLock<T::Balance, T::BlockNumber>>;
	}
	add_extra_genesis {
		config(balances): Vec<(T::AccountId, T::Balance)>;
		config(vesting): Vec<(T::AccountId, T::BlockNumber, T::BlockNumber)>;		// begin, length
	}
	extra_genesis_skip_phantom_data_field;
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance = DefaultInstance> for enum Call where origin: T::Origin {
		fn deposit_event<T, I>() = default;

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

// For funding methods, see Currency trait
impl<T: Trait<I>, I: Instance> Module<T, I> {

	/// Get the amount that is currently being vested and cannot be transfered out of this account.
	pub fn vesting_balance(who: &T::AccountId) -> T::Balance {
		if let Some(v) = Self::vesting(who) {
			Self::free_balance(who).min(v.locked_at(<system::Module<T>>::block_number()))
		} else {
			Zero::zero()
		}
	}

	/// Set the free balance of an account to some new value.
	///
	/// Will enforce ExistentialDeposit law, anulling the account as needed.
	/// In that case it will return `AccountKilled`.
	pub fn set_reserved_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		if balance < Self::existential_deposit() {
			<ReservedBalance<T, I>>::insert(who, balance);
			Self::on_reserved_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<ReservedBalance<T, I>>::insert(who, balance);
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
			<FreeBalance<T, I>>::insert(who, balance);
			Self::on_free_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<FreeBalance<T, I>>::insert(who, balance);
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
		let ed = <Module<T, I>>::existential_deposit();
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
			if !<FreeBalance<T, I>>::exists(who) {
				Self::new_account(&who, balance);
			}
			Self::set_free_balance(who, balance);

			UpdateBalanceOutcome::Updated
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
			None => return Err("balance too low to send value"),
			Some(b) => b,
		};
		if would_create && value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		Self::ensure_account_can_withdraw(transactor, value, WithdrawReason::Transfer, new_from_balance)?;

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
		<FreeBalance<T, I>>::remove(who);
		<Locks<T, I>>::remove(who);

		T::OnFreeBalanceZero::on_free_balance_zero(who);

		if Self::reserved_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}

	/// Kill an account's reserved portion.
	fn on_reserved_too_low(who: &T::AccountId) {
		Self::decrease_total_stake_by(Self::reserved_balance(who));
		<ReservedBalance<T, I>>::remove(who);

		if Self::free_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}

	/// Increase TotalIssuance by Value.
	pub fn increase_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T, I>>::total_issuance().checked_add(&value) {
			<TotalIssuance<T, I>>::put(v);
		}
	}
	/// Decrease TotalIssuance by Value.
	pub fn decrease_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T, I>>::total_issuance().checked_sub(&value) {
			<TotalIssuance<T, I>>::put(v);
		}
	}

	/// Returns `Ok` iff the account is able to make a withdrawal of the given amount
	/// for the given reason.
	/// 
	/// `Err(...)` with the reason why not otherwise.
	pub fn ensure_account_can_withdraw(
		who: &T::AccountId,
		_amount: T::Balance,
		reason: WithdrawReason,
		new_balance: T::Balance,
	) -> Result {
		match reason {
			WithdrawReason::Reserve | WithdrawReason::Transfer if Self::vesting_balance(who) > new_balance =>
				return Err("vesting balance too high to send value"),
			_ => {}
		}
		let locks = Self::locks(who);
		if locks.is_empty() {
			return Ok(())
		}
		let now = <system::Module<T>>::block_number();
		if Self::locks(who).into_iter()
			.all(|l| now >= l.until || new_balance >= l.amount || !l.reasons.contains(reason))
		{
			Ok(())
		} else {
			Err("account liquidity restrictions prevent withdrawal")
		}
	}
}

impl<T: Trait<I>, I: Instance> Currency<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDebug
{
	type Balance = T::Balance;

	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		Self::free_balance(who) >= value
	}

	fn can_reserve(who: &T::AccountId, value: Self::Balance) -> bool {
		Self::free_balance(who)
			.checked_sub(&value)
			.map_or(false, |new_balance|
				Self::ensure_account_can_withdraw(who, value, WithdrawReason::Reserve, new_balance).is_ok()
			)
	}

	fn total_issuance() -> Self::Balance {
		<TotalIssuance<T, I>>::get()
	}

	fn minimum_balance() -> Self::Balance {
		Self::existential_deposit()
	}

	fn free_balance(who: &T::AccountId) -> Self::Balance {
		<FreeBalance<T, I>>::get(who)
	}

	fn reserved_balance(who: &T::AccountId) -> Self::Balance {
		<ReservedBalance<T, I>>::get(who)
	}

	fn slash(who: &T::AccountId, value: Self::Balance) -> Option<Self::Balance> {
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

	fn reward(who: &T::AccountId, value: Self::Balance) -> result::Result<(), &'static str> {
		if Self::total_balance(who).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		Self::set_free_balance(who, Self::free_balance(who) + value);
		Self::increase_total_stake_by(value);
		Ok(())
	}

	fn increase_free_balance_creating(who: &T::AccountId, value: Self::Balance) -> UpdateBalanceOutcome {
		Self::set_free_balance_creating(who, Self::free_balance(who) + value)
	}

	fn reserve(who: &T::AccountId, value: Self::Balance) -> result::Result<(), &'static str> {
		let b = Self::free_balance(who);
		if b < value {
			return Err("not enough free funds")
		}
		let new_balance = b - value;
		Self::ensure_account_can_withdraw(who, value, WithdrawReason::Reserve, new_balance)?;
		Self::set_reserved_balance(who, Self::reserved_balance(who) + value);
		Self::set_free_balance(who, new_balance);
		Ok(())
	}

	fn unreserve(who: &T::AccountId, value: Self::Balance) -> Option<Self::Balance> {
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

	fn slash_reserved(who: &T::AccountId, value: Self::Balance) -> Option<Self::Balance> {
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

	fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance
	) -> result::Result<Option<Self::Balance>, &'static str> {
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
}

impl<T: Trait<I>, I: Instance> LockableCurrency<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDebug
{
	type Moment = T::BlockNumber;

	fn set_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		let now = <system::Module<T>>::block_number();
		let mut new_lock = Some(BalanceLock { id, amount, until, reasons });
		let mut locks = Self::locks(who).into_iter().filter_map(|l|
			if l.id == id {
				new_lock.take()
			} else if l.until > now {
				Some(l)
			} else {
				None
			}).collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		<Locks<T, I>>::insert(who, locks);
	}

	fn extend_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		until: T::BlockNumber,
		reasons: WithdrawReasons,
	) {
		let now = <system::Module<T>>::block_number();
		let mut new_lock = Some(BalanceLock { id, amount, until, reasons });
		let mut locks = Self::locks(who).into_iter().filter_map(|l|
			if l.id == id {
				new_lock.take().map(|nl| {
					BalanceLock {
						id: l.id,
						amount: l.amount.max(nl.amount),
						until: l.until.max(nl.until),
						reasons: l.reasons | nl.reasons,
					}
				})
			} else if l.until > now {
				Some(l)
			} else {
				None
			}).collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		<Locks<T, I>>::insert(who, locks);
	}

	fn remove_lock(
		id: LockIdentifier,
		who: &T::AccountId,
	) {
		let now = <system::Module<T>>::block_number();
		let locks = Self::locks(who).into_iter().filter_map(|l|
			if l.until > now && l.id != id {
				Some(l)
			} else {
				None
			}).collect::<Vec<_>>();
		<Locks<T, I>>::insert(who, locks);
	}
}

impl<T: Trait<I>, I: Instance> TransferAsset<T::AccountId> for Module<T, I> {
	type Amount = T::Balance;

	fn transfer(from: &T::AccountId, to: &T::AccountId, amount: T::Balance) -> Result {
		Self::make_transfer(from, to, amount)
	}

	fn withdraw(who: &T::AccountId, value: T::Balance, reason: WithdrawReason) -> Result {
		let b = Self::free_balance(who);
		ensure!(b >= value, "account has too few funds");
		let new_balance = b - value;
		Self::ensure_account_can_withdraw(who, value, reason, new_balance)?;
		Self::set_free_balance(who, new_balance);
		Self::decrease_total_stake_by(value);
		Ok(())
	}

	fn deposit(who: &T::AccountId, value: T::Balance) -> Result {
		Self::set_free_balance_creating(who, Self::free_balance(who) + value);
		Self::increase_total_stake_by(value);
		Ok(())
	}
}

impl<T: Trait<I>, I: Instance> IsDeadAccount<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDebug
{
	fn is_dead_account(who: &T::AccountId) -> bool {
		Self::total_balance(who).is_zero()
	}
}
