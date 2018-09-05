// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Balances: Handles balances.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

#[cfg_attr(feature = "std", macro_use)]
extern crate substrate_runtime_std as rstd;

#[macro_use]
extern crate substrate_codec_derive;

extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
use rstd::{cmp, result};
use codec::{Encode, Decode, Codec, Input, Output};
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;
use primitives::traits::{Zero, One, RefInto, SimpleArithmetic, OnFinalise, MakePayment,
	As, AuxLookup, Member, CheckedAdd, CheckedSub};
use address::Address as RawAddress;

mod mock;

pub mod address;
mod tests;
mod genesis_config;

#[cfg(feature = "std")]
pub use genesis_config::GenesisConfig;

/// Number of account IDs stored per enum set.
const ENUM_SET_SIZE: usize = 64;

/// The byte to identify intention to reclaim an existing account index.
const RECLAIM_INDEX_MAGIC: usize = 0x69;

pub type Address<T> = RawAddress<<T as system::Trait>::AccountId, <T as Trait>::AccountIndex>;

pub type Event<T> = RawEvent<
	<T as system::Trait>::AccountId,
	<T as Trait>::AccountIndex
>;

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

/// Trait for a hook to get called when some balance has been minted.
pub trait OnMinted<Balance> {
	/// Some balance `b` was minted.
	fn on_minted(b: Balance);
}

impl<Balance> OnMinted<Balance> for () {
	fn on_minted(_b: Balance) {}
}

/// Determinator for whether a given account is able to transfer balance.
pub trait EnsureAccountLiquid<AccountId> {
	/// Returns `Ok` iff the account is able to transfer funds normally. `Err(...)`
	/// with the reason why not otherwise.
	fn ensure_account_liquid(who: &AccountId) -> Result;
}

impl<AccountId> EnsureAccountLiquid<AccountId> for () {
	fn ensure_account_liquid(_who: &AccountId) -> Result { Ok(()) }
}

pub trait Trait: system::Trait {
	/// The balance of an account.
	type Balance: Parameter + SimpleArithmetic + Codec + Default + Copy + As<Self::AccountIndex> + As<usize> + As<u64>;
	/// Type used for storing an account's index; implies the maximum number of accounts the system
	/// can hold.
	type AccountIndex: Parameter + Member + Codec + SimpleArithmetic + As<u8> + As<u16> + As<u32> + As<u64> + As<usize> + Copy;
	/// A function which is invoked when the free-balance has fallen below the existential deposit and
	/// has been reduced to zero.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnFreeBalanceZero: OnFreeBalanceZero<Self::AccountId>;

	/// A function that returns true iff a given account can transfer its funds to another account.
	type EnsureAccountLiquid: EnsureAccountLiquid<Self::AccountId>;

	/// The overarching event type. 
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_module! {
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		fn transfer(aux, dest: RawAddress<T::AccountId, T::AccountIndex>, value: T::Balance) -> Result;
	}

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum PrivCall {
		fn set_balance(who: RawAddress<T::AccountId, T::AccountIndex>, free: T::Balance, reserved: T::Balance) -> Result;
	}
}

/// An event in this module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawEvent<AccountId, AccountIndex> {
	/// A new account was created.
	NewAccount(AccountId, AccountIndex, NewAccountOutcome),
	/// An account was reaped.
	ReapedAccount(AccountId),
}

impl<A, I> From<RawEvent<A, I>> for () {
	fn from(_: RawEvent<A, I>) -> () { () }
}

decl_storage! {
	trait Store for Module<T: Trait> as Balances {
		/// The total amount of stake on the system.
		pub TotalIssuance get(total_stake): required T::Balance;
		/// The minimum amount allowed to keep an account open.
		pub ExistentialDeposit get(existential_deposit): required T::Balance;
		/// The amount credited to a destination's account whose index was reclaimed.
		pub ReclaimRebate get(reclaim_rebate): required T::Balance;
		/// The fee required to make a transfer.
		pub TransferFee get(transfer_fee): required T::Balance;
		/// The fee required to create an account. At least as big as ReclaimRebate.
		pub CreationFee get(creation_fee): required T::Balance;

		/// The next free enumeration set.
		pub NextEnumSet get(next_enum_set): required T::AccountIndex;
		/// The enumeration sets.
		pub EnumSet get(enum_set): default map [ T::AccountIndex => Vec<T::AccountId> ];

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
		pub FreeBalance get(free_balance): default map [ T::AccountId => T::Balance ];

		/// The amount of the balance of a given account that is exterally reserved; this can still get
		/// slashed, but gets slashed last of all.
		///
		/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
		/// that are still 'owned' by the account holder, but which are unspendable. (This is different
		/// and wholly unrelated to the `Bondage` system used in the staking module.)
		///
		/// When this balance falls below the value of `ExistentialDeposit`, then this 'reserve account'
		/// is deleted: specifically, `ReservedBalance`.
		///
		/// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
		/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
		pub ReservedBalance get(reserved_balance): default map [ T::AccountId => T::Balance ];


		// Payment stuff.

		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee): required T::Balance;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee): required T::Balance;
	}
}

/// Whatever happened about the hint given when creating the new account.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone, Copy)]
pub enum NewAccountOutcome {
	NoHint,
	GoodHint,
	BadHint,
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

	/// Lookup an T::AccountIndex to get an Id, if there's one there.
	pub fn lookup_index(index: T::AccountIndex) -> Option<T::AccountId> {
		let enum_set_size = Self::enum_set_size();
		let set = Self::enum_set(index / enum_set_size);
		let i: usize = (index % enum_set_size).as_();
		set.get(i).map(|x| x.clone())
	}

	/// `true` if the account `index` is ready for reclaim.
	pub fn can_reclaim(try_index: T::AccountIndex) -> bool {
		let enum_set_size = Self::enum_set_size();
		let try_set = Self::enum_set(try_index / enum_set_size);
		let i = (try_index % enum_set_size).as_();
		i < try_set.len() && Self::total_balance(&try_set[i]).is_zero()
	}

	/// Lookup an address to get an Id, if there's one there.
	pub fn lookup_address(a: address::Address<T::AccountId, T::AccountIndex>) -> Option<T::AccountId> {
		match a {
			address::Address::Id(i) => Some(i),
			address::Address::Index(i) => Self::lookup_index(i),
		}
	}

	// PUBLIC DISPATCH

	/// Transfer some liquid free balance to another staker.
	pub fn transfer(aux: &T::PublicAux, dest: Address<T>, value: T::Balance) -> Result {
		let dest = Self::lookup(dest)?;

		let transactor = aux.ref_into();
		let from_balance = Self::free_balance(transactor);
		let would_create = from_balance.is_zero();
		let fee = if would_create { Self::creation_fee() } else { Self::transfer_fee() };
		let liability = value + fee;

		let new_from_balance = match from_balance.checked_sub(&liability) {
			Some(b) => b,
			None => return Err("balance too low to send value"),
		};
		if would_create && value < Self::existential_deposit() {
			return Err("value too low to create account");
		}
		T::EnsureAccountLiquid::ensure_account_liquid(transactor)?;

		let to_balance = Self::free_balance(&dest);
		// NOTE: total stake being stored in the same type means that this could never overflow
		// but better to be safe than sorry.
		let new_to_balance = match to_balance.checked_add(&value) {
			Some(b) => b,
			None => return Err("destination balance too high to receive value"),
		};

		if transactor != &dest {
			Self::set_free_balance(transactor, new_from_balance);			
			Self::decrease_total_stake_by(fee);
			Self::set_free_balance_creating(&dest, new_to_balance);
		}

		Ok(())
	}

	// PRIV DISPATCH

	/// Deposit one of this module's events.
	fn deposit_event(event: Event<T>) {
		<system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
	}

	/// Set the balances of a given account.
	fn set_balance(who: Address<T>, free: T::Balance, reserved: T::Balance) -> Result {
		let who = Self::lookup(who)?;
		Self::set_free_balance(&who, free);
		Self::set_reserved_balance(&who, reserved);
		Ok(())
	}

	// PUBLIC MUTABLES (DANGEROUS)

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
		// TODO: enforce this for the other balance-altering functions.
		if balance < ed {
			Self::set_free_balance(who, balance);
			UpdateBalanceOutcome::AccountKilled
		} else {
			if !<FreeBalance<T>>::exists(who) {
				let outcome = Self::new_account(&who, balance);
				let credit = match outcome {
					NewAccountOutcome::GoodHint => balance + <Module<T>>::reclaim_rebate(),
					_ => balance,
				};
				Self::set_free_balance(who, credit);
				Self::increase_total_stake_by(credit - balance);
			} else {	
				Self::set_free_balance(who, balance);
			}

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

	fn enum_set_size() -> T::AccountIndex {
		T::AccountIndex::sa(ENUM_SET_SIZE)
	}

	/// Register a new account (with existential balance).
	fn new_account(who: &T::AccountId, balance: T::Balance) -> NewAccountOutcome {
		let enum_set_size = Self::enum_set_size();
		let next_set_index = Self::next_enum_set();
		let reclaim_index_magic = T::AccountIndex::sa(RECLAIM_INDEX_MAGIC);
		let reclaim_index_modulus = T::AccountIndex::sa(256usize);
		let quantization = T::AccountIndex::sa(256usize);

		// A little easter-egg for reclaiming dead indexes..
		let ret = {
			// we quantise the number of accounts so it stays constant over a reasonable
			// period of time.
			let quantized_account_count: T::AccountIndex = (next_set_index * enum_set_size / quantization + One::one()) * quantization;
			// then modify the starting balance to be modulo this to allow it to potentially
			// identify an account index for reuse.
			let maybe_try_index = balance % <T::Balance as As<T::AccountIndex>>::sa(quantized_account_count * reclaim_index_modulus);
			let maybe_try_index = As::<T::AccountIndex>::as_(maybe_try_index);

			// this identifier must end with magic byte 0x69 to trigger this check (a minor
			// optimisation to ensure we don't check most unintended account creations).
			if maybe_try_index % reclaim_index_modulus == reclaim_index_magic {
				// reuse is probably intended. first, remove magic byte.
				let try_index = maybe_try_index / reclaim_index_modulus;

				// then check to see if this balance identifies a dead account index.
				let set_index = try_index / enum_set_size;
				let mut try_set = Self::enum_set(set_index);
				let item_index = (try_index % enum_set_size).as_();
				if item_index < try_set.len() {
					if Self::total_balance(&try_set[item_index]).is_zero() {
						// yup - this index refers to a dead account. can be reused.
						try_set[item_index] = who.clone();
						<EnumSet<T>>::insert(set_index, try_set);

						Self::deposit_event(RawEvent::NewAccount(who.clone(), try_index, NewAccountOutcome::GoodHint));

						return NewAccountOutcome::GoodHint
					}
				}
				NewAccountOutcome::BadHint
			} else {
				NewAccountOutcome::NoHint
			}
		};

		// insert normally as a back up
		let mut set_index = next_set_index;
		// defensive only: this loop should never iterate since we keep NextEnumSet up to date later.
		let mut set = loop {
			let set = Self::enum_set(set_index);
			if set.len() < ENUM_SET_SIZE {
				break set;
			}
			set_index += One::one();
		};

		let index = T::AccountIndex::sa(set_index.as_() * ENUM_SET_SIZE + set.len());

		// update set.
		set.push(who.clone());

		// keep NextEnumSet up to date
		if set.len() == ENUM_SET_SIZE {
			<NextEnumSet<T>>::put(set_index + One::one());
		}

		// write set.
		<EnumSet<T>>::insert(set_index, set);

		Self::deposit_event(RawEvent::NewAccount(who.clone(), index, ret));

		ret
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
		if let Some(v) = <Module<T>>::total_stake().checked_add(&value) {
			<TotalIssuance<T>>::put(v);
		}
	}
	/// Decrease TotalIssuance by Value.
	pub fn decrease_total_stake_by(value: T::Balance) {
		if let Some(v) = <Module<T>>::total_stake().checked_sub(&value) {
			<TotalIssuance<T>>::put(v);
		}
	}
}

impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(_n: T::BlockNumber) {
	}
}

impl<T: Trait> AuxLookup for Module<T> {
	type Source = address::Address<T::AccountId, T::AccountIndex>;
	type Target = T::AccountId;
	fn lookup(a: Self::Source) -> result::Result<Self::Target, &'static str> {
		match a {
			address::Address::Id(i) => Ok(i),
			address::Address::Index(i) => <Module<T>>::lookup_index(i).ok_or("invalid account index"),
		}
	}
}

impl<T: Trait> MakePayment<T::AccountId> for Module<T> {
	fn make_payment(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let b = Self::free_balance(transactor);
		let transaction_fee = Self::transaction_base_fee() + Self::transaction_byte_fee() * <T::Balance as As<u64>>::sa(encoded_len as u64);
		if b < transaction_fee + Self::existential_deposit() {
			return Err("not enough funds for transaction fee");
		}
		Self::set_free_balance(transactor, b - transaction_fee);
		Self::decrease_total_stake_by(transaction_fee);
		Ok(())
	}
}
