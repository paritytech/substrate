// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! # Balances Module
//!
//! The Balances module provides functionality for handling accounts and balances.
//!
//! - [`balances::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The Balances module provides functions for:
//!
//! - Getting and setting free balances.
//! - Retrieving total, reserved and unreserved balances.
//! - Repatriating a reserved balance to a beneficiary account that exists.
//! - Transferring a balance between accounts (when not reserved).
//! - Slashing an account balance.
//! - Account creation and removal.
//! - Managing total issuance.
//! - Setting and managing locks.
//!
//! ### Terminology
//!
//! - **Existential Deposit:** The minimum balance required to create or keep an account open. This prevents
//! "dust accounts" from filling storage. When the free plus the reserved balance (i.e. the total balance)
//!   fall below this, then the account is said to be dead; and it loses its functionality as well as any
//!   prior history and all information on it is removed from the chain's state.
//!   No account should ever have a total balance that is strictly between 0 and the existential
//!   deposit (exclusive). If this ever happens, it indicates either a bug in this module or an
//!   erroneous raw mutation of storage.
//!
//! - **Total Issuance:** The total number of units in existence in a system.
//!
//! - **Reaping an account:** The act of removing an account by resetting its nonce. Happens after its
//! total balance has become zero (or, strictly speaking, less than the Existential Deposit).
//!
//! - **Free Balance:** The portion of a balance that is not reserved. The free balance is the only
//!   balance that matters for most operations.
//!
//! - **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended.
//!   Reserved balance can still be slashed, but only after all the free balance has been slashed.
//!
//! - **Imbalance:** A condition when some funds were credited or debited without equal and opposite accounting
//! (i.e. a difference between total issuance and account balances). Functions that result in an imbalance will
//! return an object of the `Imbalance` trait that can be managed within your runtime logic. (If an imbalance is
//! simply dropped, it should automatically maintain any book-keeping such as total issuance.)
//!
//! - **Lock:** A freeze on a specified amount of an account's free balance until a specified block number. Multiple
//! locks always operate over the same funds, so they "overlay" rather than "stack".
//!
//! ### Implementations
//!
//! The Balances module provides implementations for the following traits. If these traits provide the functionality
//! that you need, then you can avoid coupling with the Balances module.
//!
//! - [`Currency`](../frame_support/traits/trait.Currency.html): Functions for dealing with a
//! fungible assets system.
//! - [`ReservableCurrency`](../frame_support/traits/trait.ReservableCurrency.html):
//! Functions for dealing with assets that can be reserved from an account.
//! - [`LockableCurrency`](../frame_support/traits/trait.LockableCurrency.html): Functions for
//! dealing with accounts that allow liquidity restrictions.
//! - [`Imbalance`](../frame_support/traits/trait.Imbalance.html): Functions for handling
//! imbalances between total issuance in the system and account balances. Must be used when a function
//! creates new funds (e.g. a reward) or destroys some funds (e.g. a system fee).
//! - [`IsDeadAccount`](../frame_system/trait.IsDeadAccount.html): Determiner to say whether a
//! given account is unused.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `transfer` - Transfer some liquid free balance to another account.
//! - `set_balance` - Set the balances of a given account. The origin of this call must be root.
//!
//! ## Usage
//!
//! The following examples show how to use the Balances module in your custom module.
//!
//! ### Examples from the SRML
//!
//! The Contract module uses the `Currency` trait to handle gas payment, and its types inherit from `Currency`:
//!
//! ```
//! use frame_support::traits::Currency;
//! # pub trait Trait: frame_system::Trait {
//! # 	type Currency: Currency<Self::AccountId>;
//! # }
//!
//! pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;
//! pub type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::NegativeImbalance;
//!
//! # fn main() {}
//! ```
//!
//! The Staking module uses the `LockableCurrency` trait to lock a stash account's funds:
//!
//! ```
//! use frame_support::traits::{WithdrawReasons, LockableCurrency};
//! use sp_runtime::traits::Bounded;
//! pub trait Trait: frame_system::Trait {
//! 	type Currency: LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;
//! }
//! # struct StakingLedger<T: Trait> {
//! # 	stash: <T as frame_system::Trait>::AccountId,
//! # 	total: <<T as Trait>::Currency as frame_support::traits::Currency<<T as frame_system::Trait>::AccountId>>::Balance,
//! # 	phantom: std::marker::PhantomData<T>,
//! # }
//! # const STAKING_ID: [u8; 8] = *b"staking ";
//!
//! fn update_ledger<T: Trait>(
//! 	controller: &T::AccountId,
//! 	ledger: &StakingLedger<T>
//! ) {
//! 	T::Currency::set_lock(
//! 		STAKING_ID,
//! 		&ledger.stash,
//! 		ledger.total,
//! 		WithdrawReasons::all()
//! 	);
//! 	// <Ledger<T>>::insert(controller, ledger); // Commented out as we don't have access to Staking's storage here.
//! }
//! # fn main() {}
//! ```
//!
//! ## Genesis config
//!
//! The Balances module depends on the [`GenesisConfig`](./struct.GenesisConfig.html).
//!
//! ## Assumptions
//!
//! * Total issued balanced of all accounts should be less than `Trait::Balance::max_value()`.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
mod migration;

use sp_std::prelude::*;
use sp_std::{cmp, result, mem, fmt::Debug, ops::BitOr};
use codec::{Codec, Encode, Decode};
use frame_support::{
	StorageValue, Parameter, decl_event, decl_storage, decl_module, decl_error, ensure,
		weights::SimpleDispatchInfo, traits::{
		UpdateBalanceOutcome, Currency, OnReapAccount, OnUnbalanced, TryDrop,
		WithdrawReason, WithdrawReasons, LockIdentifier, LockableCurrency, ExistenceRequirement,
		Imbalance, SignedImbalance, ReservableCurrency, Get, ExistenceRequirement::KeepAlive
	}
};
use sp_runtime::{
	RuntimeDebug, DispatchResult, DispatchError,
	traits::{
		Zero, SimpleArithmetic, StaticLookup, Member, CheckedAdd, CheckedSub,
		MaybeSerializeDeserialize, Saturating, Bounded,
	},
};
use frame_system::{self as system, IsDeadAccount, OnNewAccount, ensure_signed, ensure_root};
use migration::{get_storage_value, put_storage_value, StorageIterator};

pub use self::imbalances::{PositiveImbalance, NegativeImbalance};

pub trait Subtrait<I: Instance = DefaultInstance>: frame_system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy +
		MaybeSerializeDeserialize + Debug;

	/// A function that is invoked when the free-balance and the reserved-balance has fallen below
	/// the existential deposit and both have been reduced to zero.
	///
	/// All resources should be cleaned up all resources associated with the given account.
	type OnReapAccount: OnReapAccount<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// The minimum amount required to keep an account open.
	type ExistentialDeposit: Get<Self::Balance>;

	/// The fee required to create an account. If you're doing significant stuff with `OnNewAccount`
	/// then you'll probably want to make this non-zero.
	type CreationFee: Get<Self::Balance>;
}

pub trait Trait<I: Instance = DefaultInstance>: frame_system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy +
		MaybeSerializeDeserialize + Debug;

	/// A function that is invoked when the free-balance and the reserved-balance has fallen below
	/// the existential deposit and both have been reduced to zero.
	///
	/// All resources should be cleaned up all resources associated with the given account.
	type OnReapAccount: OnReapAccount<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// Handler for the unbalanced reduction when taking fees associated with balance
	/// transfer (which may also include account creation).
	type TransferPayment: OnUnbalanced<NegativeImbalance<Self, I>>;

	/// Handler for the unbalanced reduction when removing a dust account.
	type DustRemoval: OnUnbalanced<NegativeImbalance<Self, I>>;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as frame_system::Trait>::Event>;

	/// The minimum amount required to keep an account open.
	type ExistentialDeposit: Get<Self::Balance>;

	/// The fee required to create an account.
	type CreationFee: Get<Self::Balance>;
}

impl<T: Trait<I>, I: Instance> Subtrait<I> for T {
	type Balance = T::Balance;
	type OnReapAccount = T::OnReapAccount;
	type OnNewAccount = T::OnNewAccount;
	type ExistentialDeposit = T::ExistentialDeposit;
	type CreationFee = T::CreationFee;
}

decl_event!(
	pub enum Event<T, I: Instance = DefaultInstance> where
		<T as frame_system::Trait>::AccountId,
		<T as Trait<I>>::Balance
	{
		/// A new account was created.
		NewAccount(AccountId, Balance),
		/// An account was reaped.
		ReapedAccount(AccountId, Balance),
		/// Transfer succeeded (from, to, value, fees).
		Transfer(AccountId, AccountId, Balance, Balance),
		/// A balance was set by root (who, free, reserved).
		BalanceSet(AccountId, Balance, Balance),
		/// Some amount was deposited (e.g. for transaction fees).
		Deposit(AccountId, Balance),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait<I>, I: Instance> {
		/// Vesting balance too high to send value
		VestingBalance,
		/// Account liquidity restrictions prevent withdrawal
		LiquidityRestrictions,
		/// Got an overflow after adding
		Overflow,
		/// Balance too low to send value
		InsufficientBalance,
		/// Value too low to create account due to existential deposit
		ExistentialDeposit,
		/// Transfer/payment would kill account
		KeepAlive,
		/// A vesting schedule already exists for this account
		ExistingVestingSchedule,
		/// Beneficiary account must pre-exist
		DeadAccount,
	}
}

/// Simplified reasons for withdrawing balance.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
pub enum Reasons {
	/// Paying system transaction fees.
	Fee = 0,
	/// Any reason other than paying system transaction fees.
	Misc = 1,
	/// Any reason at all.
	All = 2,
}

impl From<WithdrawReasons> for Reasons {
	fn from(r: WithdrawReasons) -> Reasons {
		if r == WithdrawReasons::from(WithdrawReason::TransactionPayment) {
			Reasons::Fee
		} else if r.contains(WithdrawReason::TransactionPayment) {
			Reasons::All
		} else {
			Reasons::Misc
		}
	}
}

impl BitOr for Reasons {
	type Output = Reasons;
	fn bitor(self, other: Reasons) -> Reasons {
		if self == other { return self }
		Reasons::All
	}
}

/// A single lock on a balance. There can be many of these on an account and they "overlap", so the
/// same balance is frozen by multiple locks.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct BalanceLock<Balance> {
	/// An identifier for this lock. Only one lock may be in existence for each identifier.
	pub id: LockIdentifier,
	/// The amount which the free balance may not drop below when this lock is in effect.
	pub amount: Balance,
	/// If true, then the lock remains in effect even for payment of transaction fees.
	pub reasons: Reasons,
}

/// All balance information for an account.
#[derive(Encode, Decode, Clone, PartialEq, Eq, Default, RuntimeDebug)]
pub struct AccountData<Balance> {
	/// Non-reserved part of the balance. There may still be restrictions on this, but it is the
	/// total pool what may in principle be transferred, reserved and used for tipping.
	///
	/// This is the only balance that matters in terms of most operations on tokens. It
	/// alone is used to determine the balance when in the contract execution environment.
	pub free: Balance,
	/// Balance which is reserved and may not be used at all.
	///
	/// This can still get slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable.
	pub reserved: Balance,
	/// The amount that `free` may not drop below when withdrawing for *anything except transaction
	/// fee payment*.
	pub misc_frozen: Balance,
	/// The amount that `free` may not drop below when withdrawing specifically for transaction
	/// fee payment.
	pub fee_frozen: Balance,
}

impl<Balance: Saturating + Copy + Ord> AccountData<Balance> {
	/// How much this account's balance can be reduced for the given `reasons`.
	fn usable(&self, reasons: Reasons) -> Balance {
		self.free.saturating_sub(self.frozen(reasons))
	}
	/// The amount that this account's free balance may not be reduced beyond for the given
	/// `reasons`.
	fn frozen(&self, reasons: Reasons) -> Balance {
		match reasons {
			Reasons::All => self.misc_frozen.max(self.fee_frozen),
			Reasons::Misc => self.misc_frozen,
			Reasons::Fee => self.fee_frozen,
		}
	}
	/// The total balance in this account including any that is reserved and ignoring any frozen.
	fn total(&self) -> Balance {
		self.free.saturating_add(self.reserved)
	}
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Balances {
		/// The total units issued in the system.
		pub TotalIssuance get(fn total_issuance) build(|config: &GenesisConfig<T, I>| {
			config.balances.iter().fold(Zero::zero(), |acc: T::Balance, &(_, n)| acc + n)
		}): T::Balance;

		/// The balance of an account.
		///
		/// NOTE: THIS MAY NEVER BE IN EXISTENCE AND YET HAVE A `total().is_zero()`. If the total
		/// is ever zero, then the entry *MUST* be removed.
		pub Account get(fn account)
			build(|config: &GenesisConfig<T, I>| config.balances.iter()
				.map(|&(ref who, free)| (who.clone(), AccountData { free, .. Default::default() }))
				.collect::<Vec<_>>()
			): map hasher(blake2_256) T::AccountId => AccountData<T::Balance>;

		/// Any liquidity locks on some account balances.
		/// NOTE: Should only be accessed when setting, changing and freeing a lock.
		pub Locks get(fn locks): map hasher(blake2_256) T::AccountId => Vec<BalanceLock<T::Balance>>;

		/// True if network has been upgraded to this version.
		///
		/// True for new networks.
		IsUpgraded build(|_: &GenesisConfig<T, I>| true): bool;
	}
	add_extra_genesis {
		config(balances): Vec<(T::AccountId, T::Balance)>;
		// ^^ begin, length, amount liquid at genesis
		build(|config: &GenesisConfig<T, I>| {
			for (_, balance) in &config.balances {
				assert!(
					*balance >= <T as Trait<I>>::ExistentialDeposit::get(),
					"the balance of any account should always be more than existential deposit.",
				)
			}
		});
	}
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance = DefaultInstance> for enum Call where origin: T::Origin {
		type Error = Error<T, I>;

		/// The minimum amount required to keep an account open.
		const ExistentialDeposit: T::Balance = T::ExistentialDeposit::get();

		/// The fee required to create an account.
		const CreationFee: T::Balance = T::CreationFee::get();

		fn deposit_event() = default;

		/// Transfer some liquid free balance to another account.
		///
		/// `transfer` will set the `FreeBalance` of the sender and receiver.
		/// It will decrease the total issuance of the system by the `TransferFee`.
		/// If the sender's account is below the existential deposit as a result
		/// of the transfer, the account will be reaped.
		///
		/// The dispatch origin for this call must be `Signed` by the transactor.
		///
		/// # <weight>
		/// - Dependent on arguments but not critical, given proper implementations for
		///   input config types. See related functions below.
		/// - It contains a limited number of reads and writes internally and no complex computation.
		///
		/// Related functions:
		///
		///   - `ensure_can_withdraw` is always called internally but has a bounded complexity.
		///   - Transferring balances to accounts that did not exist before will cause
		///      `T::OnNewAccount::on_new_account` to be called.
		///   - Removing enough funds from an account will trigger `T::DustRemoval::on_unbalanced`.
		///   - `transfer_keep_alive` works the same way as `transfer`, but has an additional
		///     check that the transfer will not kill the origin account.
		///
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		pub fn transfer(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: T::Balance
		) {
			let transactor = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as Currency<_>>::transfer(&transactor, &dest, value, ExistenceRequirement::AllowDeath)?;
		}

		/// Set the balances of a given account.
		///
		/// This will alter `FreeBalance` and `ReservedBalance` in storage. it will
		/// also decrease the total issuance of the system (`TotalIssuance`).
		/// If the new free or reserved balance is below the existential deposit,
		/// it will reset the account nonce (`frame_system::AccountNonce`).
		///
		/// The dispatch origin for this call is `root`.
		///
		/// # <weight>
		/// - Independent of the arguments.
		/// - Contains a limited number of reads and writes.
		/// # </weight>
		#[weight = SimpleDispatchInfo::FixedOperational(50_000)]
		fn set_balance(
			origin,
			who: <T::Lookup as StaticLookup>::Source,
			#[compact] new_free: T::Balance,
			#[compact] new_reserved: T::Balance
		) {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;
			let existential_deposit = T::ExistentialDeposit::get();

			let wipeout = new_free + new_reserved < existential_deposit;
			let new_free = if wipeout { Zero::zero() } else { new_free };
			let new_reserved = if wipeout { Zero::zero() } else { new_reserved };

			let old_account = Account::<T, I>::get(&who);

			if new_free > old_account.free {
				mem::drop(PositiveImbalance::<T, I>::new(new_free - old_account.free));
			} else if new_free < old_account.free {
				mem::drop(NegativeImbalance::<T, I>::new(old_account.free - new_free));
			}

			if new_reserved > old_account.reserved {
				mem::drop(PositiveImbalance::<T, I>::new(new_reserved - old_account.reserved));
			} else if new_reserved < old_account.reserved {
				mem::drop(NegativeImbalance::<T, I>::new(old_account.reserved - new_reserved));
			}

			let account = AccountData { free: new_free, reserved: new_reserved, ..old_account };
			Self::set_account(&who, &account, &old_account);

			Self::deposit_event(RawEvent::BalanceSet(who, account.free, account.reserved));
		}

		/// Exactly as `transfer`, except the origin must be root and the source account may be
		/// specified.
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		pub fn force_transfer(
			origin,
			source: <T::Lookup as StaticLookup>::Source,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: T::Balance
		) {
			ensure_root(origin)?;
			let source = T::Lookup::lookup(source)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as Currency<_>>::transfer(&source, &dest, value, ExistenceRequirement::AllowDeath)?;
		}

		/// Same as the [`transfer`] call, but with a check that the transfer will not kill the
		/// origin account.
		///
		/// 99% of the time you want [`transfer`] instead.
		///
		/// [`transfer`]: struct.Module.html#method.transfer
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		pub fn transfer_keep_alive(
			origin,
			dest: <T::Lookup as StaticLookup>::Source,
			#[compact] value: T::Balance
		) {
			let transactor = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as Currency<_>>::transfer(&transactor, &dest, value, KeepAlive)?;
		}

		fn on_initialize() {
			if !IsUpgraded::<I>::get() {
				IsUpgraded::<I>::put(true);
				Self::do_upgrade();
			}
		}
	}
}

#[derive(Decode)]
struct OldBalanceLock<Balance, BlockNumber> {
	id: LockIdentifier,
	amount: Balance,
	until: BlockNumber,
	reasons: WithdrawReasons,
}

impl<Balance, BlockNumber> OldBalanceLock<Balance, BlockNumber> {
	fn upgraded(self) -> (BalanceLock<Balance>, BlockNumber) {
		(BalanceLock {
			id: self.id,
			amount: self.amount,
			reasons: self.reasons.into(),
		}, self.until)
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {
	// PRIVATE MUTABLES

	// Upgrade from the pre-#4649 balances/vesting into the new balances.
	pub fn do_upgrade() {
		sp_runtime::print("Upgrading account balances...");
		// First, migrate from old FreeBalance to new Account.
		// We also move all locks across since only accounts with FreeBalance values have locks.
		// FreeBalance: map T::AccountId => T::Balance
		for (hash, free) in StorageIterator::<T::Balance>::new(b"Balances", b"FreeBalance").drain() {
			let mut account = AccountData { free, ..Default::default() };
			// Locks: map T::AccountId => Vec<BalanceLock>
			let old_locks = get_storage_value::<Vec<OldBalanceLock<T::Balance, T::BlockNumber>>>(b"Balances", b"Locks", &hash);
			if let Some(locks) = old_locks {
				let locks = locks.into_iter()
					.map(|i| {
						let (result, expiry) = i.upgraded();
						if expiry != T::BlockNumber::max_value() {
							// Any `until`s that are not T::BlockNumber::max_value come from
							// democracy and need to be migrated over there.
							// Democracy: Locks get(locks): map T::AccountId => Option<T::BlockNumber>;
							put_storage_value(b"Democracy", b"Locks", &hash, expiry);
						}
						result
					})
					.collect::<Vec<_>>();
				for l in locks.iter() {
					if l.reasons == Reasons::All || l.reasons == Reasons::Misc {
						account.misc_frozen = account.misc_frozen.max(l.amount);
					}
					if l.reasons == Reasons::All || l.reasons == Reasons::Fee {
						account.fee_frozen = account.fee_frozen.max(l.amount);
					}
				}
				put_storage_value(b"Balances", b"Locks", &hash, locks);
			}
			put_storage_value(b"Balances", b"Account", &hash, account);
		}
		// Second, migrate old ReservedBalance into new Account.
		// ReservedBalance: map T::AccountId => T::Balance
		for (hash, reserved) in StorageIterator::<T::Balance>::new(b"Balances", b"ReservedBalance").drain() {
			let mut account = get_storage_value::<AccountData<T::Balance>>(b"Balances", b"Account", &hash).unwrap_or_default();
			account.reserved = reserved;
			put_storage_value(b"Balances", b"Account", &hash, account);
		}

		// Finally, migrate vesting and ensure locks are in place. We will be lazy and just lock
		// for the maximum amount (i.e. at genesis). Users will need to call "vest" to reduce the
		// lock to something sensible.
		// pub Vesting: map T::AccountId => Option<VestingSchedule>;
		for (hash, vesting) in StorageIterator::<(T::Balance, T::Balance, T::BlockNumber)>::new(b"Balances", b"Vesting").drain() {
			let mut account = get_storage_value::<AccountData<T::Balance>>(b"Balances", b"Account", &hash).unwrap_or_default();
			let mut locks = get_storage_value::<Vec<BalanceLock<T::Balance>>>(b"Balances", b"Locks", &hash).unwrap_or_default();
			locks.push(BalanceLock {
				id: *b"vesting ",
				amount: vesting.0.clone(),
				reasons: Reasons::Misc,
			});
			account.misc_frozen = account.misc_frozen.max(vesting.0.clone());
			put_storage_value(b"Vesting", b"Vesting", &hash, vesting);
			put_storage_value(b"Balances", b"Locks", &hash, locks);
			put_storage_value(b"Balances", b"Account", &hash, account);
		}
	}

	/// Get the free balance of an account.
	pub fn free_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Account::<T, I>::get(who.borrow()).free
	}

	/// Get the balance of an account that can be used for transfers, reservations, or any other
	/// non-locking, non-transaction-fee activity. Will be at most `free_balance`.
	pub fn usable_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Account::<T, I>::get(who.borrow()).usable(Reasons::Misc)
	}

	/// Get the balance of an account that can be used for paying transaction fees (not tipping,
	/// or any other kind of fees, though). Will be at most `free_balance`.
	pub fn usable_balance_for_fees(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Account::<T, I>::get(who.borrow()).usable(Reasons::Fee)
	}

	/// Get the reserved balance of an account.
	pub fn reserved_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Account::<T, I>::get(who.borrow()).reserved
	}

	/// Set both the free and reserved balance of an account to some new value. Will enforce
	/// `ExistentialDeposit` law, annulling the account as needed.
	///
	/// Will return `AccountKilled` if either reserved or free are too low.
	///
	/// NOTE: This assumes that `account` is the same as `Self::account(who)` except for altered
	/// values of `free` and `balance`.
	///
	/// NOTE: Doesn't do any preparatory work for creating a new account, so should only be used
	/// when it is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn set_account(
		who: &T::AccountId,
		account: &AccountData<T::Balance>,
		old: &AccountData<T::Balance>,
	) -> UpdateBalanceOutcome {
		let total = account.free + account.reserved;
		if total < T::ExistentialDeposit::get() {
			T::DustRemoval::on_unbalanced(NegativeImbalance::new(total));
			if !old.total().is_zero() {
				Self::reap_account(who, total);
				UpdateBalanceOutcome::AccountKilled
			} else {
				UpdateBalanceOutcome::StillDead
			}
		} else {
			if old.total().is_zero() {
				Self::about_to_create_account(who, account.free);
			}
			Account::<T, I>::insert(who, account);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Register a new account (with existential balance).
	///
	/// This just calls appropriate hooks. It doesn't (necessarily) make any state changes.
	fn about_to_create_account(who: &T::AccountId, balance: T::Balance) {
		T::OnNewAccount::on_new_account(&who);
		Self::deposit_event(RawEvent::NewAccount(who.clone(), balance.clone()));
	}

	/// Unregister an account.
	///
	/// This just removes the nonce and leaves an event.
	fn reap_account(who: &T::AccountId, dust: T::Balance) {
		Locks::<T, I>::remove(who);
		Account::<T, I>::remove(who);
		T::OnReapAccount::on_reap_account(who);
		Self::deposit_event(RawEvent::ReapedAccount(who.clone(), dust));
	}

	/// Update the account entry for `who`, given the locks.
	fn update_locks(who: &T::AccountId, locks: &[BalanceLock<T::Balance>]) {
		Account::<T, I>::mutate(who, |b| {
			b.misc_frozen = Zero::zero();
			b.fee_frozen = Zero::zero();
			for l in locks.iter() {
				if l.reasons == Reasons::All || l.reasons == Reasons::Misc {
					b.misc_frozen = b.misc_frozen.max(l.amount);
				}
				if l.reasons == Reasons::All || l.reasons == Reasons::Fee {
					b.fee_frozen = b.fee_frozen.max(l.amount);
				}
			}
		});
		Locks::<T, I>::insert(who, locks);
	}
}

// wrapping these imbalances in a private module is necessary to ensure absolute privacy
// of the inner member.
mod imbalances {
	use super::{
		result, Subtrait, DefaultInstance, Imbalance, Trait, Zero, Instance, Saturating,
		StorageValue, TryDrop,
	};
	use sp_std::mem;

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been created without any equal and opposite accounting.
	#[must_use]
	pub struct PositiveImbalance<T: Subtrait<I>, I: Instance=DefaultInstance>(T::Balance);

	impl<T: Subtrait<I>, I: Instance> PositiveImbalance<T, I> {
		/// Create a new positive imbalance from a balance.
		pub fn new(amount: T::Balance) -> Self {
			PositiveImbalance(amount)
		}
	}

	/// Opaque, move-only struct with private fields that serves as a token denoting that
	/// funds have been destroyed without any equal and opposite accounting.
	#[must_use]
	pub struct NegativeImbalance<T: Subtrait<I>, I: Instance=DefaultInstance>(T::Balance);

	impl<T: Subtrait<I>, I: Instance> NegativeImbalance<T, I> {
		/// Create a new negative imbalance from a balance.
		pub fn new(amount: T::Balance) -> Self {
			NegativeImbalance(amount)
		}
	}

	impl<T: Trait<I>, I: Instance> TryDrop for PositiveImbalance<T, I> {
		fn try_drop(self) -> result::Result<(), Self> {
			self.drop_zero()
		}
	}

	impl<T: Trait<I>, I: Instance> Imbalance<T::Balance> for PositiveImbalance<T, I> {
		type Opposite = NegativeImbalance<T, I>;

		fn zero() -> Self {
			Self(Zero::zero())
		}
		fn drop_zero(self) -> result::Result<(), Self> {
			if self.0.is_zero() {
				Ok(())
			} else {
				Err(self)
			}
		}
		fn split(self, amount: T::Balance) -> (Self, Self) {
			let first = self.0.min(amount);
			let second = self.0 - first;

			mem::forget(self);
			(Self(first), Self(second))
		}
		fn merge(mut self, other: Self) -> Self {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);

			self
		}
		fn subsume(&mut self, other: Self) {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);
		}
		fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a >= b {
				Ok(Self(a - b))
			} else {
				Err(NegativeImbalance::new(b - a))
			}
		}
		fn peek(&self) -> T::Balance {
			self.0.clone()
		}
	}

	impl<T: Trait<I>, I: Instance> TryDrop for NegativeImbalance<T, I> {
		fn try_drop(self) -> result::Result<(), Self> {
			self.drop_zero()
		}
	}

	impl<T: Trait<I>, I: Instance> Imbalance<T::Balance> for NegativeImbalance<T, I> {
		type Opposite = PositiveImbalance<T, I>;

		fn zero() -> Self {
			Self(Zero::zero())
		}
		fn drop_zero(self) -> result::Result<(), Self> {
			if self.0.is_zero() {
				Ok(())
			} else {
				Err(self)
			}
		}
		fn split(self, amount: T::Balance) -> (Self, Self) {
			let first = self.0.min(amount);
			let second = self.0 - first;

			mem::forget(self);
			(Self(first), Self(second))
		}
		fn merge(mut self, other: Self) -> Self {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);

			self
		}
		fn subsume(&mut self, other: Self) {
			self.0 = self.0.saturating_add(other.0);
			mem::forget(other);
		}
		fn offset(self, other: Self::Opposite) -> result::Result<Self, Self::Opposite> {
			let (a, b) = (self.0, other.0);
			mem::forget((self, other));

			if a >= b {
				Ok(Self(a - b))
			} else {
				Err(PositiveImbalance::new(b - a))
			}
		}
		fn peek(&self) -> T::Balance {
			self.0.clone()
		}
	}

	impl<T: Subtrait<I>, I: Instance> Drop for PositiveImbalance<T, I> {
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<super::ElevatedTrait<T, I>, I>>::mutate(
				|v| *v = v.saturating_add(self.0)
			);
		}
	}

	impl<T: Subtrait<I>, I: Instance> Drop for NegativeImbalance<T, I> {
		/// Basic drop handler will just square up the total issuance.
		fn drop(&mut self) {
			<super::TotalIssuance<super::ElevatedTrait<T, I>, I>>::mutate(
				|v| *v = v.saturating_sub(self.0)
			);
		}
	}
}

// TODO: #2052
// Somewhat ugly hack in order to gain access to module's `increase_total_issuance_by`
// using only the Subtrait (which defines only the types that are not dependent
// on Positive/NegativeImbalance). Subtrait must be used otherwise we end up with a
// circular dependency with Trait having some types be dependent on PositiveImbalance<Trait>
// and PositiveImbalance itself depending back on Trait for its Drop impl (and thus
// its type declaration).
// This works as long as `increase_total_issuance_by` doesn't use the Imbalance
// types (basically for charging fees).
// This should eventually be refactored so that the three type items that do
// depend on the Imbalance type (TransferPayment, DustRemoval)
// are placed in their own SRML module.
struct ElevatedTrait<T: Subtrait<I>, I: Instance>(T, I);
impl<T: Subtrait<I>, I: Instance> Clone for ElevatedTrait<T, I> {
	fn clone(&self) -> Self { unimplemented!() }
}
impl<T: Subtrait<I>, I: Instance> PartialEq for ElevatedTrait<T, I> {
	fn eq(&self, _: &Self) -> bool { unimplemented!() }
}
impl<T: Subtrait<I>, I: Instance> Eq for ElevatedTrait<T, I> {}
impl<T: Subtrait<I>, I: Instance> frame_system::Trait for ElevatedTrait<T, I> {
	type Origin = T::Origin;
	type Call = T::Call;
	type Index = T::Index;
	type BlockNumber = T::BlockNumber;
	type Hash = T::Hash;
	type Hashing = T::Hashing;
	type AccountId = T::AccountId;
	type Lookup = T::Lookup;
	type Header = T::Header;
	type Event = ();
	type BlockHashCount = T::BlockHashCount;
	type MaximumBlockWeight = T::MaximumBlockWeight;
	type MaximumBlockLength = T::MaximumBlockLength;
	type AvailableBlockRatio = T::AvailableBlockRatio;
	type Version = T::Version;
	type ModuleToIndex = T::ModuleToIndex;
}
impl<T: Subtrait<I>, I: Instance> Trait<I> for ElevatedTrait<T, I> {
	type Balance = T::Balance;
	type OnReapAccount = T::OnReapAccount;
	type OnNewAccount = T::OnNewAccount;
	type Event = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = T::ExistentialDeposit;
	type CreationFee = T::CreationFee;
}

impl<T: Trait<I>, I: Instance> Currency<T::AccountId> for Module<T, I> where
	T::Balance: MaybeSerializeDeserialize + Debug
{
	type Balance = T::Balance;
	type PositiveImbalance = PositiveImbalance<T, I>;
	type NegativeImbalance = NegativeImbalance<T, I>;

	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).total()
	}

	// Check if `value` amount of free balance can be slashed from `who`.
	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		if value.is_zero() { return true }
		Self::free_balance(who) >= value
	}

	fn total_issuance() -> Self::Balance {
		<TotalIssuance<T, I>>::get()
	}

	fn minimum_balance() -> Self::Balance {
		T::ExistentialDeposit::get()
	}

	fn free_balance(who: &T::AccountId) -> Self::Balance {
		Account::<T, I>::get(who).free
	}

	// Burn funds from the total issuance, returning a positive imbalance for the amount burned.
	// Is a no-op if amount to be burned is zero.
	fn burn(mut amount: Self::Balance) -> Self::PositiveImbalance {
		if amount.is_zero() { return PositiveImbalance::zero() }
		<TotalIssuance<T, I>>::mutate(|issued| {
			*issued = issued.checked_sub(&amount).unwrap_or_else(|| {
				amount = *issued;
				Zero::zero()
			});
		});
		PositiveImbalance::new(amount)
	}

	// Create new funds into the total issuance, returning a negative imbalance
	// for the amount issued.
	// Is a no-op if amount to be issued it zero.
	fn issue(mut amount: Self::Balance) -> Self::NegativeImbalance {
		if amount.is_zero() { return NegativeImbalance::zero() }
		<TotalIssuance<T, I>>::mutate(|issued|
			*issued = issued.checked_add(&amount).unwrap_or_else(|| {
				amount = Self::Balance::max_value() - *issued;
				Self::Balance::max_value()
			})
		);
		NegativeImbalance::new(amount)
	}

	// Ensure that an account can withdraw from their free balance given any existing withdrawal
	// restrictions like locks and vesting balance.
	// Is a no-op if amount to be withdrawn is zero.
	//
	// # <weight>
	// Despite iterating over a list of locks, they are limited by the number of
	// lock IDs, which means the number of runtime modules that intend to use and create locks.
	// # </weight>
	fn ensure_can_withdraw(
		who: &T::AccountId,
		amount: T::Balance,
		reasons: WithdrawReasons,
		new_balance: T::Balance,
	) -> DispatchResult {
		if amount.is_zero() { return Ok(()) }
		let min_balance = Account::<T, I>::get(who).frozen(reasons.into());
		ensure!(new_balance >= min_balance, Error::<T, I>::LiquidityRestrictions);
		Ok(())
	}

	// Transfer some free balance from `transactor` to `dest`, respecting existence requirements.
	// Is a no-op if value to be transferred is zero or the `transactor` is the same as `dest`.
	fn transfer(
		transactor: &T::AccountId,
		dest: &T::AccountId,
		value: Self::Balance,
		existence_requirement: ExistenceRequirement,
	) -> DispatchResult {
		if value.is_zero() || transactor == dest { return Ok(()) }

		let old_from_account = Self::account(transactor);
		let mut from_account = old_from_account.clone();
		let old_to_account = Self::account(dest);
		let mut to_account = old_to_account.clone();

		let would_create = to_account.total().is_zero();
		let fee = if would_create { T::CreationFee::get() } else { Zero::zero() };
		let liability = value.checked_add(&fee).ok_or(Error::<T, I>::Overflow)?;

		from_account.free = from_account.free.checked_sub(&liability)
			.ok_or(Error::<T, I>::InsufficientBalance)?;

		// NOTE: total stake being stored in the same type means that this could never overflow
		// but better to be safe than sorry.
		to_account.free = to_account.free.checked_add(&value).ok_or(Error::<T, I>::Overflow)?;

		let ed = T::ExistentialDeposit::get();
		ensure!(to_account.free >= ed, Error::<T, I>::ExistentialDeposit);

		Self::ensure_can_withdraw(
			transactor,
			value,
			WithdrawReason::Transfer.into(),
			from_account.free,
		)?;

		let allow_death = existence_requirement == ExistenceRequirement::AllowDeath;
		ensure!(allow_death || from_account.free >= ed, Error::<T, I>::KeepAlive);

		Self::set_account(transactor, &from_account, &old_from_account);

		// Take action on the set_account call.
		// This will emit events that _resulted_ from the transfer.
		Self::set_account(dest, &to_account, &old_to_account);

		// Emit transfer event.
		Self::deposit_event(RawEvent::Transfer(transactor.clone(), dest.clone(), value, fee));

		T::TransferPayment::on_unbalanced(NegativeImbalance::new(fee));

		Ok(())
	}

	// Withdraw some free balance from an account, respecting existence requirements.
	// Is a no-op if value to be withdrawn is zero.
	fn withdraw(
		who: &T::AccountId,
		value: Self::Balance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> result::Result<Self::NegativeImbalance, DispatchError> {
		if value.is_zero() { return Ok(NegativeImbalance::zero()); }

		let old_account = Self::account(who);
		let mut account = old_account.clone();
		if let Some(new_free_account) = account.free.checked_sub(&value) {
			// if we need to keep the account alive...
			if liveness == ExistenceRequirement::KeepAlive
				// ...and it would be dead afterwards...
				&& new_free_account < T::ExistentialDeposit::get()
				// ...yet is was alive before
				&& account.free >= T::ExistentialDeposit::get()
			{
				Err(Error::<T, I>::KeepAlive)?
			}
			Self::ensure_can_withdraw(who, value, reasons, new_free_account)?;
			account.free = new_free_account;
			Self::set_account(who, &account, &old_account);
			Ok(NegativeImbalance::new(value))
		} else {
			Err(Error::<T, I>::InsufficientBalance)?
		}
	}

	/// Slash a target account `who`, returning the negative imbalance created and any left over
	/// amount that could not be slashed.
	///
	/// Is a no-op if `value` to be slashed is zero.
	///
	/// NOTE: `slash()` prefers free balance, but assumes that reserve balance can be drawn
	/// from in extreme circumstances. `can_slash()` should be used prior to `slash()` to avoid having
	/// to draw from reserved funds, however we err on the side of punishment if things are inconsistent
	/// or `can_slash` wasn't used appropriately.
	fn slash(
		who: &T::AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance) {
		if value.is_zero() { return (NegativeImbalance::zero(), Zero::zero()) }

		let old_account = Self::account(who);
		let mut account = old_account.clone();

		let free_slash = cmp::min(account.free, value);
		account.free -= free_slash;

		let remaining_slash = value - free_slash;
		let result = if !remaining_slash.is_zero() {
			let reserved_slash = cmp::min(account.reserved, remaining_slash);
			account.reserved -= reserved_slash;
			(NegativeImbalance::new(free_slash + reserved_slash), remaining_slash - reserved_slash)
		} else {
			(NegativeImbalance::new(value), Zero::zero())
		};
		Self::set_account(who, &account, &old_account);
		result
	}

	/// Deposit some `value` into the free balance of an existing target account `who`.
	///
	/// Is a no-op if the `value` to be deposited is zero.
	fn deposit_into_existing(
		who: &T::AccountId,
		value: Self::Balance
	) -> result::Result<Self::PositiveImbalance, DispatchError> {
		if value.is_zero() { return Ok(PositiveImbalance::zero()) }

		let old_account = Self::account(who);
		let mut account = old_account.clone();
		ensure!(!account.total().is_zero(), Error::<T, I>::DeadAccount);
		account.free = account.free.checked_add(&value).ok_or(Error::<T, I>::Overflow)?;

		Self::set_account(who, &account, &old_account);
		Ok(PositiveImbalance::new(value))
	}

	/// Deposit some `value` into the free balance of `who`, possibly creating a new account.
	///
	/// This function is a no-op if:
	/// - the `value` to be deposited is zero; or
	/// - if the `value` to be deposited is less than the ED and the account does not yet exist; or
	/// - `value` is so large it would cause the balance of `who` to overflow.
	fn deposit_creating(
		who: &T::AccountId,
		value: Self::Balance,
	) -> Self::PositiveImbalance {
		if value.is_zero() { return Self::PositiveImbalance::zero() }

		let old_account = Self::account(who);
		let mut account = old_account.clone();
		let ed = T::ExistentialDeposit::get();

		// bail if not yet created and this operation wouldn't be enough to create it.
		if value < ed && account.total().is_zero() { return Self::PositiveImbalance::zero() }

		// defensive only: overflow should never happen, however in case it does, then this
		// operation is a no-op.
		account.free = match account.free.checked_add(&value) {
			Some(f) => f,
			None => return Self::PositiveImbalance::zero(),
		};

		Self::set_account(who, &account, &old_account);

		PositiveImbalance::new(value)
	}

	/// Force the new free balance of a target account `who` to some new value `balance`.
	fn make_free_balance_be(who: &T::AccountId, value: Self::Balance) -> (
		SignedImbalance<Self::Balance, Self::PositiveImbalance>,
		UpdateBalanceOutcome
	) {
		let old_account = Self::account(who);
		let mut account = old_account.clone();

		if value < T::ExistentialDeposit::get() && account.free.is_zero() {
			// If we're attempting to set an existing account to less than ED, then
			// bypass the entire operation. It's a no-op if you follow it through, but
			// since this is an instance where we might account for a negative imbalance
			// (in the dust cleaner of set_account) before we account for its actual
			// equal and opposite cause (returned as an Imbalance), then in the
			// instance that there's no other accounts on the system at all, we might
			// underflow the issuance and our arithmetic will be off.
			return (
				SignedImbalance::Positive(Self::PositiveImbalance::zero()),
				UpdateBalanceOutcome::AccountKilled,
			)
		}
		let imbalance = if account.free <= value {
			SignedImbalance::Positive(PositiveImbalance::new(value - account.free))
		} else {
			SignedImbalance::Negative(NegativeImbalance::new(account.free - value))
		};
		account.free = value;

		// If the balance is too low, then the account is reaped.
		// Free balance can never be less than ED. If that happens, it gets reduced to zero
		// and the account information relevant to this subsystem is deleted (i.e. the
		// account is reaped).
		let outcome = Self::set_account(who, &account, &old_account);
		(imbalance, outcome)
	}
}

impl<T: Trait<I>, I: Instance> ReservableCurrency<T::AccountId> for Module<T, I>  where
	T::Balance: MaybeSerializeDeserialize + Debug
{
	/// Check if `who` can reserve `value` from their free balance.
	///
	/// Always `true` if value to be reserved is zero.
	fn can_reserve(who: &T::AccountId, value: Self::Balance) -> bool {
		if value.is_zero() { return true }
		Self::account(who).free
			.checked_sub(&value)
			.map_or(false, |new_balance|
				Self::ensure_can_withdraw(who, value, WithdrawReason::Reserve.into(), new_balance).is_ok()
			)
	}

	fn reserved_balance(who: &T::AccountId) -> Self::Balance {
		Self::account(who).reserved
	}

	/// Move `value` from the free balance from `who` to their reserved balance.
	///
	/// Is a no-op if value to be reserved is zero.
	fn reserve(who: &T::AccountId, value: Self::Balance) -> result::Result<(), DispatchError> {
		if value.is_zero() { return Ok(()) }

		let old_account = Self::account(who);
		let mut account = old_account.clone();

		account.free = account.free.checked_sub(&value).ok_or(Error::<T, I>::InsufficientBalance)?;
		account.reserved = account.reserved.checked_add(&value).ok_or(Error::<T, I>::Overflow)?;
		Self::ensure_can_withdraw(who, value, WithdrawReason::Reserve.into(), account.free)?;

		Self::set_account(who, &account, &old_account);
		Ok(())
	}

	/// Unreserve some funds, returning any amount that was unable to be unreserved.
	///
	/// Is a no-op if the value to be unreserved is zero.
	fn unreserve(who: &T::AccountId, value: Self::Balance) -> Self::Balance {
		if value.is_zero() { return Zero::zero() }

		let old_account = Self::account(who);
		let mut account = old_account.clone();

		let actual = cmp::min(account.reserved, value);
		account.reserved -= actual;
		// defensive only: this can never fail since total issuance which is at least free+reserved
		// fits into the same datatype.
		account.free = account.free.saturating_add(actual);

		Self::set_account(who, &account, &old_account);

		value - actual
	}

	/// Slash from reserved balance, returning the negative imbalance created,
	/// and any amount that was unable to be slashed.
	///
	/// Is a no-op if the value to be slashed is zero.
	fn slash_reserved(
		who: &T::AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance) {
		if value.is_zero() { return (NegativeImbalance::zero(), Zero::zero()) }

		let old_account = Self::account(who);
		let mut account = old_account.clone();

		// underflow should never happen, but it if does, there's nothing to be done here.
		let actual = cmp::min(account.reserved, value);
		account.reserved -= actual;

		Self::set_account(who, &account, &old_account);

		(NegativeImbalance::new(actual), value - actual)
	}

	/// Move the reserved balance of one account into the free balance of another.
	///
	/// Is a no-op if the value to be moved is zero.
	fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance,
	) -> result::Result<Self::Balance, DispatchError> {
		if value.is_zero() { return Ok (Zero::zero()) }

		if slashed == beneficiary {
			return Ok(Self::unreserve(slashed, value));
		}

		let old_to_account = Self::account(beneficiary);
		let mut to_account = old_to_account.clone();
		ensure!(!to_account.total().is_zero(), Error::<T, I>::DeadAccount);

		let old_from_account = Self::account(slashed);
		let mut from_account = old_from_account.clone();
		let actual = cmp::min(from_account.reserved, value);

		to_account.free = to_account.free.checked_add(&actual).ok_or(Error::<T, I>::Overflow)?;
		from_account.reserved -= actual;

		Self::set_account(slashed, &from_account, &old_from_account);
		Self::set_account(beneficiary, &to_account, &old_to_account);

		Ok(value - actual)
	}
}

impl<T: Trait<I>, I: Instance> LockableCurrency<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug
{
	type Moment = T::BlockNumber;

	// Set a lock on the balance of `who`.
	// Is a no-op if lock amount is zero or `reasons` `is_none()`.
	fn set_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		reasons: WithdrawReasons,
	) {
		if amount.is_zero() || reasons.is_none() { return }
		let mut new_lock = Some(BalanceLock { id, amount, reasons: reasons.into() });
		let mut locks = Self::locks(who).into_iter().filter_map(|l|
			if l.id == id {
				new_lock.take()
			} else {
				Some(l)
			}).collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		Self::update_locks(who, &locks[..]);
	}

	// Extend a lock on the balance of `who`.
	// Is a no-op if lock amount is zero or `reasons` `is_none()`.
	fn extend_lock(
		id: LockIdentifier,
		who: &T::AccountId,
		amount: T::Balance,
		reasons: WithdrawReasons,
	) {
		if amount.is_zero() || reasons.is_none() { return }
		let mut new_lock = Some(BalanceLock { id, amount, reasons: reasons.into() });
		let mut locks = Self::locks(who).into_iter().filter_map(|l|
			if l.id == id {
				new_lock.take().map(|nl| {
					BalanceLock {
						id: l.id,
						amount: l.amount.max(nl.amount),
						reasons: l.reasons | nl.reasons,
					}
				})
			} else {
				Some(l)
			}).collect::<Vec<_>>();
		if let Some(lock) = new_lock {
			locks.push(lock)
		}
		Self::update_locks(who, &locks[..]);
	}

	fn remove_lock(
		id: LockIdentifier,
		who: &T::AccountId,
	) {
		let mut locks = Self::locks(who);
		locks.retain(|l| l.id != id);
		Self::update_locks(who, &locks[..]);
	}
}

impl<T: Trait<I>, I: Instance> IsDeadAccount<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDeserialize + Debug
{
	fn is_dead_account(who: &T::AccountId) -> bool {
		// this should always be exactly equivalent to `Self::account(who).total().is_zero()`
		!Account::<T, I>::exists(who)
	}
}
