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
//! "dust accounts" from filling storage.
//! - **Total Issuance:** The total number of units in existence in a system.
//! - **Reaping an account:** The act of removing an account by resetting its nonce. Happens after its balance is set
//! to zero.
//! - **Free Balance:** The portion of a balance that is not reserved. The free balance is the only balance that matters
//! for most operations. When this balance falls below the existential deposit, most functionality of the account is
//! removed. When both it and the reserved balance are deleted, then the account is said to be dead.
//! - **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended. Reserved balance
//! can still be slashed, but only after all the free balance has been slashed. If the reserved balance falls below the
//! existential deposit then it and any related functionality will be deleted. When both it and the free balance are
//! deleted, then the account is said to be dead.
//! - **Imbalance:** A condition when some funds were credited or debited without equal and opposite accounting
//! (i.e. a difference between total issuance and account balances). Functions that result in an imbalance will
//! return an object of the `Imbalance` trait that can be managed within your runtime logic. (If an imbalance is
//! simply dropped, it should automatically maintain any book-keeping such as total issuance.)
//! - **Lock:** A freeze on a specified amount of an account's free balance until a specified block number. Multiple
//! locks always operate over the same funds, so they "overlay" rather than "stack".
//! - **Vesting:** Similar to a lock, this is another, but independent, liquidity restriction that reduces linearly
//! over time.
//!
//! ### Implementations
//!
//! The Balances module provides implementations for the following traits. If these traits provide the functionality
//! that you need, then you can avoid coupling with the Balances module.
//!
//! - [`Currency`](../srml_support/traits/trait.Currency.html): Functions for dealing with a
//! fungible assets system.
//! - [`ReservableCurrency`](../srml_support/traits/trait.ReservableCurrency.html):
//! Functions for dealing with assets that can be reserved from an account.
//! - [`LockableCurrency`](../srml_support/traits/trait.LockableCurrency.html): Functions for
//! dealing with accounts that allow liquidity restrictions.
//! - [`Imbalance`](../srml_support/traits/trait.Imbalance.html): Functions for handling
//! imbalances between total issuance in the system and account balances. Must be used when a function
//! creates new funds (e.g. a reward) or destroys some funds (e.g. a system fee).
//! - [`IsDeadAccount`](../srml_system/trait.IsDeadAccount.html): Determiner to say whether a
//! given account is unused.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `transfer` - Transfer some liquid free balance to another account.
//! - `set_balance` - Set the balances of a given account. The origin of this call must be root.
//!
//! ### Public Functions
//!
//! - `vesting_balance` - Get the amount that is currently being vested and cannot be transferred out of this account.
//!
//! ### Signed Extensions
//!
//! The balances module defines the following extensions:
//!
//!   - [`TakeFees`]: Consumes fees proportional to the length and weight of the transaction.
//!     Additionally, it can contain a single encoded payload as a `tip`. The inclusion priority
//!     is increased proportional to the tip.
//!
//! Lookup the runtime aggregator file (e.g. `node/runtime`) to see the full list of signed
//! extensions included in a chain.
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
//! use support::traits::Currency;
//! # pub trait Trait: system::Trait {
//! # 	type Currency: Currency<Self::AccountId>;
//! # }
//!
//! pub type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
//! pub type NegativeImbalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;
//!
//! # fn main() {}
//! ```
//!
//! The Staking module uses the `LockableCurrency` trait to lock a stash account's funds:
//!
//! ```
//! use support::traits::{WithdrawReasons, LockableCurrency};
//! use sr_primitives::traits::Bounded;
//! pub trait Trait: system::Trait {
//! 	type Currency: LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;
//! }
//! # struct StakingLedger<T: Trait> {
//! # 	stash: <T as system::Trait>::AccountId,
//! # 	total: <<T as Trait>::Currency as support::traits::Currency<<T as system::Trait>::AccountId>>::Balance,
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
//! 		T::BlockNumber::max_value(),
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

use rstd::prelude::*;
use rstd::{cmp, result, mem};
use codec::{Codec, Encode, Decode};
use support::{
	StorageValue, Parameter, decl_event, decl_storage, decl_module,
	traits::{
		UpdateBalanceOutcome, Currency, OnFreeBalanceZero, OnUnbalanced,
		WithdrawReason, WithdrawReasons, LockIdentifier, LockableCurrency, ExistenceRequirement,
		Imbalance, SignedImbalance, ReservableCurrency, Get,
	},
	dispatch::Result,
};
use sr_primitives::{
	transaction_validity::{
		TransactionPriority, ValidTransaction, InvalidTransaction, TransactionValidityError,
		TransactionValidity,
	},
	traits::{
		Zero, SimpleArithmetic, StaticLookup, Member, CheckedAdd, CheckedSub, MaybeSerializeDebug,
		Saturating, Bounded, SignedExtension, SaturatedConversion, Convert,
	},
	weights::{DispatchInfo, SimpleDispatchInfo, Weight},
};
use system::{IsDeadAccount, OnNewAccount, ensure_signed, ensure_root};

mod mock;
mod tests;

pub use self::imbalances::{PositiveImbalance, NegativeImbalance};

pub trait Subtrait<I: Instance = DefaultInstance>: system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy +
		MaybeSerializeDebug + From<Self::BlockNumber>;

	/// A function that is invoked when the free-balance has fallen below the existential deposit and
	/// has been reduced to zero.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnFreeBalanceZero: OnFreeBalanceZero<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// The minimum amount required to keep an account open.
	type ExistentialDeposit: Get<Self::Balance>;

	/// The fee required to make a transfer.
	type TransferFee: Get<Self::Balance>;

	/// The fee required to create an account.
	type CreationFee: Get<Self::Balance>;

	/// The fee to be paid for making a transaction; the base.
	type TransactionBaseFee: Get<Self::Balance>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee: Get<Self::Balance>;

	/// Convert a weight value into a deductible fee based on the currency type.
	type WeightToFee: Convert<Weight, Self::Balance>;
}

pub trait Trait<I: Instance = DefaultInstance>: system::Trait {
	/// The balance of an account.
	type Balance: Parameter + Member + SimpleArithmetic + Codec + Default + Copy +
		MaybeSerializeDebug + From<Self::BlockNumber>;

	/// A function that is invoked when the free-balance has fallen below the existential deposit and
	/// has been reduced to zero.
	///
	/// Gives a chance to clean up resources associated with the given account.
	type OnFreeBalanceZero: OnFreeBalanceZero<Self::AccountId>;

	/// Handler for when a new account is created.
	type OnNewAccount: OnNewAccount<Self::AccountId>;

	/// Handler for the unbalanced reduction when taking transaction fees.
	type TransactionPayment: OnUnbalanced<NegativeImbalance<Self, I>>;

	/// Handler for the unbalanced reduction when taking fees associated with balance
	/// transfer (which may also include account creation).
	type TransferPayment: OnUnbalanced<NegativeImbalance<Self, I>>;

	/// Handler for the unbalanced reduction when removing a dust account.
	type DustRemoval: OnUnbalanced<NegativeImbalance<Self, I>>;

	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;

	/// The minimum amount required to keep an account open.
	type ExistentialDeposit: Get<Self::Balance>;

	/// The fee required to make a transfer.
	type TransferFee: Get<Self::Balance>;

	/// The fee required to create an account.
	type CreationFee: Get<Self::Balance>;

	/// The fee to be paid for making a transaction; the base.
	type TransactionBaseFee: Get<Self::Balance>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee: Get<Self::Balance>;

	/// Convert a weight value into a deductible fee based on the currency type.
	type WeightToFee: Convert<Weight, Self::Balance>;
}

impl<T: Trait<I>, I: Instance> Subtrait<I> for T {
	type Balance = T::Balance;
	type OnFreeBalanceZero = T::OnFreeBalanceZero;
	type OnNewAccount = T::OnNewAccount;
	type ExistentialDeposit = T::ExistentialDeposit;
	type TransferFee = T::TransferFee;
	type CreationFee = T::CreationFee;
	type TransactionBaseFee = T::TransactionBaseFee;
	type TransactionByteFee = T::TransactionByteFee;
	type WeightToFee = T::WeightToFee;
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
pub struct VestingSchedule<Balance, BlockNumber> {
	/// Locked amount at genesis.
	pub locked: Balance,
	/// Amount that gets unlocked every block after `starting_block`.
	pub per_block: Balance,
	/// Starting block for unlocking(vesting).
	pub starting_block: BlockNumber,
}

impl<Balance: SimpleArithmetic + Copy, BlockNumber: SimpleArithmetic + Copy> VestingSchedule<Balance, BlockNumber> {
	/// Amount locked at block `n`.
	pub fn locked_at(&self, n: BlockNumber) -> Balance
		where Balance: From<BlockNumber>
	{
		// Number of blocks that count toward vesting
		// Saturating to 0 when n < starting_block
		let vested_block_count = n.saturating_sub(self.starting_block);
		// Return amount that is still locked in vesting
		if let Some(x) = Balance::from(vested_block_count).checked_mul(&self.per_block) {
			self.locked.max(x) - x
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
		/// The total units issued in the system.
		pub TotalIssuance get(total_issuance) build(|config: &GenesisConfig<T, I>| {
			config.balances.iter().fold(Zero::zero(), |acc: T::Balance, &(_, n)| acc + n)
		}): T::Balance;

		/// Information regarding the vesting of a given account.
		pub Vesting get(vesting) build(|config: &GenesisConfig<T, I>| {
			// Generate initial vesting configuration
			// * who - Account which we are generating vesting configuration for
			// * begin - Block when the account will start to vest
			// * length - Number of blocks from `begin` until fully vested
			// * liquid - Number of units which can be spent before vesting begins
			config.vesting.iter().filter_map(|&(ref who, begin, length, liquid)| {
				let length = <T::Balance as From<T::BlockNumber>>::from(length);

				config.balances.iter()
					.find(|&&(ref w, _)| w == who)
					.map(|&(_, balance)| {
						// Total genesis `balance` minus `liquid` equals funds locked for vesting
						let locked = balance.saturating_sub(liquid);
						// Number of units unlocked per block after `begin`
						let per_block = locked / length.max(sr_primitives::traits::One::one());

						(who.clone(), VestingSchedule {
							locked: locked,
							per_block: per_block,
							starting_block: begin
						})
					})
			}).collect::<Vec<_>>()
		}): map T::AccountId => Option<VestingSchedule<T::Balance, T::BlockNumber>>;

		/// The 'free' balance of a given account.
		///
		/// This is the only balance that matters in terms of most operations on tokens. It
		/// alone is used to determine the balance when in the contract execution environment. When this
		/// balance falls below the value of `ExistentialDeposit`, then the 'current account' is
		/// deleted: specifically `FreeBalance`. Further, the `OnFreeBalanceZero` callback
		/// is invoked, giving a chance to external modules to clean up data associated with
		/// the deleted account.
		///
		/// `system::AccountNonce` is also deleted if `ReservedBalance` is also zero (it also gets
		/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
		pub FreeBalance get(free_balance)
			build(|config: &GenesisConfig<T, I>| config.balances.clone()):
			map T::AccountId => T::Balance;

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
		/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.)
		pub ReservedBalance get(reserved_balance): map T::AccountId => T::Balance;

		/// Any liquidity locks on some account balances.
		pub Locks get(locks): map T::AccountId => Vec<BalanceLock<T::Balance, T::BlockNumber>>;
	}
	add_extra_genesis {
		config(balances): Vec<(T::AccountId, T::Balance)>;
		config(vesting): Vec<(T::AccountId, T::BlockNumber, T::BlockNumber, T::Balance)>;
		// ^^ begin, length, amount liquid at genesis
	}
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance = DefaultInstance> for enum Call where origin: T::Origin {
		/// The minimum amount required to keep an account open.
		const ExistentialDeposit: T::Balance = T::ExistentialDeposit::get();

		/// The fee required to make a transfer.
		const TransferFee: T::Balance = T::TransferFee::get();

		/// The fee required to create an account.
		const CreationFee: T::Balance = T::CreationFee::get();

		/// The fee to be paid for making a transaction; the base.
		const TransactionBaseFee: T::Balance = T::TransactionBaseFee::get();

		/// The fee to be paid for making a transaction; the per-byte portion.
		const TransactionByteFee: T::Balance = T::TransactionByteFee::get();

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
		///   - Removing enough funds from an account will trigger
		///     `T::DustRemoval::on_unbalanced` and `T::OnFreeBalanceZero::on_free_balance_zero`.
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
			<Self as Currency<_>>::transfer(&transactor, &dest, value)?;
		}

		/// Set the balances of a given account.
		///
		/// This will alter `FreeBalance` and `ReservedBalance` in storage. it will
		/// also decrease the total issuance of the system (`TotalIssuance`).
		/// If the new free or reserved balance is below the existential deposit,
		/// it will reset the account nonce (`system::AccountNonce`).
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

			let current_free = <FreeBalance<T, I>>::get(&who);
			if new_free > current_free {
				mem::drop(PositiveImbalance::<T, I>::new(new_free - current_free));
			} else if new_free < current_free {
				mem::drop(NegativeImbalance::<T, I>::new(current_free - new_free));
			}
			Self::set_free_balance(&who, new_free);

			let current_reserved = <ReservedBalance<T, I>>::get(&who);
			if new_reserved > current_reserved {
				mem::drop(PositiveImbalance::<T, I>::new(new_reserved - current_reserved));
			} else if new_reserved < current_reserved {
				mem::drop(NegativeImbalance::<T, I>::new(current_reserved - new_reserved));
			}
			Self::set_reserved_balance(&who, new_reserved);
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
			<Self as Currency<_>>::transfer(&source, &dest, value)?;
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {

	// PUBLIC IMMUTABLES

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	pub fn vesting_balance(who: &T::AccountId) -> T::Balance {
		if let Some(v) = Self::vesting(who) {
			Self::free_balance(who)
				.min(v.locked_at(<system::Module<T>>::block_number()))
		} else {
			Zero::zero()
		}
	}

	// PRIVATE MUTABLES

	/// Set the reserved balance of an account to some new value. Will enforce `ExistentialDeposit`
	/// law, annulling the account as needed.
	///
	/// Doesn't do any preparatory work for creating a new account, so should only be used when it
	/// is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn set_reserved_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		if balance < T::ExistentialDeposit::get() {
			<ReservedBalance<T, I>>::insert(who, balance);
			Self::on_reserved_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<ReservedBalance<T, I>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Set the free balance of an account to some new value. Will enforce `ExistentialDeposit`
	/// law, annulling the account as needed.
	///
	/// Doesn't do any preparatory work for creating a new account, so should only be used when it
	/// is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn set_free_balance(who: &T::AccountId, balance: T::Balance) -> UpdateBalanceOutcome {
		// Commented out for now - but consider it instructive.
		// assert!(!Self::total_balance(who).is_zero());
		// assert!(Self::free_balance(who) > T::ExistentialDeposit::get());
		if balance < T::ExistentialDeposit::get() {
			<FreeBalance<T, I>>::insert(who, balance);
			Self::on_free_too_low(who);
			UpdateBalanceOutcome::AccountKilled
		} else {
			<FreeBalance<T, I>>::insert(who, balance);
			UpdateBalanceOutcome::Updated
		}
	}

	/// Register a new account (with existential balance).
	///
	/// This just calls appropriate hooks. It doesn't (necessarily) make any state changes.
	fn new_account(who: &T::AccountId, balance: T::Balance) {
		T::OnNewAccount::on_new_account(&who);
		Self::deposit_event(RawEvent::NewAccount(who.clone(), balance.clone()));
	}

	/// Unregister an account.
	///
	/// This just removes the nonce and leaves an event.
	fn reap_account(who: &T::AccountId) {
		<system::AccountNonce<T>>::remove(who);
		Self::deposit_event(RawEvent::ReapedAccount(who.clone()));
	}

	/// Account's free balance has dropped below existential deposit. Kill its
	/// free side and the account completely if its reserved size is already dead.
	///
	/// Will maintain total issuance.
	fn on_free_too_low(who: &T::AccountId) {
		let dust = <FreeBalance<T, I>>::take(who);
		<Locks<T, I>>::remove(who);

		// underflow should never happen, but if it does, there's not much we can do about it.
		if !dust.is_zero() {
			T::DustRemoval::on_unbalanced(NegativeImbalance::new(dust));
		}

		T::OnFreeBalanceZero::on_free_balance_zero(who);

		if Self::reserved_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}

	/// Account's reserved balance has dropped below existential deposit. Kill its
	/// reserved side and the account completely if its free size is already dead.
	///
	/// Will maintain total issuance.
	fn on_reserved_too_low(who: &T::AccountId) {
		let dust = <ReservedBalance<T, I>>::take(who);

		// underflow should never happen, but it if does, there's nothing to be done here.
		if !dust.is_zero() {
			T::DustRemoval::on_unbalanced(NegativeImbalance::new(dust));
		}

		if Self::free_balance(who).is_zero() {
			Self::reap_account(who);
		}
	}
}

// wrapping these imbalances in a private module is necessary to ensure absolute privacy
// of the inner member.
mod imbalances {
	use super::{
		result, Subtrait, DefaultInstance, Imbalance, Trait, Zero, Instance, Saturating,
		StorageValue,
	};
	use rstd::mem;

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
// depend on the Imbalance type (TransactionPayment, TransferPayment, DustRemoval)
// are placed in their own SRML module.
struct ElevatedTrait<T: Subtrait<I>, I: Instance>(T, I);
impl<T: Subtrait<I>, I: Instance> Clone for ElevatedTrait<T, I> {
	fn clone(&self) -> Self { unimplemented!() }
}
impl<T: Subtrait<I>, I: Instance> PartialEq for ElevatedTrait<T, I> {
	fn eq(&self, _: &Self) -> bool { unimplemented!() }
}
impl<T: Subtrait<I>, I: Instance> Eq for ElevatedTrait<T, I> {}
impl<T: Subtrait<I>, I: Instance> system::Trait for ElevatedTrait<T, I> {
	type Origin = T::Origin;
	type Call = T::Call;
	type Index = T::Index;
	type BlockNumber = T::BlockNumber;
	type Hash = T::Hash;
	type Hashing = T::Hashing;
	type AccountId = T::AccountId;
	type Lookup = T::Lookup;
	type Header = T::Header;
	type WeightMultiplierUpdate = T::WeightMultiplierUpdate;
	type Event = ();
	type BlockHashCount = T::BlockHashCount;
	type MaximumBlockWeight = T::MaximumBlockWeight;
	type MaximumBlockLength = T::MaximumBlockLength;
	type AvailableBlockRatio = T::AvailableBlockRatio;
	type Version = T::Version;
}
impl<T: Subtrait<I>, I: Instance> Trait<I> for ElevatedTrait<T, I> {
	type Balance = T::Balance;
	type OnFreeBalanceZero = T::OnFreeBalanceZero;
	type OnNewAccount = T::OnNewAccount;
	type Event = ();
	type TransactionPayment = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = T::ExistentialDeposit;
	type TransferFee = T::TransferFee;
	type CreationFee = T::CreationFee;
	type TransactionBaseFee = T::TransactionBaseFee;
	type TransactionByteFee = T::TransactionByteFee;
	type WeightToFee = T::WeightToFee;
}

impl<T: Trait<I>, I: Instance> Currency<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDebug
{
	type Balance = T::Balance;
	type PositiveImbalance = PositiveImbalance<T, I>;
	type NegativeImbalance = NegativeImbalance<T, I>;

	fn total_balance(who: &T::AccountId) -> Self::Balance {
		Self::free_balance(who) + Self::reserved_balance(who)
	}

	fn can_slash(who: &T::AccountId, value: Self::Balance) -> bool {
		Self::free_balance(who) >= value
	}

	fn total_issuance() -> Self::Balance {
		<TotalIssuance<T, I>>::get()
	}

	fn minimum_balance() -> Self::Balance {
		T::ExistentialDeposit::get()
	}

	fn free_balance(who: &T::AccountId) -> Self::Balance {
		<FreeBalance<T, I>>::get(who)
	}

	fn burn(mut amount: Self::Balance) -> Self::PositiveImbalance {
		<TotalIssuance<T, I>>::mutate(|issued| {
			*issued = issued.checked_sub(&amount).unwrap_or_else(|| {
				amount = *issued;
				Zero::zero()
			});
		});
		PositiveImbalance::new(amount)
	}

	fn issue(mut amount: Self::Balance) -> Self::NegativeImbalance {
		<TotalIssuance<T, I>>::mutate(|issued|
			*issued = issued.checked_add(&amount).unwrap_or_else(|| {
				amount = Self::Balance::max_value() - *issued;
				Self::Balance::max_value()
			})
		);
		NegativeImbalance::new(amount)
	}

	// # <weight>
	// Despite iterating over a list of locks, they are limited by the number of
	// lock IDs, which means the number of runtime modules that intend to use and create locks.
	// # </weight>
	fn ensure_can_withdraw(
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
		if locks.into_iter()
			.all(|l|
				now >= l.until
				|| new_balance >= l.amount
				|| !l.reasons.contains(reason)
			)
		{
			Ok(())
		} else {
			Err("account liquidity restrictions prevent withdrawal")
		}
	}

	fn transfer(transactor: &T::AccountId, dest: &T::AccountId, value: Self::Balance) -> Result {
		let from_balance = Self::free_balance(transactor);
		let to_balance = Self::free_balance(dest);
		let would_create = to_balance.is_zero();
		let fee = if would_create { T::CreationFee::get() } else { T::TransferFee::get() };
		let liability = match value.checked_add(&fee) {
			Some(l) => l,
			None => return Err("got overflow after adding a fee to value"),
		};

		let new_from_balance = match from_balance.checked_sub(&liability) {
			None => return Err("balance too low to send value"),
			Some(b) => b,
		};
		if would_create && value < T::ExistentialDeposit::get() {
			return Err("value too low to create account");
		}
		Self::ensure_can_withdraw(transactor, value, WithdrawReason::Transfer, new_from_balance)?;

		// NOTE: total stake being stored in the same type means that this could never overflow
		// but better to be safe than sorry.
		let new_to_balance = match to_balance.checked_add(&value) {
			Some(b) => b,
			None => return Err("destination balance too high to receive value"),
		};

		if transactor != dest {
			Self::set_free_balance(transactor, new_from_balance);
			if !<FreeBalance<T, I>>::exists(dest) {
				Self::new_account(dest, new_to_balance);
			}
			Self::set_free_balance(dest, new_to_balance);
			T::TransferPayment::on_unbalanced(NegativeImbalance::new(fee));
			Self::deposit_event(RawEvent::Transfer(transactor.clone(), dest.clone(), value, fee));
		}

		Ok(())
	}

	fn withdraw(
		who: &T::AccountId,
		value: Self::Balance,
		reason: WithdrawReason,
		liveness: ExistenceRequirement,
	) -> result::Result<Self::NegativeImbalance, &'static str> {
		if let Some(new_balance) = Self::free_balance(who).checked_sub(&value) {
			if liveness == ExistenceRequirement::KeepAlive && new_balance < T::ExistentialDeposit::get() {
				return Err("payment would kill account")
			}
			Self::ensure_can_withdraw(who, value, reason, new_balance)?;
			Self::set_free_balance(who, new_balance);
			Ok(NegativeImbalance::new(value))
		} else {
			Err("too few free funds in account")
		}
	}

	fn slash(
		who: &T::AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance) {
		let free_balance = Self::free_balance(who);
		let free_slash = cmp::min(free_balance, value);
		Self::set_free_balance(who, free_balance - free_slash);
		let remaining_slash = value - free_slash;
		// NOTE: `slash()` prefers free balance, but assumes that reserve balance can be drawn
		// from in extreme circumstances. `can_slash()` should be used prior to `slash()` to avoid having
		// to draw from reserved funds, however we err on the side of punishment if things are inconsistent
		// or `can_slash` wasn't used appropriately.
		if !remaining_slash.is_zero() {
			let reserved_balance = Self::reserved_balance(who);
			let reserved_slash = cmp::min(reserved_balance, remaining_slash);
			Self::set_reserved_balance(who, reserved_balance - reserved_slash);
			(NegativeImbalance::new(free_slash + reserved_slash), remaining_slash - reserved_slash)
		} else {
			(NegativeImbalance::new(value), Zero::zero())
		}
	}

	fn deposit_into_existing(
		who: &T::AccountId,
		value: Self::Balance
	) -> result::Result<Self::PositiveImbalance, &'static str> {
		if Self::total_balance(who).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		Self::set_free_balance(who, Self::free_balance(who) + value);
		Ok(PositiveImbalance::new(value))
	}

	fn deposit_creating(
		who: &T::AccountId,
		value: Self::Balance,
	) -> Self::PositiveImbalance {
		let (imbalance, _) = Self::make_free_balance_be(who, Self::free_balance(who) + value);
		if let SignedImbalance::Positive(p) = imbalance {
			p
		} else {
			// Impossible, but be defensive.
			Self::PositiveImbalance::zero()
		}
	}

	fn make_free_balance_be(who: &T::AccountId, balance: Self::Balance) -> (
		SignedImbalance<Self::Balance, Self::PositiveImbalance>,
		UpdateBalanceOutcome
	) {
		let original = Self::free_balance(who);
		if balance < T::ExistentialDeposit::get() && original.is_zero() {
			// If we're attempting to set an existing account to less than ED, then
			// bypass the entire operation. It's a no-op if you follow it through, but
			// since this is an instance where we might account for a negative imbalance
			// (in the dust cleaner of set_free_balance) before we account for its actual
			// equal and opposite cause (returned as an Imbalance), then in the
			// instance that there's no other accounts on the system at all, we might
			// underflow the issuance and our arithmetic will be off.
			return (
				SignedImbalance::Positive(Self::PositiveImbalance::zero()),
				UpdateBalanceOutcome::AccountKilled,
			)
		}
		let imbalance = if original <= balance {
			SignedImbalance::Positive(PositiveImbalance::new(balance - original))
		} else {
			SignedImbalance::Negative(NegativeImbalance::new(original - balance))
		};
		// If the balance is too low, then the account is reaped.
		// NOTE: There are two balances for every account: `reserved_balance` and
		// `free_balance`. This contract subsystem only cares about the latter: whenever
		// the term "balance" is used *here* it should be assumed to mean "free balance"
		// in the rest of the module.
		// Free balance can never be less than ED. If that happens, it gets reduced to zero
		// and the account information relevant to this subsystem is deleted (i.e. the
		// account is reaped).
		let outcome = if balance < T::ExistentialDeposit::get() {
			Self::set_free_balance(who, balance);
			UpdateBalanceOutcome::AccountKilled
		} else {
			if !<FreeBalance<T, I>>::exists(who) {
				Self::new_account(&who, balance);
			}
			Self::set_free_balance(who, balance);
			UpdateBalanceOutcome::Updated
		};
		(imbalance, outcome)
	}
}

impl<T: Trait<I>, I: Instance> ReservableCurrency<T::AccountId> for Module<T, I>
where
	T::Balance: MaybeSerializeDebug
{
	fn can_reserve(who: &T::AccountId, value: Self::Balance) -> bool {
		Self::free_balance(who)
			.checked_sub(&value)
			.map_or(false, |new_balance|
				Self::ensure_can_withdraw(who, value, WithdrawReason::Reserve, new_balance).is_ok()
			)
	}

	fn reserved_balance(who: &T::AccountId) -> Self::Balance {
		<ReservedBalance<T, I>>::get(who)
	}

	fn reserve(who: &T::AccountId, value: Self::Balance) -> result::Result<(), &'static str> {
		let b = Self::free_balance(who);
		if b < value {
			return Err("not enough free funds")
		}
		let new_balance = b - value;
		Self::ensure_can_withdraw(who, value, WithdrawReason::Reserve, new_balance)?;
		Self::set_reserved_balance(who, Self::reserved_balance(who) + value);
		Self::set_free_balance(who, new_balance);
		Ok(())
	}

	fn unreserve(who: &T::AccountId, value: Self::Balance) -> Self::Balance {
		let b = Self::reserved_balance(who);
		let actual = cmp::min(b, value);
		Self::set_free_balance(who, Self::free_balance(who) + actual);
		Self::set_reserved_balance(who, b - actual);
		value - actual
	}

	fn slash_reserved(
		who: &T::AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance) {
		let b = Self::reserved_balance(who);
		let slash = cmp::min(b, value);
		// underflow should never happen, but it if does, there's nothing to be done here.
		Self::set_reserved_balance(who, b - slash);
		(NegativeImbalance::new(slash), value - slash)
	}

	fn repatriate_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: Self::Balance,
	) -> result::Result<Self::Balance, &'static str> {
		if Self::total_balance(beneficiary).is_zero() {
			return Err("beneficiary account must pre-exist");
		}
		let b = Self::reserved_balance(slashed);
		let slash = cmp::min(b, value);
		Self::set_free_balance(beneficiary, Self::free_balance(beneficiary) + slash);
		Self::set_reserved_balance(slashed, b - slash);
		Ok(value - slash)
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

/// Require the transactor pay for themselves and maybe include a tip to gain additional priority
/// in the queue.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct TakeFees<T: Trait<I>, I: Instance = DefaultInstance>(#[codec(compact)] T::Balance);

impl<T: Trait<I>, I: Instance> TakeFees<T, I> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(fee: T::Balance) -> Self {
		Self(fee)
	}

	/// Compute the final fee value for a particular transaction.
	///
	/// The final fee is composed of:
	///   - _length-fee_: This is the amount paid merely to pay for size of the transaction.
	///   - _weight-fee_: This amount is computed based on the weight of the transaction. Unlike
	///      size-fee, this is not input dependent and reflects the _complexity_ of the execution
	///      and the time it consumes.
	///   - (optional) _tip_: if included in the transaction, it will be added on top. Only signed
	///      transactions can have a tip.
	fn compute_fee(len: usize, info: DispatchInfo, tip: T::Balance) -> T::Balance {
		let len_fee = if info.pay_length_fee() {
			let len = T::Balance::from(len as u32);
			let base = T::TransactionBaseFee::get();
			let per_byte = T::TransactionByteFee::get();
			base.saturating_add(per_byte.saturating_mul(len))
		} else {
			Zero::zero()
		};

		let weight_fee = {
			// cap the weight to the maximum defined in runtime, otherwise it will be the `Bounded`
			// maximum of its data type, which is not desired.
			let capped_weight = info.weight.min(<T as system::Trait>::MaximumBlockWeight::get());
			let weight_update = <system::Module<T>>::next_weight_multiplier();
			let adjusted_weight = weight_update.apply_to(capped_weight);
			T::WeightToFee::convert(adjusted_weight)
		};

		len_fee.saturating_add(weight_fee).saturating_add(tip)
	}
}

#[cfg(feature = "std")]
impl<T: Trait<I>, I: Instance> rstd::fmt::Debug for TakeFees<T, I> {
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		self.0.fmt(f)
	}
}

impl<T: Trait<I>, I: Instance + Clone + Eq> SignedExtension for TakeFees<T, I> {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	fn additional_signed(&self) -> rstd::result::Result<(), TransactionValidityError> { Ok(()) }

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		// pay any fees.
		let fee = Self::compute_fee(len, info, self.0);
		let imbalance = match <Module<T, I>>::withdraw(
			who,
			fee,
			WithdrawReason::TransactionPayment,
			ExistenceRequirement::KeepAlive,
		) {
			Ok(imbalance) => imbalance,
			Err(_) => return InvalidTransaction::Payment.into(),
		};
		T::TransactionPayment::on_unbalanced(imbalance);

		let mut r = ValidTransaction::default();
		// NOTE: we probably want to maximize the _fee (of any type) per weight unit_ here, which
		// will be a bit more than setting the priority to tip. For now, this is enough.
		r.priority = fee.saturated_into::<TransactionPriority>();
		Ok(r)
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
