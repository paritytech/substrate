// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Balances Pallet
//!
//! The Balances pallet provides functionality for handling accounts and balances.
//!
//! - [`Config`]
//! - [`Call`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Balances pallet provides functions for:
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
//! - **Existential Deposit:** The minimum balance required to create or keep an account open. This
//!   prevents "dust accounts" from filling storage. When the free plus the reserved balance (i.e.
//!   the total balance) fall below this, then the account is said to be dead; and it loses its
//!   functionality as well as any prior history and all information on it is removed from the
//!   chain's state. No account should ever have a total balance that is strictly between 0 and the
//!   existential deposit (exclusive). If this ever happens, it indicates either a bug in this
//!   pallet or an erroneous raw mutation of storage.
//!
//! - **Total Issuance:** The total number of units in existence in a system.
//!
//! - **Reaping an account:** The act of removing an account by resetting its nonce. Happens after
//!   its
//! total balance has become zero (or, strictly speaking, less than the Existential Deposit).
//!
//! - **Free Balance:** The portion of a balance that is not reserved. The free balance is the only
//!   balance that matters for most operations.
//!
//! - **Reserved Balance:** Reserved balance still belongs to the account holder, but is suspended.
//!   Reserved balance can still be slashed, but only after all the free balance has been slashed.
//!
//! - **Imbalance:** A condition when some funds were credited or debited without equal and opposite
//!   accounting
//! (i.e. a difference between total issuance and account balances). Functions that result in an
//! imbalance will return an object of the `Imbalance` trait that can be managed within your runtime
//! logic. (If an imbalance is simply dropped, it should automatically maintain any book-keeping
//! such as total issuance.)
//!
//! - **Lock:** A freeze on a specified amount of an account's free balance until a specified block
//!   number. Multiple
//! locks always operate over the same funds, so they "overlay" rather than "stack".
//!
//! ### Implementations
//!
//! The Balances pallet provides implementations for the following traits. If these traits provide
//! the functionality that you need, then you can avoid coupling with the Balances pallet.
//!
//! - [`Currency`](frame_support::traits::Currency): Functions for dealing with a
//! fungible assets system.
//! - [`ReservableCurrency`](frame_support::traits::ReservableCurrency):
//! - [`NamedReservableCurrency`](frame_support::traits::NamedReservableCurrency):
//! Functions for dealing with assets that can be reserved from an account.
//! - [`LockableCurrency`](frame_support::traits::LockableCurrency): Functions for
//! dealing with accounts that allow liquidity restrictions.
//! - [`Imbalance`](frame_support::traits::Imbalance): Functions for handling
//! imbalances between total issuance in the system and account balances. Must be used when a
//! function creates new funds (e.g. a reward) or destroys some funds (e.g. a system fee).
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
//! The following examples show how to use the Balances pallet in your custom pallet.
//!
//! ### Examples from the FRAME
//!
//! The Contract pallet uses the `Currency` trait to handle gas payment, and its types inherit from
//! `Currency`:
//!
//! ```
//! use frame_support::traits::Currency;
//! # pub trait Config: frame_system::Config {
//! # 	type Currency: Currency<Self::AccountId>;
//! # }
//!
//! pub type BalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
//! pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::NegativeImbalance;
//!
//! # fn main() {}
//! ```
//!
//! The Staking pallet uses the `LockableCurrency` trait to lock a stash account's funds:
//!
//! ```
//! use frame_support::traits::{WithdrawReasons, LockableCurrency};
//! use sp_runtime::traits::Bounded;
//! pub trait Config: frame_system::Config {
//! 	type Currency: LockableCurrency<Self::AccountId, Moment=Self::BlockNumber>;
//! }
//! # struct StakingLedger<T: Config> {
//! # 	stash: <T as frame_system::Config>::AccountId,
//! # 	total: <<T as Config>::Currency as frame_support::traits::Currency<<T as frame_system::Config>::AccountId>>::Balance,
//! # 	phantom: std::marker::PhantomData<T>,
//! # }
//! # const STAKING_ID: [u8; 8] = *b"staking ";
//!
//! fn update_ledger<T: Config>(
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
//! The Balances pallet depends on the [`GenesisConfig`].
//!
//! ## Assumptions
//!
//! * Total issued balanced of all accounts should be less than `Config::Balance::max_value()`.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
mod tests;
mod benchmarking;
mod impl_fungible;
mod impl_currency;
pub mod migration;
mod tests_composite;
mod tests_local;
#[cfg(test)]
mod tests_reentrancy;
mod types;
pub mod weights;

use codec::{Codec, Decode, Encode, MaxEncodedLen};
#[cfg(feature = "std")]
use frame_support::traits::GenesisBuild;
use frame_support::{
	ensure,
	pallet_prelude::DispatchResult,
	traits::{
		tokens::{
			fungible, BalanceStatus as Status, DepositConsequence,
			KeepAlive::{CanKill, Keep},
			WithdrawConsequence,
		},
		Currency, Defensive, ExistenceRequirement,
		Get, Imbalance, NamedReservableCurrency, OnUnbalanced,
		ReservableCurrency, StoredMap,
	},
	WeakBoundedVec,
};
use frame_system as system;
pub use impl_currency::{NegativeImbalance, PositiveImbalance};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{
		AtLeast32BitUnsigned, Bounded, CheckedAdd, CheckedSub, MaybeSerializeDeserialize,
		Saturating, StaticLookup, Zero,
	},
	ArithmeticError, DispatchError, FixedPointOperand, RuntimeDebug,
};
use sp_std::{cmp, fmt::Debug, mem, prelude::*, result};
pub use types::{AccountData, BalanceLock, IdAmount, Reasons, ReserveData, DustCleaner};
pub use weights::WeightInfo;

pub use pallet::*;

type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The balance of an account.
		type Balance: Parameter
			+ Member
			+ AtLeast32BitUnsigned
			+ Codec
			+ Default
			+ Copy
			+ MaybeSerializeDeserialize
			+ Debug
			+ MaxEncodedLen
			+ TypeInfo
			+ FixedPointOperand;

		/// Handler for the unbalanced reduction when removing a dust account.
		type DustRemoval: OnUnbalanced<NegativeImbalance<Self, I>>;

		/// The minimum amount required to keep an account open.
		#[pallet::constant]
		type ExistentialDeposit: Get<Self::Balance>;

		/// The means of storing the balances of an account.
		type AccountStore: StoredMap<Self::AccountId, AccountData<Self::Balance>>;

		/// The ID type for reserves. Use of reserves is deprecated.
		type ReserveIdentifier: Parameter + Member + MaxEncodedLen + Ord + Copy;

		/// The ID type for holds.
		type HoldIdentifier: Parameter + Member + MaxEncodedLen + Ord + Copy;

		/// The ID type for freezes.
		type FreezeIdentifier: Parameter + Member + MaxEncodedLen + Ord + Copy;

		/// The maximum number of locks that should exist on an account.
		/// Not strictly enforced, but used for weight estimation.
		#[pallet::constant]
		type MaxLocks: Get<u32>;

		/// The maximum number of named reserves that can exist on an account.
		#[pallet::constant]
		type MaxReserves: Get<u32>;

		/// The maximum number of holds that can exist on an account at any time.
		#[pallet::constant]
		type MaxHolds: Get<u32>;

		/// The maximum number of individual freeze locks that can exist on an account at any time.
		#[pallet::constant]
		type MaxFreezes: Get<u32>;
	}

	/// The current storage version.
	const STORAGE_VERSION: frame_support::traits::StorageVersion =
		frame_support::traits::StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T, I = ()>(PhantomData<(T, I)>);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// An account was created with some free balance.
		Endowed { account: T::AccountId, free_balance: T::Balance },
		/// An account was removed whose balance was non-zero but below ExistentialDeposit,
		/// resulting in an outright loss.
		DustLost { account: T::AccountId, amount: T::Balance },
		/// Transfer succeeded.
		Transfer { from: T::AccountId, to: T::AccountId, amount: T::Balance },
		/// A balance was set by root.
		BalanceSet { who: T::AccountId, free: T::Balance },
		/// Some balance was reserved (moved from free to reserved).
		Reserved { who: T::AccountId, amount: T::Balance },
		/// Some balance was unreserved (moved from reserved to free).
		Unreserved { who: T::AccountId, amount: T::Balance },
		/// Some balance was moved from the reserve of the first account to the second account.
		/// Final argument indicates the destination balance type.
		ReserveRepatriated {
			from: T::AccountId,
			to: T::AccountId,
			amount: T::Balance,
			destination_status: Status,
		},
		/// Some amount was deposited (e.g. for transaction fees).
		Deposit { who: T::AccountId, amount: T::Balance },
		/// Some amount was withdrawn from the account (e.g. for transaction fees).
		Withdraw { who: T::AccountId, amount: T::Balance },
		/// Some amount was removed from the account (e.g. for misbehavior).
		Slashed { who: T::AccountId, amount: T::Balance },
		/// Some amount was minted into an account.
		Minted { who: T::AccountId, amount: T::Balance },
		/// Some amount was burned from an account.
		Burned { who: T::AccountId, amount: T::Balance },
		/// Some amount was suspended from an account (it can be restored later).
		Suspended { who: T::AccountId, amount: T::Balance },
		/// Some amount was restored into an account.
		Restored { who: T::AccountId, amount: T::Balance },
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// Vesting balance too high to send value
		VestingBalance,
		/// Account liquidity restrictions prevent withdrawal
		LiquidityRestrictions,
		/// Balance too low to send value.
		InsufficientBalance,
		/// Value too low to create account due to existential deposit
		ExistentialDeposit,
		/// Transfer/payment would kill account
		KeepAlive,
		/// A vesting schedule already exists for this account
		ExistingVestingSchedule,
		/// Beneficiary account must pre-exist
		DeadAccount,
		/// Number of named reserves exceed MaxReserves
		TooManyReserves,
		/// Number of named reserves exceed MaxHolds
		TooManyHolds,
	}

	/// The total units issued in the system.
	#[pallet::storage]
	#[pallet::getter(fn total_issuance)]
	#[pallet::whitelist_storage]
	pub type TotalIssuance<T: Config<I>, I: 'static = ()> = StorageValue<_, T::Balance, ValueQuery>;

	/// The total units of outstanding deactivated balance in the system.
	#[pallet::storage]
	#[pallet::getter(fn inactive_issuance)]
	#[pallet::whitelist_storage]
	pub type InactiveIssuance<T: Config<I>, I: 'static = ()> =
		StorageValue<_, T::Balance, ValueQuery>;

	/// The Balances pallet example of storing the balance of an account.
	///
	/// # Example
	///
	/// ```nocompile
	///  impl pallet_balances::Config for Runtime {
	///    type AccountStore = StorageMapShim<Self::Account<Runtime>, frame_system::Provider<Runtime>, AccountId, Self::AccountData<Balance>>
	///  }
	/// ```
	///
	/// You can also store the balance of an account in the `System` pallet.
	///
	/// # Example
	///
	/// ```nocompile
	///  impl pallet_balances::Config for Runtime {
	///   type AccountStore = System
	///  }
	/// ```
	///
	/// But this comes with tradeoffs, storing account balances in the system pallet stores
	/// `frame_system` data alongside the account data contrary to storing account balances in the
	/// `Balances` pallet, which uses a `StorageMap` to store balances data only.
	/// NOTE: This is only used in the case that this pallet is used to store balances.
	#[pallet::storage]
	pub type Account<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, T::AccountId, AccountData<T::Balance>, ValueQuery>;

	/// Any liquidity locks on some account balances.
	/// NOTE: Should only be accessed when setting, changing and freeing a lock.
	#[pallet::storage]
	#[pallet::getter(fn locks)]
	pub type Locks<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		WeakBoundedVec<BalanceLock<T::Balance>, T::MaxLocks>,
		ValueQuery,
	>;

	/// Named reserves on some account balances.
	#[pallet::storage]
	#[pallet::getter(fn reserves)]
	pub type Reserves<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		BoundedVec<ReserveData<T::ReserveIdentifier, T::Balance>, T::MaxReserves>,
		ValueQuery,
	>;

	/// Holds on account balances.
	#[pallet::storage]
	pub type Holds<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		BoundedVec<IdAmount<T::HoldIdentifier, T::Balance>, T::MaxHolds>,
		ValueQuery,
	>;

	/// Freeze locks on account balances.
	#[pallet::storage]
	pub type Freezes<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		BoundedVec<IdAmount<T::FreezeIdentifier, T::Balance>, T::MaxFreezes>,
		ValueQuery,
	>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub balances: Vec<(T::AccountId, T::Balance)>,
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self { balances: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			let total = self.balances.iter().fold(Zero::zero(), |acc: T::Balance, &(_, n)| acc + n);
			<TotalIssuance<T, I>>::put(total);

			for (_, balance) in &self.balances {
				assert!(
					*balance >= <T as Config<I>>::ExistentialDeposit::get(),
					"the balance of any account should always be at least the existential deposit.",
				)
			}

			// ensure no duplicates exist.
			let endowed_accounts = self
				.balances
				.iter()
				.map(|(x, _)| x)
				.cloned()
				.collect::<std::collections::BTreeSet<_>>();

			assert!(
				endowed_accounts.len() == self.balances.len(),
				"duplicate balances in genesis."
			);

			for &(ref who, free) in self.balances.iter() {
				frame_system::Pallet::<T>::inc_providers(who);
				assert!(T::AccountStore::insert(who, AccountData { free, ..Default::default() })
					.is_ok());
			}
		}
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> GenesisConfig<T, I> {
		/// Direct implementation of `GenesisBuild::build_storage`.
		///
		/// Kept in order not to break dependency.
		pub fn build_storage(&self) -> Result<sp_runtime::Storage, String> {
			<Self as GenesisBuild<T, I>>::build_storage(self)
		}

		/// Direct implementation of `GenesisBuild::assimilate_storage`.
		///
		/// Kept in order not to break dependency.
		pub fn assimilate_storage(&self, storage: &mut sp_runtime::Storage) -> Result<(), String> {
			<Self as GenesisBuild<T, I>>::assimilate_storage(self, storage)
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Transfer some liquid free balance to another account.
		///
		/// `transfer` will set the `FreeBalance` of the sender and receiver.
		/// If the sender's account is below the existential deposit as a result
		/// of the transfer, the account will be reaped.
		///
		/// The dispatch origin for this call must be `Signed` by the transactor.
		///
		/// # <weight>
		/// - Dependent on arguments but not critical, given proper implementations for input config
		///   types. See related functions below.
		/// - It contains a limited number of reads and writes internally and no complex
		///   computation.
		///
		/// Related functions:
		///
		///   - `ensure_can_withdraw` is always called internally but has a bounded complexity.
		///   - Transferring balances to accounts that did not exist before will cause
		///     `T::OnNewAccount::on_new_account` to be called.
		///   - Removing enough funds from an account will trigger `T::DustRemoval::on_unbalanced`.
		///   - `transfer_keep_alive` works the same way as `transfer`, but has an additional check
		///     that the transfer will not kill the origin account.
		/// ---------------------------------
		/// - Origin account is already in memory, so no DB operations for them.
		/// # </weight>
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::transfer())]
		pub fn transfer(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			#[pallet::compact] value: T::Balance,
		) -> DispatchResultWithPostInfo {
			let source = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as fungible::Mutate<_>>::transfer(&source, &dest, value, CanKill)?;
			Ok(().into())
		}

		/// Set the balances of a given account.
		///
		/// This will alter `FreeBalance` and `ReservedBalance` in storage. it will
		/// also alter the total issuance of the system (`TotalIssuance`) appropriately.
		/// If the new free or reserved balance is below the existential deposit,
		/// it will reset the account nonce (`frame_system::AccountNonce`).
		///
		/// The dispatch origin for this call is `root`.
		#[pallet::call_index(1)]
		#[pallet::weight(
			T::WeightInfo::set_balance_creating() // Creates a new account.
				.max(T::WeightInfo::set_balance_killing()) // Kills an existing account.
		)]
		pub fn set_balance(
			origin: OriginFor<T>,
			who: AccountIdLookupOf<T>,
			#[pallet::compact] new_free: T::Balance,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;
			let existential_deposit = T::ExistentialDeposit::get();

			let wipeout = new_free < existential_deposit;
			let new_free = if wipeout { Zero::zero() } else { new_free };

			// First we try to modify the account's balance to the forced balance.
			let old_free = Self::mutate_account(&who, |account| {
				let old_free = account.free;
				account.free = new_free;
				old_free
			})?;

			// This will adjust the total issuance, which was not done by the `mutate_account`
			// above.
			if new_free > old_free {
				mem::drop(PositiveImbalance::<T, I>::new(new_free - old_free));
			} else if new_free < old_free {
				mem::drop(NegativeImbalance::<T, I>::new(old_free - new_free));
			}

			Self::deposit_event(Event::BalanceSet { who, free: new_free });
			Ok(().into())
		}

		/// Exactly as `transfer`, except the origin must be root and the source account may be
		/// specified.
		/// # <weight>
		/// - Same as transfer, but additional read and write because the source account is not
		///   assumed to be in the overlay.
		/// # </weight>
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::force_transfer())]
		pub fn force_transfer(
			origin: OriginFor<T>,
			source: AccountIdLookupOf<T>,
			dest: AccountIdLookupOf<T>,
			#[pallet::compact] value: T::Balance,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let source = T::Lookup::lookup(source)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as fungible::Mutate<_>>::transfer(&source, &dest, value, CanKill)?;
			Ok(().into())
		}

		/// Same as the [`transfer`] call, but with a check that the transfer will not kill the
		/// origin account.
		///
		/// 99% of the time you want [`transfer`] instead.
		///
		/// [`transfer`]: struct.Pallet.html#method.transfer
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::transfer_keep_alive())]
		pub fn transfer_keep_alive(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			#[pallet::compact] value: T::Balance,
		) -> DispatchResultWithPostInfo {
			let source = ensure_signed(origin)?;
			let dest = T::Lookup::lookup(dest)?;
			<Self as fungible::Mutate<_>>::transfer(&source, &dest, value, Keep)?;
			Ok(().into())
		}

		/// Transfer the entire transferable balance from the caller account.
		///
		/// NOTE: This function only attempts to transfer _transferable_ balances. This means that
		/// any locked, reserved, or existential deposits (when `keep_alive` is `true`), will not be
		/// transferred by this function. To ensure that this function results in a killed account,
		/// you might need to prepare the account by removing any reference counters, storage
		/// deposits, etc...
		///
		/// The dispatch origin of this call must be Signed.
		///
		/// - `dest`: The recipient of the transfer.
		/// - `keep_alive`: A boolean to determine if the `transfer_all` operation should send all
		///   of the funds the account has, causing the sender account to be killed (false), or
		///   transfer everything except at least the existential deposit, which will guarantee to
		///   keep the sender account alive (true). # <weight>
		/// - O(1). Just like transfer, but reading the user's transferable balance first.
		///   #</weight>
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::transfer_all())]
		pub fn transfer_all(
			origin: OriginFor<T>,
			dest: AccountIdLookupOf<T>,
			keep_alive: bool,
		) -> DispatchResult {
			let transactor = ensure_signed(origin)?;
			let keep_alive = if keep_alive { Keep } else { CanKill };
			let reducible_balance =
				<Self as fungible::Inspect<_>>::reducible_balance(&transactor, keep_alive, false);
			let dest = T::Lookup::lookup(dest)?;
			<Self as fungible::Mutate<_>>::transfer(
				&transactor,
				&dest,
				reducible_balance,
				keep_alive,
			)?;
			Ok(())
		}

		/// Unreserve some balance from a user by force.
		///
		/// Can only be called by ROOT.
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::force_unreserve())]
		pub fn force_unreserve(
			origin: OriginFor<T>,
			who: AccountIdLookupOf<T>,
			amount: T::Balance,
		) -> DispatchResult {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;
			let _leftover = <Self as ReservableCurrency<_>>::unreserve(&who, amount);
			Ok(())
		}
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Ensure the account `who` is using the new logic.
	pub fn ensure_upgraded(who: &T::AccountId) {
		let mut a = Self::account(who);
		if a.flags.is_new_logic() {
			return
		}
		a.flags.set_new_logic();
		if !a.reserved.is_zero() {
			if !system::Pallet::<T>::can_inc_consumer(who) {
				// Gah!! We have a non-zero reserve balance but no provider refs :(
				// This shouldn't practically happen, but we need a failsafe anyway: let's give
				// them enough for an ED.
				a.free = a.free.min(T::ExistentialDeposit::get());
				system::Pallet::<T>::inc_providers(who);
			}
			let _ = system::Pallet::<T>::inc_consumers(who).defensive();
		}
		// Should never fail - we're only setting a bit.
		let _ = Self::mutate_account(who, |account| *account = a);
	}

	/// Get the free balance of an account.
	pub fn free_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Self::account(who.borrow()).free
	}

	/// Get the balance of an account that can be used for transfers, reservations, or any other
	/// non-locking, non-transaction-fee activity. Will be at most `free_balance`.
	pub fn usable_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		// TODO: use fungible::Inspect
		Self::account(who.borrow()).usable()
	}

	/// Get the balance of an account that can be used for paying transaction fees (not tipping,
	/// or any other kind of fees, though). Will be at most `free_balance`.
	pub fn usable_balance_for_fees(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Self::account(who.borrow()).usable()
	}

	/// Get the reserved balance of an account.
	pub fn reserved_balance(who: impl sp_std::borrow::Borrow<T::AccountId>) -> T::Balance {
		Self::account(who.borrow()).reserved
	}

	/// Get both the free and reserved balances of an account.
	fn account(who: &T::AccountId) -> AccountData<T::Balance> {
		T::AccountStore::get(who)
	}

	/// Handles any steps needed after mutating an account.
	///
	/// This includes DustRemoval unbalancing, in the case than the `new` account's total balance
	/// is non-zero but below ED.
	///
	/// Returns two values:
	/// - `Some` containing the the `new` account, iff the account has sufficient balance.
	/// - `Some` containing the dust to be dropped, iff some dust should be dropped.
	fn post_mutation(
		_who: &T::AccountId,
		new: AccountData<T::Balance>,
	) -> (Option<AccountData<T::Balance>>, Option<NegativeImbalance<T, I>>) {
		// We should never be dropping if reserved is non-zero. Reserved being non-zero should imply
		// that we have a consumer ref, so this is economically safe.
		if new.free < T::ExistentialDeposit::get() && new.reserved.is_zero() {
			if new.free.is_zero() {
				(None, None)
			} else {
				(None, Some(NegativeImbalance::new(new.free)))
			}
		} else {
			(Some(new), None)
		}
	}

	/// Mutate an account to some new value, or delete it entirely with `None`. Will enforce
	/// `ExistentialDeposit` law, annulling the account as needed.
	///
	/// NOTE: Doesn't do any preparatory work for creating a new account, so should only be used
	/// when it is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	pub fn mutate_account<R>(
		who: &T::AccountId,
		f: impl FnOnce(&mut AccountData<T::Balance>) -> R,
	) -> Result<R, DispatchError> {
		Self::try_mutate_account(who, |a, _| -> Result<R, DispatchError> { Ok(f(a)) })
	}

	/// Mutate an account to some new value, or delete it entirely with `None`. Will enforce
	/// `ExistentialDeposit` law, annulling the account as needed. This will do nothing if the
	/// result of `f` is an `Err`.
	///
	/// NOTE: Doesn't do any preparatory work for creating a new account, so should only be used
	/// when it is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn try_mutate_account<R, E: From<DispatchError>>(
		who: &T::AccountId,
		f: impl FnOnce(&mut AccountData<T::Balance>, bool) -> Result<R, E>,
	) -> Result<R, E> {
		Self::try_mutate_account_with_dust(who, f).map(|(result, dust_cleaner)| {
			drop(dust_cleaner);
			result
		})
	}

	/// Mutate an account to some new value, or delete it entirely with `None`. Will enforce
	/// `ExistentialDeposit` law, annulling the account as needed. This will do nothing if the
	/// result of `f` is an `Err`.
	///
	/// It returns both the result from the closure, and an optional `DustCleaner` instance which
	/// should be dropped once it is known that all nested mutates that could affect storage items
	/// what the dust handler touches have completed.
	///
	/// NOTE: Doesn't do any preparatory work for creating a new account, so should only be used
	/// when it is known that the account already exists.
	///
	/// NOTE: LOW-LEVEL: This will not attempt to maintain total issuance. It is expected that
	/// the caller will do this.
	fn try_mutate_account_with_dust<R, E: From<DispatchError>>(
		who: &T::AccountId,
		f: impl FnOnce(&mut AccountData<T::Balance>, bool) -> Result<R, E>,
	) -> Result<(R, DustCleaner<T, I>), E> {
		let result = T::AccountStore::try_mutate_exists(who, |maybe_account| {
			let is_new = maybe_account.is_none();
			let mut account = maybe_account.take().unwrap_or_default();
			let did_provide = account.free >= T::ExistentialDeposit::get();
			let did_consume = !is_new && !account.reserved.is_zero();

			let result = f(&mut account, is_new)?;

			let does_provide = account.free >= T::ExistentialDeposit::get();
			let does_consume = !account.reserved.is_zero();

			if !did_provide && does_provide {
				frame_system::Pallet::<T>::inc_providers(who);
			}
			if did_consume && !does_consume {
				frame_system::Pallet::<T>::dec_consumers(who);
			}
			if !did_consume && does_consume {
				frame_system::Pallet::<T>::inc_consumers(who)?;
			}
			if did_provide && !does_provide {
				// This could reap the account so must go last.
				frame_system::Pallet::<T>::dec_providers(who).map_err(|r| {
					if did_consume && !does_consume {
						// best-effort revert consumer change.
						let _ = frame_system::Pallet::<T>::inc_consumers(who).defensive();
					}
					if !did_consume && does_consume {
						let _ = frame_system::Pallet::<T>::dec_consumers(who);
					}
					r
				})?;
			}

			let maybe_endowed = if is_new { Some(account.free) } else { None };
			let maybe_account_maybe_dust = Self::post_mutation(who, account);
			*maybe_account = maybe_account_maybe_dust.0;
			if let Some(ref account) = &maybe_account {
				assert!(
					account.free.is_zero() ||
						account.free >= T::ExistentialDeposit::get() ||
						!account.reserved.is_zero()
				);
			}
			Ok((maybe_endowed, maybe_account_maybe_dust.1, result))
		});
		result.map(|(maybe_endowed, maybe_dust, result)| {
			if let Some(endowed) = maybe_endowed {
				Self::deposit_event(Event::Endowed { account: who.clone(), free_balance: endowed });
			}
			let dust_cleaner = DustCleaner(maybe_dust.map(|dust| (who.clone(), dust)));
			(result, dust_cleaner)
		})
	}

	/// Update the account entry for `who`, given the locks.
	fn update_locks(who: &T::AccountId, locks: &[BalanceLock<T::Balance>]) {
		let bounded_locks = WeakBoundedVec::<_, T::MaxLocks>::force_from(
			locks.to_vec(),
			Some("Balances Update Locks"),
		);

		if locks.len() as u32 > T::MaxLocks::get() {
			log::warn!(
				target: "runtime::balances",
				"Warning: A user has more currency locks than expected. \
				A runtime configuration adjustment may be needed."
			);
		}
		let freezes = Freezes::<T, I>::get(who);
		// No way this can fail since we do not alter the existential balances.
		let res = Self::mutate_account(who, |b| {
			b.frozen = Zero::zero();
			for l in locks.iter() {
				b.frozen = b.frozen.max(l.amount);
			}
			for l in freezes.iter() {
				b.frozen = b.frozen.max(l.amount);
			}
		});
		debug_assert!(res.is_ok());

		let existed = Locks::<T, I>::contains_key(who);
		if locks.is_empty() {
			Locks::<T, I>::remove(who);
			if existed {
				// TODO: use Locks::<T, I>::hashed_key
				// https://github.com/paritytech/substrate/issues/4969
				system::Pallet::<T>::dec_consumers(who);
			}
		} else {
			Locks::<T, I>::insert(who, bounded_locks);
			if !existed && system::Pallet::<T>::inc_consumers_without_limit(who).is_err() {
				// No providers for the locks. This is impossible under normal circumstances
				// since the funds that are under the lock will themselves be stored in the
				// account and therefore will need a reference.
				log::warn!(
					target: "runtime::balances",
					"Warning: Attempt to introduce lock consumer reference, yet no providers. \
					This is unexpected but should be safe."
				);
			}
		}
	}

	/// Move the reserved balance of one account into the balance of another, according to `status`.
	///
	/// Is a no-op if:
	/// - the value to be moved is zero; or
	/// - the `slashed` id equal to `beneficiary` and the `status` is `Reserved`.
	///
	/// NOTE: returns actual amount of transferred value in `Ok` case.
	fn do_transfer_reserved(
		slashed: &T::AccountId,
		beneficiary: &T::AccountId,
		value: T::Balance,
		best_effort: bool,
		status: Status,
	) -> Result<T::Balance, DispatchError> {
		if value.is_zero() {
			return Ok(Zero::zero())
		}

		if slashed == beneficiary {
			return match status {
				Status::Free => Ok(value.saturating_sub(Self::unreserve(slashed, value))),
				Status::Reserved => Ok(value.saturating_sub(Self::reserved_balance(slashed))),
			}
		}

		let ((actual, _maybe_one_dust), _maybe_other_dust) = Self::try_mutate_account_with_dust(
			beneficiary,
			|to_account, is_new| -> Result<(T::Balance, DustCleaner<T, I>), DispatchError> {
				ensure!(!is_new, Error::<T, I>::DeadAccount);
				Self::try_mutate_account_with_dust(
					slashed,
					|from_account, _| -> Result<T::Balance, DispatchError> {
						let actual = cmp::min(from_account.reserved, value);
						ensure!(best_effort || actual == value, Error::<T, I>::InsufficientBalance);
						match status {
							Status::Free =>
								to_account.free = to_account
									.free
									.checked_add(&actual)
									.ok_or(ArithmeticError::Overflow)?,
							Status::Reserved =>
								to_account.reserved = to_account
									.reserved
									.checked_add(&actual)
									.ok_or(ArithmeticError::Overflow)?,
						}
						from_account.reserved -= actual;
						Ok(actual)
					},
				)
			},
		)?;

		Self::deposit_event(Event::ReserveRepatriated {
			from: slashed.clone(),
			to: beneficiary.clone(),
			amount: actual,
			destination_status: status,
		});
		Ok(actual)
	}
}
