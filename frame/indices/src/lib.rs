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

//! An index is a short form of an address. This module handles allocation
//! of indices for a newly created accounts.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::Codec;
use sp_runtime::traits::{
	StaticLookup, Member, LookupError, Zero, Saturating, AtLeast32Bit
};
use frame_support::{Parameter, decl_module, decl_error, decl_event, decl_storage, ensure};
use frame_support::dispatch::DispatchResult;
use frame_support::traits::{Currency, ReservableCurrency, Get, BalanceStatus::Reserved};
use frame_system::{ensure_signed, ensure_root};
use self::address::Address as RawAddress;

mod mock;
pub mod address;
mod tests;

pub type Address<T> = RawAddress<<T as frame_system::Trait>::AccountId, <T as Trait>::AccountIndex>;
type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

/// The module's config trait.
pub trait Trait: frame_system::Trait {
	/// Type used for storing an account's index; implies the maximum number of accounts the system
	/// can hold.
	type AccountIndex: Parameter + Member + Codec + Default + AtLeast32Bit + Copy;

	/// The currency trait.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The deposit needed for reserving an index.
	type Deposit: Get<BalanceOf<Self>>;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Indices {
		/// The lookup from index to account.
		pub Accounts build(|config: &GenesisConfig<T>|
			config.indices.iter()
				.cloned()
				.map(|(a, b)| (a, (b, Zero::zero())))
				.collect::<Vec<_>>()
		): map hasher(blake2_128_concat) T::AccountIndex => Option<(T::AccountId, BalanceOf<T>)>;
	}
	add_extra_genesis {
		config(indices): Vec<(T::AccountIndex, T::AccountId)>;
	}
}

decl_event!(
	pub enum Event<T> where
		<T as frame_system::Trait>::AccountId,
		<T as Trait>::AccountIndex
	{
		/// A account index was assigned.
		IndexAssigned(AccountId, AccountIndex),
		/// A account index has been freed up (unassigned).
		IndexFreed(AccountIndex),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// The index was not already assigned.
		NotAssigned,
		/// The index is assigned to another account.
		NotOwner,
		/// The index was not available.
		InUse,
		/// The source and destination accounts are identical.
		NotTransfer,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		fn deposit_event() = default;

		/// Assign an previously unassigned index.
		///
		/// Payment: `Deposit` is reserved from the sender account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `index`: the index to be claimed. This must not be in use.
		///
		/// Emits `IndexAssigned` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - One reserve operation.
		/// - One event.
		/// # </weight>
		#[weight = 0]
		fn claim(origin, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;

			Accounts::<T>::try_mutate(index, |maybe_value| {
				ensure!(maybe_value.is_none(), Error::<T>::InUse);
				*maybe_value = Some((who.clone(), T::Deposit::get()));
				T::Currency::reserve(&who, T::Deposit::get())
			})?;
			Self::deposit_event(RawEvent::IndexAssigned(who, index));
		}

		/// Assign an index already owned by the sender to another account. The balance reservation
		/// is effectively transferred to the new account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// - `index`: the index to be re-assigned. This must be owned by the sender.
		/// - `new`: the new owner of the index. This function is a no-op if it is equal to sender.
		///
		/// Emits `IndexAssigned` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - One transfer operation.
		/// - One event.
		/// # </weight>
		#[weight = 0]
		fn transfer(origin, new: T::AccountId, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;
			ensure!(who != new, Error::<T>::NotTransfer);

			Accounts::<T>::try_mutate(index, |maybe_value| -> DispatchResult {
				let (account, amount) = maybe_value.take().ok_or(Error::<T>::NotAssigned)?;
				ensure!(&account == &who, Error::<T>::NotOwner);
				let lost = T::Currency::repatriate_reserved(&who, &new, amount, Reserved)?;
				*maybe_value = Some((new.clone(), amount.saturating_sub(lost)));
				Ok(())
			})?;
			Self::deposit_event(RawEvent::IndexAssigned(new, index));
		}

		/// Free up an index owned by the sender.
		///
		/// Payment: Any previous deposit placed for the index is unreserved in the sender account.
		///
		/// The dispatch origin for this call must be _Signed_ and the sender must own the index.
		///
		/// - `index`: the index to be freed. This must be owned by the sender.
		///
		/// Emits `IndexFreed` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - One reserve operation.
		/// - One event.
		/// # </weight>
		#[weight = 0]
		fn free(origin, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;

			Accounts::<T>::try_mutate(index, |maybe_value| -> DispatchResult {
				let (account, amount) = maybe_value.take().ok_or(Error::<T>::NotAssigned)?;
				ensure!(&account == &who, Error::<T>::NotOwner);
				T::Currency::unreserve(&who, amount);
				Ok(())
			})?;
			Self::deposit_event(RawEvent::IndexFreed(index));
		}

		/// Force an index to an account. This doesn't require a deposit. If the index is already
		/// held, then any deposit is reimbursed to its current owner.
		///
		/// The dispatch origin for this call must be _Root_.
		///
		/// - `index`: the index to be (re-)assigned.
		/// - `new`: the new owner of the index. This function is a no-op if it is equal to sender.
		///
		/// Emits `IndexAssigned` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - Up to one reserve operation.
		/// - One event.
		/// # </weight>
		#[weight = 0]
		fn force_transfer(origin, new: T::AccountId, index: T::AccountIndex) {
			ensure_root(origin)?;

			Accounts::<T>::mutate(index, |maybe_value| {
				if let Some((account, amount)) = maybe_value.take() {
					T::Currency::unreserve(&account, amount);
				}
				*maybe_value = Some((new.clone(), Zero::zero()));
			});
			Self::deposit_event(RawEvent::IndexAssigned(new, index));
		}
	}
}

impl<T: Trait> Module<T> {
	// PUBLIC IMMUTABLES

	/// Lookup an T::AccountIndex to get an Id, if there's one there.
	pub fn lookup_index(index: T::AccountIndex) -> Option<T::AccountId> {
		Accounts::<T>::get(index).map(|x| x.0)
	}

	/// Lookup an address to get an Id, if there's one there.
	pub fn lookup_address(
		a: address::Address<T::AccountId, T::AccountIndex>
	) -> Option<T::AccountId> {
		match a {
			address::Address::Id(i) => Some(i),
			address::Address::Index(i) => Self::lookup_index(i),
		}
	}
}

impl<T: Trait> StaticLookup for Module<T> {
	type Source = address::Address<T::AccountId, T::AccountIndex>;
	type Target = T::AccountId;

	fn lookup(a: Self::Source) -> Result<Self::Target, LookupError> {
		Self::lookup_address(a).ok_or(LookupError)
	}

	fn unlookup(a: Self::Target) -> Self::Source {
		address::Address::Id(a)
	}
}
