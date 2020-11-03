// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! An index is a short form of an address. This module handles allocation
//! of indices for a newly created accounts.

#![cfg_attr(not(feature = "std"), no_std)]

mod mock;
pub mod address;
mod tests;
mod benchmarking;
pub mod weights;

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
pub use weights::WeightInfo;

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

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

decl_storage! {
	trait Store for Module<T: Trait> as Indices {
		/// The lookup from index to account.
		pub Accounts build(|config: &GenesisConfig<T>|
			config.indices.iter()
				.cloned()
				.map(|(a, b)| (a, (b, Zero::zero(), false)))
				.collect::<Vec<_>>()
		): map hasher(blake2_128_concat) T::AccountIndex => Option<(T::AccountId, BalanceOf<T>, bool)>;
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
		/// A account index was assigned. \[who, index\]
		IndexAssigned(AccountId, AccountIndex),
		/// A account index has been freed up (unassigned). \[index\]
		IndexFreed(AccountIndex),
		/// A account index has been frozen to its current account ID. \[who, index\]
		IndexFrozen(AccountIndex, AccountId),
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
		/// The index is permanent and may not be freed/changed.
		Permanent,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin, system = frame_system {
		/// The deposit needed for reserving an index.
		const Deposit: BalanceOf<T> = T::Deposit::get();

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
		/// -------------------
		/// - DB Weight: 1 Read/Write (Accounts)
		/// # </weight>
		#[weight = T::WeightInfo::claim()]
		fn claim(origin, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;

			Accounts::<T>::try_mutate(index, |maybe_value| {
				ensure!(maybe_value.is_none(), Error::<T>::InUse);
				*maybe_value = Some((who.clone(), T::Deposit::get(), false));
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
		/// -------------------
		/// - DB Weight:
		///    - Reads: Indices Accounts, System Account (recipient)
		///    - Writes: Indices Accounts, System Account (recipient)
		/// # </weight>
		#[weight = T::WeightInfo::transfer()]
		fn transfer(origin, new: T::AccountId, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;
			ensure!(who != new, Error::<T>::NotTransfer);

			Accounts::<T>::try_mutate(index, |maybe_value| -> DispatchResult {
				let (account, amount, perm) = maybe_value.take().ok_or(Error::<T>::NotAssigned)?;
				ensure!(!perm, Error::<T>::Permanent);
				ensure!(&account == &who, Error::<T>::NotOwner);
				let lost = T::Currency::repatriate_reserved(&who, &new, amount, Reserved)?;
				*maybe_value = Some((new.clone(), amount.saturating_sub(lost), false));
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
		/// -------------------
		/// - DB Weight: 1 Read/Write (Accounts)
		/// # </weight>
		#[weight = T::WeightInfo::free()]
		fn free(origin, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;

			Accounts::<T>::try_mutate(index, |maybe_value| -> DispatchResult {
				let (account, amount, perm) = maybe_value.take().ok_or(Error::<T>::NotAssigned)?;
				ensure!(!perm, Error::<T>::Permanent);
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
		/// - `freeze`: if set to `true`, will freeze the index so it cannot be transferred.
		///
		/// Emits `IndexAssigned` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - Up to one reserve operation.
		/// - One event.
		/// -------------------
		/// - DB Weight:
		///    - Reads: Indices Accounts, System Account (original owner)
		///    - Writes: Indices Accounts, System Account (original owner)
		/// # </weight>
		#[weight = T::WeightInfo::force_transfer()]
		fn force_transfer(origin, new: T::AccountId, index: T::AccountIndex, freeze: bool) {
			ensure_root(origin)?;

			Accounts::<T>::mutate(index, |maybe_value| {
				if let Some((account, amount, _)) = maybe_value.take() {
					T::Currency::unreserve(&account, amount);
				}
				*maybe_value = Some((new.clone(), Zero::zero(), freeze));
			});
			Self::deposit_event(RawEvent::IndexAssigned(new, index));
		}

		/// Freeze an index so it will always point to the sender account. This consumes the deposit.
		///
		/// The dispatch origin for this call must be _Signed_ and the signing account must have a
		/// non-frozen account `index`.
		///
		/// - `index`: the index to be frozen in place.
		///
		/// Emits `IndexFrozen` if successful.
		///
		/// # <weight>
		/// - `O(1)`.
		/// - One storage mutation (codec `O(1)`).
		/// - Up to one slash operation.
		/// - One event.
		/// -------------------
		/// - DB Weight: 1 Read/Write (Accounts)
		/// # </weight>
		#[weight = T::WeightInfo::freeze()]
		fn freeze(origin, index: T::AccountIndex) {
			let who = ensure_signed(origin)?;

			Accounts::<T>::try_mutate(index, |maybe_value| -> DispatchResult {
				let (account, amount, perm) = maybe_value.take().ok_or(Error::<T>::NotAssigned)?;
				ensure!(!perm, Error::<T>::Permanent);
				ensure!(&account == &who, Error::<T>::NotOwner);
				T::Currency::slash_reserved(&who, amount);
				*maybe_value = Some((account, Zero::zero(), true));
				Ok(())
			})?;
			Self::deposit_event(RawEvent::IndexFrozen(index, who));
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
