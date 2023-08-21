// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Handles basic registration and deregistration of names.

use crate::{types::*, *};
use frame_support::traits::{BalanceStatus, ReservableCurrency};
use frame_system::pallet_prelude::BlockNumberFor;
use sp_runtime::traits::Zero;

impl<T: Config> Pallet<T> {
	/// Check if an account is authorized to control a name registration.
	pub fn is_owner(registration: &RegistrationOf<T>, user: &T::AccountId) -> bool {
		&registration.owner == user
	}

	/// Returns whether a provided rgistration has expired.
	pub fn is_expired(registration: &RegistrationOf<T>) -> bool {
		if let Some(expiry) = registration.expiry {
			return expiry < frame_system::Pallet::<T>::block_number()
		} else {
			false
		}
	}

	/// Gets the registration of a name hash, or returns an error if none exist.
	pub fn get_registration(name_hash: NameHash) -> Result<RegistrationOf<T>, DispatchError> {
		Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound.into())
	}

	/// Reserves a deposit if one is given.
	///
	/// Returns an error if the owner does not have enough to reserve the deposit.
	pub fn reserve_deposit(
		maybe_deposit: Option<BalanceOf<T>>,
		who: &T::AccountId,
	) -> DispatchResult {
		if let Some(deposit) = maybe_deposit {
			T::Currency::reserve(&who, deposit)?;
		}
		Ok(())
	}

	/// Handling of a name hash registration.
	///
	/// Notes:
	/// * Does not check for an existing registration before overwriting, but does free any existing
	///   deposit if one exists.
	/// * Does not assume any expiry is being set, and does not force an expiry.
	/// * Does not assume any deposit is being reserved, and does not force a deposit.
	pub fn do_register(
		name_hash: NameHash,
		owner: T::AccountId,
		maybe_expiration: Option<BlockNumberFor<T>>,
		maybe_deposit: Option<BalanceOf<T>>,
	) -> DispatchResult {
		if let Some(old_registration) = Registrations::<T>::take(name_hash) {
			if let Some(old_deposit) = old_registration.deposit {
				let res = T::Currency::unreserve(&old_registration.owner, old_deposit);
				debug_assert!(res.is_zero());
			}
		}
		Registrations::<T>::insert(
			name_hash,
			Registration { owner: owner.clone(), expiry: maybe_expiration, deposit: maybe_deposit },
		);
		Self::deposit_event(Event::<T>::NameRegistered { name_hash, owner });
		Ok(())
	}

	/// Handling of a name hash de-registration.
	///
	/// Notes:
	/// * Does not assume the registration exists, and does not return an error if no registration
	///   exists.
	/// * Ensures records pertaining to the hash are removed from all resolvers.
	pub fn do_deregister(name_hash: NameHash) {
		if let Some(registration) = Registrations::<T>::take(name_hash) {
			if let Some(deposit) = registration.deposit {
				let res = T::Currency::unreserve(&registration.owner, deposit);
				debug_assert!(res.is_zero());
			}
		}
		// Clean up all resolvers.
		AddressResolver::<T>::remove(name_hash);
		if let Some(name) = NameResolver::<T>::take(name_hash) {
			let res = T::Currency::unreserve(&name.depositor, name.deposit);
			debug_assert!(res.is_zero())
		}
		if let Some(text) = TextResolver::<T>::take(name_hash) {
			let res = T::Currency::unreserve(&text.depositor, text.deposit);
			debug_assert!(res.is_zero())
		}

		Self::deposit_event(Event::<T>::AddressDeregistered { name_hash });
	}

	/// Transfer ownership of a name registration without any ownership checks.
	///
	/// Transfers any deposited amount of the name hash to the new owner.
	pub fn do_transfer_ownership(name_hash: NameHash, new_owner: T::AccountId) -> DispatchResult {
		Registrations::<T>::try_mutate(name_hash, |maybe_registration| {
			let r = maybe_registration.as_mut().ok_or(Error::<T>::RegistrationNotFound)?;
			let old_owner = r.owner.clone();

			if let Some(deposit) = r.deposit {
				T::Currency::repatriate_reserved(
					&old_owner,
					&new_owner,
					deposit,
					BalanceStatus::Reserved,
				)?;
			}

			r.owner = new_owner.clone();
			Self::deposit_event(Event::<T>::NewOwner { from: old_owner, to: new_owner });
			Ok(())
		})
	}
}
