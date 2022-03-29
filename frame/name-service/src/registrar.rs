// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use frame_support::{
	pallet_prelude::*,
	traits::{BalanceStatus, ReservableCurrency},
};
use sp_runtime::traits::Zero;

impl<T: Config> Pallet<T> {
	/// Check if an account is authorized to control a name registration.
	pub fn is_owner(registration: &RegistrationOf<T>, user: &T::AccountId) -> bool {
		&registration.owner == user
	}

	/// Check if an account is a controller or owner of this name registration.
	pub fn is_controller(registration: &RegistrationOf<T>, user: &T::AccountId) -> bool {
		&registration.controller == user || Self::is_owner(registration, user)
	}

	pub fn is_expired(registration: &RegistrationOf<T>) -> bool {
		if let Some(expiry) = registration.expiry {
			return expiry < frame_system::Pallet::<T>::block_number()
		} else {
			false
		}
	}

	pub fn get_registration(name_hash: NameHash) -> Result<RegistrationOf<T>, DispatchError> {
		Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound.into())
	}

	/// A function that handles registration of a name hash.
	///
	/// Does not check for an existing registration before overwriting, but does
	/// free any existing deposit if one does exist.
	pub fn do_register(
		name_hash: NameHash,
		owner: T::AccountId,
		controller: T::AccountId,
		maybe_expiration: Option<T::BlockNumber>,
		maybe_deposit: Option<BalanceOf<T>>,
	) -> DispatchResult {
		if let Some(deposit) = maybe_deposit {
			T::Currency::reserve(&owner, deposit)?;
		}

		if let Some(old_registration) = Registrations::<T>::take(name_hash) {
			if let Some(old_deposit) = old_registration.deposit {
				let res = T::Currency::unreserve(&old_registration.owner, old_deposit);
				debug_assert!(res.is_zero());
			}
		}

		let registration = Registration {
			owner: owner.clone(),
			controller,
			expiry: maybe_expiration,
			deposit: maybe_deposit,
		};

		Registrations::<T>::insert(name_hash, registration);
		Self::deposit_event(Event::<T>::NameRegistered { name_hash, owner });
		Ok(())
	}

	pub fn do_deregister(name_hash: NameHash) {
		if let Some(registration) = Registrations::<T>::take(name_hash) {
			if let Some(deposit) = registration.deposit {
				let res = T::Currency::unreserve(&registration.owner, deposit);
				debug_assert!(res.is_zero());
			}
		}

		Resolvers::<T>::remove(name_hash);
		Self::deposit_event(Event::<T>::AddressDeregistered { name_hash });
	}

	/// Transfer ownership of a name registration without any checks.
	///
	/// Will also transfer any deposited amount to the new owner.
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
