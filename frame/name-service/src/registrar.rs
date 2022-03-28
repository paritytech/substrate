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
use frame_support::{pallet_prelude::*, traits::ReservableCurrency};
use sp_runtime::traits::Zero;

impl<T: Config> Pallet<T> {
	/// Check if an account is authorized to control a name registration.
	pub fn is_owner(registration: &RegistrationOf<T>, user: T::AccountId) -> bool {
		registration.owner == user
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
	pub fn do_register(
		name_hash: NameHash,
		maybe_registrant: Option<T::AccountId>,
		owner: T::AccountId,
		maybe_expiration: Option<T::BlockNumber>,
		maybe_deposit: Option<BalanceOf<T>>,
	) -> DispatchResult {
		if let Some(deposit) = maybe_deposit {
			T::Currency::reserve(&owner, deposit)?;
		}

		if let Some(old_registration) = Registrations::<T>::take(name_hash) {
			if let Some(deposit) = old_registration.deposit {
				let res = T::Currency::unreserve(&old_registration.owner, deposit);
				debug_assert!(res.is_zero());
			}
		}

		let registration = Registration {
			registrant: maybe_registrant,
			owner: owner.clone(),
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
}
