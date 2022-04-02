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

//! Handles the mapping of a name registration to an name record.

use crate::{types::*, *};
use frame_support::{pallet_prelude::*, traits::ReservableCurrency};

pub trait NameServiceResolver<T: Config> {
	/// Get the native address associated with this name hash.
	fn get_address(name_hash: NameHash) -> Option<T::AccountId>;
	/// Set the native address associated with this name hash.
	fn set_address(
		name_hash: NameHash,
		address: T::AccountId,
		depositor: T::AccountId,
	) -> DispatchResult;

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: NameHash) -> Option<BoundedNameOf<T>>;
	/// Set the unhashed name associated with this name hash.
	fn set_name(
		name_hash: NameHash,
		name: BoundedNameOf<T>,
		depositor: T::AccountId,
	) -> DispatchResult;

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: NameHash) -> Option<BoundedTextOf<T>>;
	/// Set the arbitrary text associated with this name hash.
	fn set_text(
		name_hash: NameHash,
		text: BoundedTextOf<T>,
		depositor: T::AccountId,
	) -> DispatchResult;
}

impl<T: Config> NameServiceResolver<T> for Pallet<T> {
	/// Get the native address associated with this name hash.
	fn get_address(name_hash: NameHash) -> Option<T::AccountId> {
		AddressResolver::<T>::get(name_hash)
	}
	/// Set the native address associated with this name hash.
	///
	/// We allow a user to set this value without paying any additional deposits.
	fn set_address(
		name_hash: NameHash,
		address: T::AccountId,
		_depositor: T::AccountId,
	) -> DispatchResult {
		AddressResolver::<T>::insert(name_hash, address.clone());
		Self::deposit_event(Event::<T>::AddressSet { name_hash, address });
		Ok(())
	}

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: NameHash) -> Option<BoundedNameOf<T>> {
		NameResolver::<T>::get(name_hash).map(|name| name.bytes)
	}
	/// Set the unhashed name associated with this name hash.
	///
	/// We verify the name matches the hash before committing the name to storage.
	fn set_name(
		name_hash: NameHash,
		name: BoundedNameOf<T>,
		depositor: T::AccountId,
	) -> DispatchResult {
		let hashed_name = Self::name_hash(&name);
		ensure!(name_hash == hashed_name, Error::<T>::BadName);
		ensure!(!NameResolver::<T>::contains_key(name_hash), Error::<T>::RegistrationExists);

		let deposit = Self::bytes_to_fee(&name);
		T::Currency::reserve(&depositor, deposit)?;

		let name_storage = BytesStorage { bytes: name, depositor, deposit };

		NameResolver::<T>::insert(name_hash, name_storage);
		Self::deposit_event(Event::<T>::NameSet { name_hash });
		Ok(())
	}

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: NameHash) -> Option<BoundedTextOf<T>> {
		TextResolver::<T>::get(name_hash).map(|text| text.bytes)
	}
	/// Set the arbitrary text associated with this name hash.
	fn set_text(
		name_hash: NameHash,
		text: BoundedTextOf<T>,
		depositor: T::AccountId,
	) -> DispatchResult {
		let deposit = Self::bytes_to_fee(&text);
		T::Currency::reserve(&depositor, deposit)?;

		let maybe_old_text = TextResolver::<T>::get(name_hash);
		if let Some(old_text) = maybe_old_text {
			T::Currency::unreserve(&old_text.depositor, old_text.deposit);
		}

		let text_storage = BytesStorage { bytes: text, depositor, deposit };

		TextResolver::<T>::insert(name_hash, text_storage);
		Self::deposit_event(Event::<T>::NameSet { name_hash });
		Ok(())
	}
}
