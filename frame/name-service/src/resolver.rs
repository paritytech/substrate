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
use frame_support::pallet_prelude::*;

pub trait NameServiceResolver<T: Config> {
	/// Get the native address associated with this name hash.
	fn get_address(name_hash: NameHash) -> Option<T::AccountId>;
	/// Set the native address associated with this name hash.
	fn set_address(name_hash: NameHash, address: T::AccountId) -> DispatchResult;

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: NameHash) -> Option<BoundedNameOf<T>>;
	/// Set the unhashed name associated with this name hash.
	fn set_name(name_hash: NameHash, name: BoundedNameOf<T>) -> DispatchResult;

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: NameHash) -> Option<BoundedTextOf<T>>;
	/// Set the arbitrary text associated with this name hash.
	fn set_text(name_hash: NameHash, bytes: BoundedTextOf<T>) -> DispatchResult;
}

impl<T: Config> NameServiceResolver<T> for Pallet<T> {
	/// Get the native address associated with this name hash.
	fn get_address(name_hash: NameHash) -> Option<T::AccountId> {
		AddressResolver::<T>::get(name_hash)
	}
	/// Set the native address associated with this name hash.
	fn set_address(name_hash: NameHash, address: T::AccountId) -> DispatchResult {
		AddressResolver::<T>::insert(name_hash, address.clone());
		Self::deposit_event(Event::<T>::AddressSet { name_hash, address });
		Ok(())
	}

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: NameHash) -> Option<BoundedNameOf<T>> {
		None
	}
	/// Set the unhashed name associated with this name hash.
	fn set_name(name_hash: NameHash, name: BoundedNameOf<T>) -> DispatchResult {
		Err("not supported".into())
	}

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: NameHash) -> Option<BoundedTextOf<T>> {
		None
	}
	/// Set the arbitrary text associated with this name hash.
	fn set_text(name_hash: NameHash, bytes: BoundedTextOf<T>) -> DispatchResult {
		Err("not supported".into())
	}
}
