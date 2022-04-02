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

pub trait NameServiceResolver {
	type AccountId;
	type NameHash;
	type NameBound: Get<u32>;
	type TextBound: Get<u32>;

	/// Get the native address associated with this name hash.
	fn get_address(name_hash: Self::NameHash) -> Option<Self::AccountId>;
	/// Set the native address associated with this name hash.
	fn set_address(name_hash: Self::NameHash, address: Self::AccountId) -> DispatchResult;

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: Self::NameHash) -> Option<BoundedVec<u8, Self::NameBound>>;
	/// Set the unhashed name associated with this name hash.
	fn set_name(name_hash: Self::NameHash, name: BoundedVec<u8, Self::NameBound>)
		-> DispatchResult;

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: Self::NameHash) -> Option<BoundedVec<u8, Self::TextBound>>;
	/// Set the arbitrary text associated with this name hash.
	fn set_text(
		name_hash: Self::NameHash,
		bytes: BoundedVec<u8, Self::TextBound>,
	) -> DispatchResult;
}

impl<T: Config> NameServiceResolver for Pallet<T> {
	type AccountId = T::AccountId;
	type NameHash = NameHash;
	type NameBound = T::MaxNameLength;
	type TextBound = T::MaxTextLength;

	/// Get the native address associated with this name hash.
	fn get_address(name_hash: Self::NameHash) -> Option<Self::AccountId> {
		AddressResolver::<T>::get(name_hash)
	}
	/// Set the native address associated with this name hash.
	fn set_address(name_hash: Self::NameHash, address: Self::AccountId) -> DispatchResult {
		AddressResolver::<T>::insert(name_hash, address.clone());
		Self::deposit_event(Event::<T>::AddressSet { name_hash, address });
		Ok(())
	}

	/// Get the unhashed name associated with this name hash.
	fn get_name(name_hash: Self::NameHash) -> Option<BoundedVec<u8, Self::NameBound>> {
		None
	}
	/// Set the unhashed name associated with this name hash.
	fn set_name(
		name_hash: Self::NameHash,
		name: BoundedVec<u8, Self::NameBound>,
	) -> DispatchResult {
		Err("not supported".into())
	}

	/// Get the arbitrary text associated with this name hash.
	fn get_text(name_hash: Self::NameHash) -> Option<BoundedVec<u8, Self::TextBound>> {
		None
	}
	/// Set the arbitrary text associated with this name hash.
	fn set_text(
		name_hash: Self::NameHash,
		bytes: BoundedVec<u8, Self::TextBound>,
	) -> DispatchResult {
		Err("not supported".into())
	}
}
