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

//! Handles all logic related to registering and deregistering subnodes.

use crate::{types::*, *};
use codec::Encode;
use sp_runtime::traits::Zero;

impl<T: Config> Pallet<T> {
	/// Calculates a subnode hash given the parent hash and label hash.
	pub fn subnode_hash(parent_hash: NameHash, label_hash: NameHash) -> NameHash {
		return sp_io::hashing::blake2_256(&(parent_hash, label_hash).encode())
	}

	/// Creates a new subname given a raw label.
	///
	/// Can only be called by the owner of a parent name.
	pub fn do_set_subnode_record(
		sender: T::AccountId,
		parent_hash: NameHash,
		label: &[u8],
	) -> DispatchResult {
		ensure!(!label.len().is_zero(), Error::<T>::NameTooShort);

		let maybe_deposit = SubNodeDeposit::<T>::get();
		ensure!(maybe_deposit.is_some(), Error::<T>::SubNodesDisabled);

		let deposit =
			maybe_deposit.expect("subnode deposit has already been verified to exist, qed.");

		let parent_registration = Self::get_registration(parent_hash)?;
		ensure!(Self::is_owner(&parent_registration, &sender), Error::<T>::NotOwner);

		let label_hash = sp_io::hashing::blake2_256(&label);
		let name_hash = Self::subnode_hash(parent_hash, label_hash);

		ensure!(!Registrations::<T>::contains_key(name_hash), Error::<T>::RegistrationExists);
		let expiration = None;
		Self::reserve_deposit(Some(deposit), &sender)?;
		Self::do_register(name_hash, sender, expiration, Some(deposit))?;
		Ok(())
	}

	/// Allow the owner of a parent name to set a new owner for a subname.
	///
	/// This will transfer the deposit of this subname from the old owner to the new one.
	pub fn do_set_subnode_owner(
		sender: T::AccountId,
		parent_hash: NameHash,
		label_hash: NameHash,
		new_owner: T::AccountId,
	) -> DispatchResult {
		let parent_registration = Self::get_registration(parent_hash)?;
		ensure!(Self::is_owner(&parent_registration, &sender), Error::<T>::NotOwner);
		let subnode_hash = Self::subnode_hash(parent_hash, label_hash);
		Self::do_transfer_ownership(subnode_hash, new_owner)
	}
}
