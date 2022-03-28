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

//! Handles all logic related to registering and deregistering subnodes.

use crate::{types::*, *};
use codec::Encode;

impl<T: Config> Pallet<T> {
	pub fn subnode_hash(parent_hash: NameHash, label_hash: NameHash) -> NameHash {
		return sp_io::hashing::blake2_256(&(parent_hash, label_hash).encode())
	}

	// pub fn get_subnode_registration(parent_hash: NameHash, label_hash: NameHash) ->
	// Result<RegistrationOf<T>, DispatchError> { 	let subnode_hash = Self::subnode_hash(parent_hash,
	// label_hash); 	Registrations::<T>::get(subnode_hash).ok_or(Error::<T>::
	// ParentRegistrationNotFound.into()) }

	// pub fn do_deregister(
	// 	maybe_label_hash: Option<NameHash>,
	// 	name_hash: NameHash,
	// 	maybe_sender: Option<T::AccountId>,
	// ) -> DispatchResult {
	// 	// if label hash has been provided, we are trying to deregister a subnode.
	// 	let name_hash = if let Some(label_hash) = maybe_label_hash {
	// 		let parent_hash = name_hash;

	// 		// generate the subnode we wish to deregister.
	// 		let subnode_hash = Self::subnode_hash(parent_hash, label_hash);

	// 		// ensure this subnode exists
	// 		let registration = Registrations::<T>::get(subnode_hash)
	// 			.ok_or(Error::<T>::RegistrationNotFound)?;

	// 		// not owner - check parent node has been deregistered.
	// 		if let Some(sender) = maybe_sender {
	// 			if registration.owner != sender {
	// 				ensure!(
	// 					!Registrations::<T>::contains_key(parent_hash),
	// 					Error::<T>::RegistrationNotExpired
	// 				);
	// 			}
	// 		}

	// 		// defensive handling subnode unreserve - should always exist.
	// 		if let Some(deposit) = registration.deposit {
	// 			let res = T::Currency::unreserve(&registration.owner, deposit);
	// 			debug_assert!(res.is_zero());
	// 		}

	// 		subnode_hash

	// 	// no label hash provided; we are trying to deregister a top level node.
	// 	} else {
	// 		let registration =
	// 			Registrations::<T>::get(name_hash).ok_or(Error::<T>::RegistrationNotFound)?;

	// 		// if not root origin nor owner, check node has expired.
	// 		if let Some(sender) = maybe_sender {
	// 			if registration.owner != sender {
	// 				let expiry =
	// 					registration.expiry.ok_or(Error::<T>::RegistrationHasNoExpiry)?;
	// 				ensure!(
	// 					expiry < frame_system::Pallet::<T>::block_number(),
	// 					Error::<T>::RegistrationNotExpired
	// 				);
	// 			}
	// 		}
	// 		name_hash
	// 	};

	// 	Resolvers::<T>::remove(name_hash);
	// 	Registrations::<T>::remove(name_hash);
	// 	Self::deposit_event(Event::<T>::AddressDeregistered { name_hash });
	// 	return Ok(())
	// }
}
