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

//! This module contains helper methods to perform functionality associated with creating and
//! destroying collections for the NFTs pallet.

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Create a new collection with the given `collection`, `owner`, `admin`, `config`, `deposit`,
	/// and `event`.
	///
	/// This function creates a new collection with the provided parameters. It reserves the
	/// required deposit from the owner's account, sets the collection details, assigns admin roles,
	/// and inserts the provided configuration. Finally, it emits the specified event upon success.
	///
	/// # Errors
	///
	/// This function returns a [`CollectionIdInUse`](crate::Error::CollectionIdInUse) error if the
	/// collection ID is already in use.
	pub fn do_create_collection(
		collection: T::CollectionId,
		owner: T::AccountId,
		admin: T::AccountId,
		config: CollectionConfigFor<T, I>,
		deposit: DepositBalanceOf<T, I>,
		event: Event<T, I>,
	) -> DispatchResult {
		ensure!(!Collection::<T, I>::contains_key(collection), Error::<T, I>::CollectionIdInUse);

		T::Currency::reserve(&owner, deposit)?;

		Collection::<T, I>::insert(
			collection,
			CollectionDetails {
				owner: owner.clone(),
				owner_deposit: deposit,
				items: 0,
				item_metadatas: 0,
				item_configs: 0,
				attributes: 0,
			},
		);
		CollectionRoleOf::<T, I>::insert(
			collection,
			admin,
			CollectionRoles(
				CollectionRole::Admin | CollectionRole::Freezer | CollectionRole::Issuer,
			),
		);

		CollectionConfigOf::<T, I>::insert(&collection, config);
		CollectionAccount::<T, I>::insert(&owner, &collection, ());
		Self::deposit_event(event);
		Ok(())
	}

	/// Destroy the specified collection with the given `collection`, `witness`, and
	/// `maybe_check_owner`.
	///
	/// This function destroys the specified collection if it exists and meets the necessary
	/// conditions. It checks the provided `witness` against the actual collection details and
	/// removes the collection along with its associated metadata, attributes, and configurations.
	/// The necessary deposits are returned to the corresponding accounts, and the roles and
	/// configurations for the collection are cleared. Finally, it emits the `Destroyed` event upon
	/// successful destruction.
	///
	/// # Errors
	///
	/// This function returns a dispatch error in the following cases:
	/// - If the collection ID is not found
	///   ([`UnknownCollection`](crate::Error::UnknownCollection)).
	/// - If the provided `maybe_check_owner` does not match the actual owner
	///   ([`NoPermission`](crate::Error::NoPermission)).
	/// - If the collection is not empty (contains items)
	///   ([`CollectionNotEmpty`](crate::Error::CollectionNotEmpty)).
	/// - If the `witness` does not match the actual collection details
	///   ([`BadWitness`](crate::Error::BadWitness)).
	pub fn do_destroy_collection(
		collection: T::CollectionId,
		witness: DestroyWitness,
		maybe_check_owner: Option<T::AccountId>,
	) -> Result<DestroyWitness, DispatchError> {
		Collection::<T, I>::try_mutate_exists(collection, |maybe_details| {
			let collection_details =
				maybe_details.take().ok_or(Error::<T, I>::UnknownCollection)?;
			if let Some(check_owner) = maybe_check_owner {
				ensure!(collection_details.owner == check_owner, Error::<T, I>::NoPermission);
			}
			ensure!(collection_details.items == 0, Error::<T, I>::CollectionNotEmpty);
			ensure!(collection_details.attributes == witness.attributes, Error::<T, I>::BadWitness);
			ensure!(
				collection_details.item_metadatas == witness.item_metadatas,
				Error::<T, I>::BadWitness
			);
			ensure!(
				collection_details.item_configs == witness.item_configs,
				Error::<T, I>::BadWitness
			);

			for (_, metadata) in ItemMetadataOf::<T, I>::drain_prefix(&collection) {
				if let Some(depositor) = metadata.deposit.account {
					T::Currency::unreserve(&depositor, metadata.deposit.amount);
				}
			}

			CollectionMetadataOf::<T, I>::remove(&collection);
			Self::clear_roles(&collection)?;

			for (_, (_, deposit)) in Attribute::<T, I>::drain_prefix((&collection,)) {
				if !deposit.amount.is_zero() {
					if let Some(account) = deposit.account {
						T::Currency::unreserve(&account, deposit.amount);
					}
				}
			}

			CollectionAccount::<T, I>::remove(&collection_details.owner, &collection);
			T::Currency::unreserve(&collection_details.owner, collection_details.owner_deposit);
			CollectionConfigOf::<T, I>::remove(&collection);
			let _ = ItemConfigOf::<T, I>::clear_prefix(&collection, witness.item_configs, None);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				item_metadatas: collection_details.item_metadatas,
				item_configs: collection_details.item_configs,
				attributes: collection_details.attributes,
			})
		})
	}
}
