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

use crate::*;
use frame_support::pallet_prelude::*;

impl<T: Config<I>, I: 'static> Pallet<T, I> {
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

		let next_id = collection.increment();

		CollectionConfigOf::<T, I>::insert(&collection, config);
		CollectionAccount::<T, I>::insert(&owner, &collection, ());
		NextCollectionId::<T, I>::set(Some(next_id));

		Self::deposit_event(Event::NextCollectionIdIncremented { next_id });
		Self::deposit_event(event);
		Ok(())
	}

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
			ensure!(collection_details.items == witness.items, Error::<T, I>::BadWitness);
			ensure!(
				collection_details.item_metadatas == witness.item_metadatas,
				Error::<T, I>::BadWitness
			);
			ensure!(collection_details.attributes == witness.attributes, Error::<T, I>::BadWitness);

			for (item, details) in Item::<T, I>::drain_prefix(&collection) {
				Account::<T, I>::remove((&details.owner, &collection, &item));
				T::Currency::unreserve(&details.deposit.account, details.deposit.amount);
			}
			#[allow(deprecated)]
			ItemMetadataOf::<T, I>::remove_prefix(&collection, None);
			#[allow(deprecated)]
			ItemPriceOf::<T, I>::remove_prefix(&collection, None);
			#[allow(deprecated)]
			PendingSwapOf::<T, I>::remove_prefix(&collection, None);
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
			let _ = ItemConfigOf::<T, I>::clear_prefix(&collection, witness.items, None);
			let _ =
				ItemAttributesApprovalsOf::<T, I>::clear_prefix(&collection, witness.items, None);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				items: collection_details.items,
				item_metadatas: collection_details.item_metadatas,
				attributes: collection_details.attributes,
			})
		})
	}
}
