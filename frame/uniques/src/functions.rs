// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Various pieces of common functionality.

use super::*;
use frame_support::{ensure, traits::Get};
use sp_runtime::{DispatchError, DispatchResult};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_transfer(
		collection: T::CollectionId,
		instance: T::InstanceId,
		dest: T::AccountId,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&mut InstanceDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!collection_details.is_frozen, Error::<T, I>::Frozen);
		ensure!(!T::Locker::is_locked(collection, instance), Error::<T, I>::Locked);

		let mut details =
			Asset::<T, I>::get(&collection, &instance).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &instance));
		Account::<T, I>::insert((&dest, &collection, &instance), ());
		let origin = details.owner;
		details.owner = dest;
		Asset::<T, I>::insert(&collection, &instance, &details);

		Self::deposit_event(Event::Transferred {
			collection,
			instance,
			from: origin,
			to: details.owner,
		});
		Ok(())
	}

	pub fn do_create_collection(
		collection: T::CollectionId,
		owner: T::AccountId,
		admin: T::AccountId,
		deposit: DepositBalanceOf<T, I>,
		free_holding: bool,
		event: Event<T, I>,
	) -> DispatchResult {
		ensure!(!Collection::<T, I>::contains_key(collection), Error::<T, I>::InUse);

		T::Currency::reserve(&owner, deposit)?;

		Collection::<T, I>::insert(
			collection,
			CollectionDetails {
				owner: owner.clone(),
				issuer: admin.clone(),
				admin: admin.clone(),
				freezer: admin,
				total_deposit: deposit,
				free_holding,
				instances: 0,
				instance_metadatas: 0,
				attributes: 0,
				is_frozen: false,
			},
		);

		CollectionAccount::<T, I>::insert(&owner, &collection, ());
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
			ensure!(collection_details.instances == witness.instances, Error::<T, I>::BadWitness);
			ensure!(
				collection_details.instance_metadatas == witness.instance_metadatas,
				Error::<T, I>::BadWitness
			);
			ensure!(collection_details.attributes == witness.attributes, Error::<T, I>::BadWitness);

			for (instance, details) in Asset::<T, I>::drain_prefix(&collection) {
				Account::<T, I>::remove((&details.owner, &collection, &instance));
			}
			InstanceMetadataOf::<T, I>::remove_prefix(&collection, None);
			CollectionMetadataOf::<T, I>::remove(&collection);
			Attribute::<T, I>::remove_prefix((&collection,), None);
			CollectionAccount::<T, I>::remove(&collection_details.owner, &collection);
			T::Currency::unreserve(&collection_details.owner, collection_details.total_deposit);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				instances: collection_details.instances,
				instance_metadatas: collection_details.instance_metadatas,
				attributes: collection_details.attributes,
			})
		})
	}

	pub fn do_mint(
		collection: T::CollectionId,
		instance: T::InstanceId,
		owner: T::AccountId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!Asset::<T, I>::contains_key(collection, instance), Error::<T, I>::AlreadyExists);

		Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> DispatchResult {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;

				with_details(collection_details)?;

				let instances =
					collection_details.instances.checked_add(1).ok_or(ArithmeticError::Overflow)?;
				collection_details.instances = instances;

				let deposit = match collection_details.free_holding {
					true => Zero::zero(),
					false => T::InstanceDeposit::get(),
				};
				T::Currency::reserve(&collection_details.owner, deposit)?;
				collection_details.total_deposit += deposit;

				let owner = owner.clone();
				Account::<T, I>::insert((&owner, &collection, &instance), ());
				let details = InstanceDetails { owner, approved: None, is_frozen: false, deposit };
				Asset::<T, I>::insert(&collection, &instance, details);
				Ok(())
			},
		)?;

		Self::deposit_event(Event::Issued { collection, instance, owner });
		Ok(())
	}

	pub fn do_burn(
		collection: T::CollectionId,
		instance: T::InstanceId,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&InstanceDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let owner = Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> Result<T::AccountId, DispatchError> {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				let details = Asset::<T, I>::get(&collection, &instance)
					.ok_or(Error::<T, I>::UnknownCollection)?;
				with_details(collection_details, &details)?;

				// Return the deposit.
				T::Currency::unreserve(&collection_details.owner, details.deposit);
				collection_details.total_deposit.saturating_reduce(details.deposit);
				collection_details.instances.saturating_dec();
				Ok(details.owner)
			},
		)?;

		Asset::<T, I>::remove(&collection, &instance);
		Account::<T, I>::remove((&owner, &collection, &instance));

		Self::deposit_event(Event::Burned { collection, instance, owner });
		Ok(())
	}
}
