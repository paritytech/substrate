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
use frame_support::{ensure, traits::Get, BoundedVec};
use sp_runtime::{DispatchError, DispatchResult};

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	pub fn do_transfer(
		collection: T::CollectionId,
		item: T::ItemId,
		dest: T::AccountId,
		with_details: impl FnOnce(
			&CollectionDetailsFor<T, I>,
			&mut ItemDetailsFor<T, I>,
		) -> DispatchResult,
	) -> DispatchResult {
		let collection_details =
			Collection::<T, I>::get(&collection).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!collection_details.is_frozen, Error::<T, I>::Frozen);
		ensure!(!T::Locker::is_locked(collection, item), Error::<T, I>::Locked);

		let mut details =
			Item::<T, I>::get(&collection, &item).ok_or(Error::<T, I>::UnknownCollection)?;
		ensure!(!details.is_frozen, Error::<T, I>::Frozen);
		with_details(&collection_details, &mut details)?;

		Account::<T, I>::remove((&details.owner, &collection, &item));
		Account::<T, I>::insert((&dest, &collection, &item), ());
		let origin = details.owner;
		details.owner = dest;
		Item::<T, I>::insert(&collection, &item, &details);

		Self::deposit_event(Event::Transferred {
			collection,
			item,
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
				items: 0,
				item_metadatas: 0,
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
			ensure!(collection_details.items == witness.items, Error::<T, I>::BadWitness);
			ensure!(
				collection_details.item_metadatas == witness.item_metadatas,
				Error::<T, I>::BadWitness
			);
			ensure!(collection_details.attributes == witness.attributes, Error::<T, I>::BadWitness);

			for (item, details) in Item::<T, I>::drain_prefix(&collection) {
				Account::<T, I>::remove((&details.owner, &collection, &item));
			}
			#[allow(deprecated)]
			ItemMetadataOf::<T, I>::remove_prefix(&collection, None);
			CollectionMetadataOf::<T, I>::remove(&collection);
			#[allow(deprecated)]
			Attribute::<T, I>::remove_prefix((&collection,), None);
			CollectionAccount::<T, I>::remove(&collection_details.owner, &collection);
			T::Currency::unreserve(&collection_details.owner, collection_details.total_deposit);
			CollectionMaxSupply::<T, I>::remove(&collection);

			Self::deposit_event(Event::Destroyed { collection });

			Ok(DestroyWitness {
				items: collection_details.items,
				item_metadatas: collection_details.item_metadatas,
				attributes: collection_details.attributes,
			})
		})
	}

	pub fn do_mint(
		collection: T::CollectionId,
		item: T::ItemId,
		owner: T::AccountId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		ensure!(!Item::<T, I>::contains_key(collection, item), Error::<T, I>::AlreadyExists);

		Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> DispatchResult {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;

				with_details(collection_details)?;

				if let Ok(max_supply) = CollectionMaxSupply::<T, I>::try_get(&collection) {
					ensure!(collection_details.items < max_supply, Error::<T, I>::MaxSupplyReached);
				}

				let items =
					collection_details.items.checked_add(1).ok_or(ArithmeticError::Overflow)?;
				collection_details.items = items;

				let deposit = match collection_details.free_holding {
					true => Zero::zero(),
					false => T::ItemDeposit::get(),
				};
				T::Currency::reserve(&collection_details.owner, deposit)?;
				collection_details.total_deposit += deposit;

				let owner = owner.clone();
				Account::<T, I>::insert((&owner, &collection, &item), ());
				let details = ItemDetails { owner, approved: None, is_frozen: false, deposit };
				Item::<T, I>::insert(&collection, &item, details);
				Ok(())
			},
		)?;

		Self::deposit_event(Event::Issued { collection, item, owner });
		Ok(())
	}

	pub fn do_burn(
		collection: T::CollectionId,
		item: T::ItemId,
		with_details: impl FnOnce(&CollectionDetailsFor<T, I>, &ItemDetailsFor<T, I>) -> DispatchResult,
	) -> DispatchResult {
		let owner = Collection::<T, I>::try_mutate(
			&collection,
			|maybe_collection_details| -> Result<T::AccountId, DispatchError> {
				let collection_details =
					maybe_collection_details.as_mut().ok_or(Error::<T, I>::UnknownCollection)?;
				let details = Item::<T, I>::get(&collection, &item)
					.ok_or(Error::<T, I>::UnknownCollection)?;
				with_details(collection_details, &details)?;

				// Return the deposit.
				T::Currency::unreserve(&collection_details.owner, details.deposit);
				collection_details.total_deposit.saturating_reduce(details.deposit);
				collection_details.items.saturating_dec();
				Ok(details.owner)
			},
		)?;

		Item::<T, I>::remove(&collection, &item);
		Account::<T, I>::remove((&owner, &collection, &item));

		Self::deposit_event(Event::Burned { collection, item, owner });
		Ok(())
	}

	pub fn do_set_instance_metadata(
		class: T::ClassId,
		instance: T::InstanceId,
		data: BoundedVec<u8, T::StringLimit>,
		is_frozen: bool,
		maybe_check_owner: Option<T::AccountId>,
		with_details: impl FnOnce(
			&ClassDetailsFor<T, I>,
			&Option<InstanceMetadata<DepositBalanceOf<T, I>, T::StringLimit>>,
		) -> DispatchResult,
	) -> DispatchResult {
		InstanceMetadataOf::<T, I>::try_mutate_exists(class, instance, |metadata| {
			let mut class_details =
				Class::<T, I>::get(&class).ok_or(Error::<T, I>::UnknownClass)?;

			with_details(&class_details, metadata)?;

			if metadata.is_none() {
				class_details.instance_metadatas.saturating_inc();
			}

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			class_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if !class_details.free_holding && maybe_check_owner.is_some() {
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}
			if deposit > old_deposit {
				T::Currency::reserve(&class_details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&class_details.owner, old_deposit - deposit);
			}
			class_details.total_deposit.saturating_accrue(deposit);

			*metadata = Some(InstanceMetadata { deposit, data: data.clone(), is_frozen });

			Class::<T, I>::insert(&class, &class_details);
			Self::deposit_event(Event::MetadataSet { class, instance, data, is_frozen });
			Ok(())
		})
	}

	pub fn do_set_class_metadata(
		class: T::ClassId,
		data: BoundedVec<u8, T::StringLimit>,
		is_frozen: bool,
		maybe_check_owner: Option<T::AccountId>,
		with_details: impl FnOnce(
			&ClassDetailsFor<T, I>,
			&Option<ClassMetadata<DepositBalanceOf<T, I>, T::StringLimit>>,
		) -> DispatchResult,
	) -> DispatchResult {
		ClassMetadataOf::<T, I>::try_mutate_exists(class, |metadata| {
			let mut class_details =
				Class::<T, I>::get(&class).ok_or(Error::<T, I>::UnknownClass)?;

			with_details(&class_details, &metadata)?;

			let old_deposit = metadata.take().map_or(Zero::zero(), |m| m.deposit);
			class_details.total_deposit.saturating_reduce(old_deposit);
			let mut deposit = Zero::zero();
			if maybe_check_owner.is_some() && !class_details.free_holding {
				deposit = T::DepositPerByte::get()
					.saturating_mul(((data.len()) as u32).into())
					.saturating_add(T::MetadataDepositBase::get());
			}
			if deposit > old_deposit {
				T::Currency::reserve(&class_details.owner, deposit - old_deposit)?;
			} else if deposit < old_deposit {
				T::Currency::unreserve(&class_details.owner, old_deposit - deposit);
			}
			class_details.total_deposit.saturating_accrue(deposit);

			*metadata = Some(ClassMetadata { deposit, data: data.clone(), is_frozen });

			Class::<T, I>::insert(&class, class_details);
			Self::deposit_event(Event::ClassMetadataSet { class, data, is_frozen });
			Ok(())
		})
	}

	pub fn do_set_attribute(
		class: &T::ClassId,
		maybe_instance: &Option<T::InstanceId>,
		key: &BoundedVec<u8, T::KeyLimit>,
		value: &BoundedVec<u8, T::ValueLimit>,
	) -> DispatchResult {
		// If class exists, update class metadata and set/update attribute
		Class::<T, I>::mutate_exists(class, |opt_class_details| {
			match opt_class_details {
				Some(class_details) => {
					let attribute = Attribute::<T, I>::get((class, maybe_instance, &key));
					// If the class does not have an attribute for the given key, increase the
					// counter of the number of attributes
					if attribute.is_none() {
						class_details.attributes.saturating_inc();
					}

					let mut deposit = Attribute::<T, I>::get((class, maybe_instance, &key))
						.map_or(Zero::zero(), |m| m.1);
					//Set attribute value
					Attribute::<T, I>::insert((&class, maybe_instance, &key), (&value, deposit));
					Ok(())
				},
				None => Err(Error::<T, I>::UnknownClass),
			}
		})?;
		Ok(())
	}
}
